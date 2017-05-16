;   Scunak: A Mathematical Assistant System
;   Copyright (C) 2006 Chad E Brown (cebrown2323@yahoo.com)
;
;   This program is free software; you can redistribute it and/or modify
;   it under the terms of the GNU General Public License as published by
;   the Free Software Foundation; either version 2 of the License, or
;   (at your option) any later version.
;
;   This program is distributed in the hope that it will be useful,
;   but WITHOUT ANY WARRANTY; without even the implied warranty of
;   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;   GNU General Public License for more details.
;
;   You should have received a copy of the GNU General Public License along
;   with this program; if not, write to the Free Software Foundation, Inc.,
;   51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

; Chad E Brown
; February 2006
(defvar *sos-fohorn* nil)
(defvar *usable-fohorn* nil)

(defvar *max-ctx-len* 3)

(defvar *fohorn-cycles* 0)
(defvar *max-cycles* 20)
(defvar *enumerate-throw-on-success* nil)
(defvar *fohorn-allow-propvars* nil)

(defvar *fohorn-binary-res* t)
(defvar *fohorn-factor* t)
(defvar *fohorn-unit-res* nil)

(defvar *fohorn-goal-clause* nil)

(defun initialize-fohorn (sos &optional (usable *global-sigma*))
  (initialize-fohorn-0)
  (initialize-fohorn-1 sos usable))

(defun initialize-fohorn-0 ()
  (setq *fohorn-cycles* 0)
  (setq *usable-fohorn* nil)
  (setq *sos-fohorn* nil))

(defun initialize-fohorn-1 (sos usable)
  (dolist (c sos)
    (when (dtype-for-fohorn-clause (get c 'dbtype))
      (push (sigelt-to-fohorn-clause c) *sos-fohorn*)))
  (dolist (c (set-difference usable sos))
    (when (dtype-for-fohorn-clause (get c 'dbtype))
      (push (sigelt-to-fohorn-clause c) *usable-fohorn*))))

(defun dtype-for-fohorn-clause (dtp &optional (allow-propvars *fohorn-allow-propvars*))
  (if (dpi-p dtp)
      (if (or (dpi-p (dpi-dom dtp))
	      (and (not allow-propvars) (prop-p (dpi-dom dtp))))
	  nil
	(dtype-for-fohorn-clause (dpi-cod dtp)))
    (or (pf-p dtp) (dclass-p dtp))))

(defun sigelt-to-fohorn-clause (c)
  (multiple-value-bind
   (trm tp evars)
   (imitation-term c *emptyctx*)
   (let ((pfevars nil)
	 (objevars nil))
     (dolist (e evars)
       (if (pf-p (cdr e))
	   (push e pfevars)
	 (if (dclass-p (cdr e))
	     (multiple-value-bind
	      (trm2 newevars)
	      (split-evar-to-pair (cdr e) (car e))
	      (setq trm (normalize (subst-1 (car e) trm2 trm)))
	      (setq tp (normalize-type (subst-type-1 (car e) trm2 tp)))
	      (push (car newevars) objevars)
	      (setq pfevars
		    (cons (cadr newevars)
			  (mapcar #'(lambda (x) (cons (car x)
						      (normalize-type (subst-type-1 (car e) trm2 (cdr x)))))
				  pfevars)))
	      )
	   (push e objevars))))
     (if (pf-p tp)
	 (list (pf-prop tp) pfevars objevars trm)
       (if (dclass-p tp)
	   (list (pair-prop tp (fst trm)) pfevars objevars (snd trm))
	 (fail "sigelt-to-fohorn-clause called with a sigelt with bad type for fohorn clause" c))))))

(defun print-fohorn-clause (c)
  (if (cadr c)
      (progn
	(format t "~d :- ~d"
		(output1-extraction-string (car c) nil nil)
		(output1-extraction-string (pf-prop (cdar (cadr c))) nil nil))
	(dolist (z (cdr (cadr c)))
	  (format t ", ~d" (output1-extraction-string (pf-prop (cdr z)) nil nil)))
	(format t ".~%"))
    (format t "~d.~%"
	    (output1-extraction-string (car c) nil nil))))

(defun fresh-evar ()
  (let ((e (intern-gensym)))
    (setf (get e 'evar) t)
    e))

(defun fohorn-clause-freshen-vars (c)
  (let* ((head (car c))
	 (pfevars (cadr c))
	 (objevars (caddr c))
	 (pfterm (cadddr c))
	 (theta1 (mapcar #'(lambda (x)
			     (cons (car x)
				   (fresh-evar)))
			 pfevars))
	 (theta2 (mapcar #'(lambda (x)
			     (cons (car x)
				   (fresh-evar)))
			 objevars))
	 (theta (append theta1 theta2))
	 (pfevars2 (mapcar #'(lambda (x y)
			       (cons (cdr y) 
				     (simul-subst-type theta
						       (cdr x)
						       )))
			   pfevars theta1))
	 (objevars2 (mapcar #'(lambda (x y)
				(cons (cdr y)
				     (simul-subst-type theta
						       (cdr x)
						       )))
			    objevars theta2)))
    (list (simul-subst theta head) pfevars2 objevars2 (simul-subst theta pfterm))))

(defun subst-fohorn-clause (theta cl)
  (let ((pfevars2 nil)
	(objevars2 nil))
    (dolist (v (cadr cl))
      (let ((a (assoc (car v) theta)))
	(unless a
	  (push (cons (car v) (simul-subst-type theta (cdr v))) pfevars2))))
    (dolist (v (caddr cl))
      (let ((a (assoc (car v) theta)))
	(unless a
	  (push (cons (car v) (simul-subst-type theta (cdr v))) objevars2))))
    (list (simul-subst theta (car cl))
	  pfevars2
	  objevars2
	  (simul-subst theta (cadddr cl)))))

; no need to keep up with types or contexts here
; returns values (<succ> <theta>)
(defun fo-unify (dpairs &optional theta)
  (if dpairs
      (let ((x (caar dpairs))
	    (y (cadar dpairs)))
	(if (or (lam-p x) (lam-p y))
	    (fo-unify (cons (list (gen-lam-body x) (gen-lam-body y)) (cdr dpairs))
		      theta)
	  (if (or (pair-p x) (pair-p y))
	      (fo-unify (cons (list (gen-pair-fst x) (gen-pair-fst y))
			      (cons (list (gen-pair-snd x) (gen-pair-snd y))
				    (cdr dpairs)))
			theta)
	    (if (and (symbolp x) (get x 'evar))
		(if (equal x y)
		    (fo-unify (cdr dpairs) theta)
		  (let ((r (assoc x theta)))
		    (if r
			(fo-unify (cons (list (cdr r) y) (cdr dpairs)) theta)
		      (if (member x (free-evars y))
			  nil
			(let ((s (simul-subst theta y)))
			  (fo-unify (cdr dpairs)
				    (acons x s
					   (mapcar #'(lambda (z)
						       (cons (car z)
							   (subst-1 x s (cdr z))))
						   theta))))))))
	      (if (and (symbolp y) (get y 'evar))
		  (let ((r (assoc y theta)))
		    (if r
			(fo-unify (cons (list x (cdr r)) (cdr dpairs)) theta)
		      (if (member y (free-evars x))
			  nil
			(let ((s (simul-subst theta x)))
			  (fo-unify (cdr dpairs)
				    (acons y s
					   (mapcar #'(lambda (z)
						       (cons (car z)
							     (subst-1 y s (cdr z))))
						   theta)))))))
		(if (equal (term-extr-head x) (term-extr-head y))
		    (fo-unify (append (mapcar #'(lambda (arg1 arg2)
						  (list arg1 arg2))
					      (term-extr-args x)
					      (term-extr-args y))
				      (cdr dpairs))
			      theta)
		  nil))))))
    (values t theta)))

; no need to keep up with types or contexts here
; returns values (<succ> <theta>)
(defun fo-match (dpairs &optional theta)
  (if dpairs
      (let ((x (caar dpairs))
	    (y (cadar dpairs)))
	(if (or (lam-p x) (lam-p y))
	    (fo-match (cons (list (gen-lam-body x) (gen-lam-body y)) (cdr dpairs))
		      theta)
	  (if (or (pair-p x) (pair-p y))
	      (fo-match (cons (list (gen-pair-fst x) (gen-pair-fst y))
			      (cons (list (gen-pair-snd x) (gen-pair-snd y))
				    (cdr dpairs)))
			theta)
	    (if (and (symbolp x) (get x 'evar))
		(if (equal x y)
		    (fo-match (cdr dpairs) theta)
		  (let ((r (assoc x theta)))
		    (if r
			(if (heq (cdr r) y)
			    (fo-match (cdr dpairs) theta)
			  nil)
		      (if (member x (free-evars y))
			  nil
			(let ((s (simul-subst theta y)))
			  (fo-match (cdr dpairs)
				    (acons x s
					   (mapcar #'(lambda (z)
						       (cons (car z)
							   (subst-1 x s (cdr z))))
						   theta))))))))
	      (if (and (symbolp y) (get y 'evar))
		  nil
		(if (equal (term-extr-head x) (term-extr-head y))
		    (fo-match (append (mapcar #'(lambda (arg1 arg2)
						  (list arg1 arg2))
					      (term-extr-args x)
					      (term-extr-args y))
				      (cdr dpairs))
			      theta)
		  nil))))))
    (values t theta)))

(defun fohorn-enum (sos &optional (usable *global-sigma*))
  (initialize-fohorn sos usable)
  (fohorn-enum-2))

(defun fohorn-enum-2 ()
  (loop while (and *sos-fohorn*
		   (or (not *max-cycles*) (< *fohorn-cycles* *max-cycles*))) do
	(incf *fohorn-cycles*)
	(when (> *verbose* 60)
	  (format t "Fohorn Cycle ~d~%" *fohorn-cycles*))
	(let ((c (pop *sos-fohorn*)))
	  (when *fohorn-factor*
	    (factor-fohorn c))
	  (when *fohorn-binary-res*
	    (resolve-fohorns c (fohorn-clause-freshen-vars c)))
	  (dolist (d *usable-fohorn*)
	    (cond (*fohorn-binary-res*
		   (resolve-fohorns c d)
		   (resolve-fohorns d c))
		  (*fohorn-unit-res*
		   (unless (cadr c)
		     (resolve-fohorns c d))
		   (unless (cadr d)
		     (resolve-fohorns d c)))
		  (t nil)))
	  (push c *usable-fohorn*)
	  )))

; clause with head: c
; clause with body: d
; try each lit in body of d
(defun resolve-fohorns (c d)
  (when (car c) ; c must have a head
    (dotimes (i (length (cadr d)))
      (resolve-fohorns-lit c d i))))

(defun resolve-fohorns-lit (c d i)
  (let ((lit (nth i (cadr d))))
    (when (> *verbose* 80)
      (format t "Trying to Resolve Clauses with Lit ~d~%" i)
      (print-fohorn-clause c)
      (print-fohorn-clause d)
      )
    (multiple-value-bind
     (succ theta)
     (fo-unify (list (list (car c) (pf-prop (cdr lit))))
	       (acons (car lit) (cadddr c) nil)) ; interesting, we build proof term along with unification...
     (when succ
       (add-new-fohorn-clause
	(fohorn-clause-freshen-vars
	 (subst-fohorn-clause
	  theta
	  (list (car d)
		(append (cadr c) (cadr d))
		(append (caddr c) (caddr d))
		(cadddr d)))))))))

(defun factor-fohorn (c)
  (dotimes (j (length (cadr c)))
    (dotimes (i j)
      (factor-fohorn-lits c i j))))

(defun factor-fohorn-lits (c i j)
  (let ((lit1 (nth i (cadr c)))
	(lit2 (nth j (cadr c))))
    (when (> *verbose* 80)
      (format t "Trying to Factor Clause with Lits ~d and ~d~%" i j)
      (print-fohorn-clause c))
    (multiple-value-bind
     (succ theta)
     (fo-unify (list (list (pf-prop (cdr lit1)) (pf-prop (cdr lit2))))
	       (acons (car lit1) (car lit2) nil)) ; put the evars together
     (when succ
       (add-new-fohorn-clause
	(fohorn-clause-freshen-vars
	 (subst-fohorn-clause
	  theta c)))))))

; add subsumption checking
(defun add-new-fohorn-clause (cl)
  (if (or (clause-subsumed-by-some cl *usable-fohorn*)
	  (clause-subsumed-by-some cl *sos-fohorn*))
      (when (> *verbose* 50)
	(format t "Subsumed generated clause:~%")
	(print-fohorn-clause cl))
    (if (and *fohorn-goal-clause* (clause-subsumes cl *fohorn-goal-clause*))
	(throw 'fohorn-success (list 'success cl))
      (if (filter-fohorn-clause cl)
	  (when (> *verbose* 50)
	    (format t "Filtered new clause:~%")
	    (print-fohorn-clause cl))
	(progn
	  (when (> *verbose* 50)
	    (format t "Adding new clause:~%")
	    (print-fohorn-clause cl))
	  (if *sos-fohorn*
	      (nconc *sos-fohorn* (list cl))
	    (setq *sos-fohorn* (list cl))
	    ))))))

(defun filter-fohorn-clause (cl)
;  (cdadr cl)
  nil)

; does not try to reorder lits
; c = h :- a1, ..., an
; d = theta(h) :- theta(a1),...,theta(an), b1,...bm
; returns (<succ> <theta[matcher]>)
(defun clause-subsumes (c d)
  (let ((pfevars1 (cadr c))
	(pfevars2 (cadr d)))
    (if (< (length pfevars2) (length pfevars1))
	nil
      (multiple-value-bind
       (succ theta)
       (fo-match (list (list (car c) (car d))) nil)
       (if succ
	   (progn
	     (loop while (and pfevars1 succ) do
		   (multiple-value-setq
		    (succ theta)
		    (fo-match (list (pf-prop (cdar pfevars1))
				    (pf-prop (cdar pfevars2)))
			      theta)))
	     (values succ theta))
	 nil)))))

(defun clause-subsumed-by-some (c cl)
  (let ((done nil)
	(c2 nil))
    (loop while (and (not done) cl) do
	  (setq c2 (pop cl))
	  (multiple-value-bind
	   (succ theta)
	   (clause-subsumes c2 c)
	   (when succ
	     (when (> *verbose* 70)
	       (format t "Clause subsumes other by ~d~%" theta)
	       (print-fohorn-clause c2)
	       (print-fohorn-clause c))
	     (setq done t))))
    done))

(defun fohorn-res-fill-1 (namedbdvars prop usable)
  (setq *fohorn-goal-clause* (list prop nil nil nil))
  (let ((s (catch 'fohorn-success
	     (fohorn-enum namedbdvars usable))))
    (if (and s (eq (car s) 'success))
	(let* ((scl (cadr s))
	       (pfterm (cadddr scl)))
	  (multiple-value-bind
	   (succ theta)
	   (clause-subsumes scl *fohorn-goal-clause*)
	   (if succ
	       (simul-subst theta pfterm)
	     nil)))
      nil)))

(defun fohorn-res-fill (namedbdvars tp &optional (usable *scip-usable*))
  (if (pf-p tp)
      (let ((res (fohorn-res-fill-1 namedbdvars (pf-prop tp) usable)))
	(if res
	    (lam-ctx namedbdvars (named-term-to-db-1 namedbdvars res))
	  nil))
    nil))

