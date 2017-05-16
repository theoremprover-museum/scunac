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
; December 2005

(defvar *preunify-msv-goal* 2)
(defvar *preunify-msv-hence* 2)
(defvar *preunify-msv-supp* 1)
(defvar *unif-debug* nil)
(defvar *quick-fill-gap-only-external* nil)
(defvar *quick-fill-gap-simplify* nil)
(defvar *quick-fill-gap-special-cases* t)
(defvar *quick-fill-gap-external-agents* nil) ; list of funcs taking ctx, type (should be pf type) and usable, then fills special cases, return NIL|closed term
(defvar *ctx-for-premiss-bd* 10)
(defvar *filter-usable-for-gap* nil)

(defvar *quick-fill-gap-method* 'A) ; B is probably better and the code is cleaner, *but* it's slower at the moment...

; return bool[fail] current-evars theta dpairs fill-constraints
(defun simplify-constraints (original-evars current-evars theta
					    dpairs
					    fill-constraints)
  (let ((fail nil)
	(change t)
	(dpair nil)
	(fc nil))
    (loop while (and change (not fail)) do
	  (when (> *verbose* 88)
	    (format t "Current Constraints~%current-evars ~d~%" current-evars)
	    (dolist (dpair dpairs)
	      (format t "dpair~%~d~%~d~%~d~%"
		      (output-term-string (cadr dpair))
		      (output-term-string (caddr dpair))
		      (output-type-string (cadddr dpair))
		      )
	      (sanity-check (cadr dpair) (cadddr dpair) (car dpair) current-evars)
	      (sanity-check (caddr dpair) (cadddr dpair) (car dpair) current-evars)
	      )
	    (dolist (fc fill-constraints)
	      (format t "fill-constraint~%~d~%~d~%"
		      (output-term-string (cadr fc))
		      (output-type-string (caddr fc)))
	      (sanity-check (cadr fc) (caddr fc) (car fc) current-evars)
	      ))
	  (setq change nil)
	  (setq dpair (find-simplify-dpair current-evars dpairs))
	  (if dpair
	      (progn
		(setq change t)
		(multiple-value-setq
		 (fail current-evars theta dpairs fill-constraints)
		 (simplify-dpair
		  dpair
		  original-evars current-evars theta
		  (remove dpair dpairs)
		  fill-constraints)))
	    (progn ; only do this if no other kind of simplification on dpairs can be done
	      (setq dpair (find-simplify-dpair-2 current-evars dpairs))
	      (when dpair
		(setq change t)
		(multiple-value-setq
		 (fail current-evars theta dpairs fill-constraints)
		 (simplify-dpair-2
		  dpair
		  original-evars current-evars theta
		  (remove dpair dpairs)
		  fill-constraints)))))
	  (unless fail
	    (setq fc (find-simplify-fill-constraint current-evars fill-constraints))
	    (when fc
	      (setq change t)
	      (multiple-value-setq
	       (fail current-evars theta dpairs fill-constraints)
	       (simplify-fill-constraint
		fc
		original-evars current-evars theta dpairs
		(remove fc fill-constraints))))))
    (values fail current-evars theta dpairs fill-constraints)))

(defun find-simplify-dpair (current-evars dpairs)
  (let ((dpair nil)
	(h1 nil)
	(h2 nil))
    (loop until (or dpair (null dpairs)) do
	  (setq dpair (pop dpairs))
	  (unless (or (dpi-p (cadddr dpair))
		      (dclass-p (cadddr dpair))
		      (let ((trm1 (cadr dpair))
			    (trm2 (caddr dpair)))
			(setq h1 (term-extr-head trm1))
			(setq h2 (term-extr-head trm2))
			(or (and (evar-p h1)
				 (n-1-to-0-p (length (car dpair)) (term-extr-args (cadr dpair)))
				 (not (member h1 (free-evars (caddr dpair))))
				 (if (fst-p trm1)
				     (fst-p trm2)
				   (if (snd-p trm1)
				       (snd-p trm2)
				     t))
				 )
			    (and (evar-p h2)
				 (n-1-to-0-p (length (car dpair)) (term-extr-args (caddr dpair)))
				 (not (member h2 (free-evars (cadr dpair))))
				 (if (fst-p trm2)
				     (fst-p trm1)
				   (if (snd-p trm2)
				       (snd-p trm1)
				     t))
				 )
			    (and (rigid-p h1) (rigid-p h2)))))
	    (setq dpair nil)))
    dpair))

(defun find-simplify-dpair-2 (current-evars dpairs)
  (let ((dpair nil)
	(h1 nil)
	(h2 nil))
    (loop until (or dpair (null dpairs)) do
	  (setq dpair (pop dpairs))
	  (unless (or (pf-p (cadddr dpair))
		      (and (obj-p (cadddr dpair))
			   (let ((trm1 (cadr dpair))
				 (trm2 (caddr dpair)))
			     (setq h1 (term-extr-head trm1))
			     (setq h2 (term-extr-head trm2))
			     (or (and (evar-p h1) (fst-p trm1))
				 (and (evar-p h2) (fst-p trm2))))))
	    (setq dpair nil)))
    dpair))

(defun find-simplify-fill-constraint (current-evars fill-constraints)
  (let ((fc nil)
	(h nil))
    (loop until (or fc (null fill-constraints)) do
	  (setq fc (pop fill-constraints))
	  (unless (or (dpi-p (caddr fc))
		      (dclass-p (caddr fc))
		      (progn
			(setq h (term-extr-head (cadr fc)))
			(rigid-p h)))
	    (setq fc nil)))
    fc))

(defun simplify-dpair (dpair original-evars current-evars theta dpairs fill-constraints)
  (when (> *verbose* 80)
    (format t "Simplify dpair~%~d~%~d~%~d~%~d~%"
	    (car dpair)
	    (output-term-string (cadr dpair))
	    (output-term-string (caddr dpair))
	    (output-type-string (cadddr dpair))
	    )
    (sanity-check (cadr dpair) (cadddr dpair) (car dpair) current-evars)
    (sanity-check (caddr dpair) (cadddr dpair) (car dpair) current-evars))
  (if (dpi-p (cadddr dpair))
      (let ((ctx (car dpair))
	    (trm1 (cadr dpair))
	    (trm2 (caddr dpair))
	    (tp (cadddr dpair)))
	(loop while (dpi-p tp) do
	      (setq ctx (ctx-cons (dpi-dom tp) ctx))
	      (setq trm1 (gen-lam-body trm1))
	      (setq trm2 (gen-lam-body trm2))
	      (setq tp (dpi-cod tp)))
	(values nil current-evars theta
		(cons (list ctx trm1 trm2 tp)
		      dpairs)
		fill-constraints))
    (let* ((trm1 (cadr dpair))
	   (trm2 (caddr dpair))
	   (h1 (term-extr-head trm1))
	   (h2 (term-extr-head trm2)))
      (if (and (evar-p h1) ; if we don't check everything again, then dclass types that should be split will try to subst for flex head
	       (n-1-to-0-p (length (car dpair)) (term-extr-args (cadr dpair)))
	       (not (member h1 (free-evars (caddr dpair))))
	       (if (fst-p trm1)
		   (fst-p trm2)
		 (if (snd-p trm1)
		     (snd-p trm2)
		   t)))
	  (let ((n (length (car dpair)))
		(b trm2))
	    (cond ((fst-p trm1)
		   (setq b (fst-arg trm2)))
		  ((snd-p trm1)
		   (setq b (snd-arg trm2))))
	    (dotimes (i n)
	      (setq b (lam b)))
	    (values nil
		    (mapcar #'(lambda (z)
				(cons (car z)
				      (normalize-type (subst-type-1 h1 b (cdr z)))))
			    (remove h1 current-evars :key #'car))
		    (compose-theta-1 h1 b
				     (extend-theta-by-id original-evars theta))
		    (subst-1-dpairs h1 b dpairs)
		    (subst-1-fill-constraints h1 b fill-constraints)))
	(if (and (evar-p h2) ; must check again
		 (n-1-to-0-p (length (car dpair)) (term-extr-args (caddr dpair)))
		 (not (member h2 (free-evars (cadr dpair))))
		 (if (fst-p trm2)
		     (fst-p trm1)
		   (if (snd-p trm2)
		       (snd-p trm1)
		     t)))
	    (let ((n (length (car dpair)))
		  (b trm1))
	      (cond ((fst-p trm2)
		     (setq b (fst-arg trm1)))
		    ((snd-p trm2)
		     (setq b (snd-arg trm1))))
	      (dotimes (i n)
		(setq b (lam b)))
	      (values nil
		      (mapcar #'(lambda (z)
				  (cons (car z)
					(normalize-type (subst-type-1 h2 b (cdr z)))))
			      (remove h2 current-evars :key #'car))
		      (compose-theta-1 h2 b (extend-theta-by-id original-evars theta))
		      (subst-1-dpairs h2 b dpairs)
		      (subst-1-fill-constraints h2 b fill-constraints)))
	  (if (dclass-p (cadddr dpair))
	      (values nil current-evars theta
		      (cons (list (car dpair) (gen-pair-fst (cadr dpair)) (gen-pair-fst (caddr dpair))
				  (obj))
			    (cons (list (car dpair) (gen-pair-snd (cadr dpair)) (gen-pair-snd (caddr dpair))
					(pf (pair-prop (cadddr dpair) (gen-pair-fst (cadr dpair)))))
				  dpairs))
		      fill-constraints)
	    (if (eq h1 h2) ; rigid-rigid
		(let* ((psi (car dpair))
		       (htp (ctx-extract-type psi h1))
		       (args1 (term-extr-args trm1))
		       (args2 (term-extr-args trm2))
		       (ai nil)
		       (bi nil)
		       (ci nil)
		       (f #'identity)
		       (dbsub 'ID))
		  (if (fst-p trm1)
		      (if (fst-p trm2)
			  (do ((ftp htp (dpi-cod ftp)))
			      ((null (dpi-p ftp))
			       (values nil current-evars theta dpairs fill-constraints))
			      (setq ai (pop args1))
			      (setq bi (pop args2))
			      (setq ci (dpi-dom ftp))
					;				 (sanity-check ai (normalize-type (dbsubst-type ci f dbsub)) nil) ; delete me
					;				 (sanity-check bi (normalize-type (dbsubst-type ci f dbsub)) nil) ; delete me
			      (push (list psi ai bi (normalize-type (dbsubst-type ci f dbsub)))
				    dpairs)
			      (setq dbsub (cons ai (cons f dbsub))))
			t ; fail
			)
		    (if (snd-p trm1)
			(if (snd-p trm2)
			    (do ((ftp htp (dpi-cod ftp)))
				((null (dpi-p ftp))
				 (if (dclass-p ftp)
				     (values nil current-evars theta 
					     (cons (list psi (pf-prop (cadddr dpair))
							 (normalize
							  (app (dbsubst (dclass-pred ftp) f dbsub)
							       (fst (snd-arg trm1))))
							 (prop))
						   dpairs)
					     fill-constraints)
				   t ; fail
				   ))
				(setq ai (pop args1))
				(setq bi (pop args2))
				(setq ci (dpi-dom ftp))
					;				 (sanity-check ai (normalize-type (dbsubst-type ci f dbsub)) nil) ; delete me
					;				 (sanity-check bi (normalize-type (dbsubst-type ci f dbsub)) nil) ; delete me
				(push (list psi ai bi (normalize-type (dbsubst-type ci f dbsub)))
				      dpairs)
				(setq dbsub (cons ai (cons f dbsub))))
			  t ; fail
			  )
		      (if (or (fst-p trm2) (snd-p trm2))
			  t ; fail
			(do ((ftp htp (dpi-cod ftp)))
			    ((null (dpi-p ftp))
			     (if (pf-p ftp)
				 (values nil current-evars theta 
					 (cons (list psi (pf-prop (cadddr dpair))
						     (normalize
						      (dbsubst (pf-prop ftp) f dbsub))
						     (prop))
					       dpairs)
					 fill-constraints)
			       (values nil current-evars theta dpairs fill-constraints)))
			    (setq ai (pop args1))
			    (setq bi (pop args2))
			    (setq ci (dpi-dom ftp))
					;				 (sanity-check ai (normalize-type (dbsubst-type ci f dbsub)) nil) ; delete me
					;				 (sanity-check bi (normalize-type (dbsubst-type ci f dbsub)) nil) ; delete me
			    (push (list psi ai bi (normalize-type (dbsubst-type ci f dbsub)))
				  dpairs)
			    (setq dbsub (cons ai (cons f dbsub))))))))
	      (if (pf-p (cadddr dpair)) ; then split into two fills
		  (values nil current-evars theta
			  dpairs
			  (cons (list (car dpair) (cadr dpair) (cadddr dpair))
				(cons (list (car dpair) (caddr dpair) (cadddr dpair))
				      fill-constraints)))
		t ; fail
		))))))))

(defun simplify-dpair-2 (dpair original-evars current-evars theta dpairs fill-constraints)
  (when (> *verbose* 80)
    (format t "Simplify dpair-2~%~S~%~d~%~d~%"
	    (car dpair)
	    (output-term-string (cadr dpair))
	    (output-term-string (caddr dpair)))
    (sanity-check (cadr dpair) (cadddr dpair) (car dpair) current-evars)
    (sanity-check (caddr dpair) (cadddr dpair) (car dpair) current-evars)
    )
  (let* ((trm1 (cadr dpair))
	 (trm2 (caddr dpair))
;	 (tp (cadddr dpair))
	 (h1 (term-extr-head trm1))
	 (h2 (term-extr-head trm2)))
    (if (and (evar-p h1) (or (fst-p trm1) (snd-p trm1)))
	(multiple-value-bind
	 (trm newevars)
	 (split-evar-to-pair (cdr (assoc h1 current-evars)) h1)
	 (values nil
		 (append newevars 
			 (mapcar #'(lambda (x)
				     (cons (car x)
					   (normalize-type (subst-type-1 h1 trm (cdr x)))))
				 (remove h1 current-evars :key #'car)))
		 (compose-theta-1 h1 trm (extend-theta-by-id original-evars theta))
		 (subst-1-dpairs h1 trm (cons dpair dpairs))
		 (subst-1-fill-constraints h1 trm fill-constraints)))
      (if (and (evar-p h2) (or (fst-p trm2) (snd-p trm2)))
	  (multiple-value-bind
	   (trm newevars)
	   (split-evar-to-pair (cdr (assoc h2 current-evars)) h2)
	   (values nil
		   (append newevars 
			   (mapcar #'(lambda (x)
				       (cons (car x)
					     (normalize-type (subst-type-1 h2 trm (cdr x)))))
				   (remove h2 current-evars :key #'car)))
		   (compose-theta-1 h2 trm (extend-theta-by-id original-evars theta))
		   (subst-1-dpairs h2 trm (cons dpair dpairs))
		   (subst-1-fill-constraints h2 trm fill-constraints)))
	(values nil current-evars theta dpairs
		(cons (list (car dpair) (cadr dpair) (cadddr dpair))
		      (cons (list (car dpair) (caddr dpair) (cadddr dpair))
			    fill-constraints)))))))

(defun split-evar-to-pair (tp &optional evar)
  (multiple-value-bind
   (ctx atp)
   (dtp-argctx tp)
   (if (dclass-p atp)
       (let* ((evar1 (intern-gensym))
	      (evar2 (intern-gensym))
	      (trm1 (app-n-1-to-0 (length ctx) evar1))
	      (trm2 (app-n-1-to-0 (length ctx) evar2))
	      (pftp (pf (normalize (app (dclass-pred atp) trm1)))))
	 (setf (get evar1 'evar) t)
	 (setf (get evar2 'evar) t)
	 (setf (get evar1 'split-from) evar)
	 (setf (get evar2 'split-from) evar)
	 (values (lam-ctx ctx (pair trm1 trm2))
		 (list (cons evar1 (dpi-ctx ctx (obj)))
		       (cons evar2 (dpi-ctx ctx pftp)))))
     (fail "problem - split-evar-to-pair given tp that does not return a dclass" tp))))

(defun simplify-fill-constraint (fc original-evars current-evars theta dpairs fill-constraints)
  (when (> *verbose* 80)
    (format t "Simplify fill-constraint~%~S~%~d~%~d~%"
	    (car fc)
	    (output-term-string (cadr fc))
	    (output-type-string (caddr fc))
	    )
    (sanity-check (cadr fc) (caddr fc) (car fc) current-evars)
    )
  (cond ((dpi-p (caddr fc))
	 (let ((ctx (car fc))
	       (trm1 (cadr fc))
	       (tp (caddr fc)))
	   (loop while (dpi-p tp) do
		 (setq ctx (ctx-cons (dpi-dom tp) ctx))
		 (setq trm1 (gen-lam-body trm1))
		 (setq tp (dpi-cod tp)))
	   (values nil current-evars theta
		   dpairs
		   (cons (list ctx trm1 tp)
			 fill-constraints))))
	((dclass-p (caddr fc))
	 (values nil current-evars theta
		 dpairs
		 (cons (list (car fc) (gen-pair-fst (cadr fc)) (obj))
		       (cons (list (car fc) (gen-pair-snd (cadr fc)) 
				   (pf (pair-prop (caddr fc) (gen-pair-fst (cadr fc)))))
			     fill-constraints))))
	(t ; rigid
	 (let* ((trm (cadr fc))
		(h (term-extr-head trm))
		(psi (car fc))
		(htp (ctx-extract-type psi h))
		(args (term-extr-args trm))
		(ai nil)
		(ci nil)
		(f #'identity)
		(dbsub 'ID))
	   (if (fst-p trm)
	       (do ((ftp htp (dpi-cod ftp)))
		   ((null (dpi-p ftp))
		    (values nil current-evars theta dpairs fill-constraints))
		   (setq ai (pop args))
		   (setq ci (dpi-dom ftp))
;				 (sanity-check ai (normalize-type (dbsubst-type ci f dbsub)) nil) ; delete me
		   (push (list psi ai (normalize-type (dbsubst-type ci f dbsub)))
			 fill-constraints)
		   (setq dbsub (cons ai (cons f dbsub))))
	     (if (snd-p trm)
		 (do ((ftp htp (dpi-cod ftp)))
		     ((null (dpi-p ftp))
		      (if (dclass-p ftp)
			  (values nil current-evars theta 
				  (cons (list psi (pf-prop (caddr fc))
					      (normalize
					       (app (dbsubst (dclass-pred ftp) f dbsub)
						    (fst (snd-arg trm))))
					      (prop))
					dpairs)
				  fill-constraints)
			t ; fail
			))
		     (setq ai (pop args))
		     (setq ci (dpi-dom ftp))
;				 (sanity-check ai (normalize-type (dbsubst-type ci f dbsub)) nil) ; delete me
		     (push (list psi ai (normalize-type (dbsubst-type ci f dbsub)))
			   fill-constraints)
		     (setq dbsub (cons ai (cons f dbsub))))
	       (do ((ftp htp (dpi-cod ftp)))
		   ((null (dpi-p ftp))
		    (if (pf-p ftp)
			(values nil current-evars theta 
				(cons (list psi (pf-prop (caddr fc))
					    (normalize
					     (dbsubst (dclass-pred ftp) f dbsub))
					    (prop))
				      dpairs)
				fill-constraints)
		      (values nil current-evars theta dpairs fill-constraints)))
		   (setq ai (pop args))
		   (setq ci (dpi-dom ftp))
;				 (sanity-check ai (normalize-type (dbsubst-type ci f dbsub)) nil) ; delete me
		   (push (list psi ai (normalize-type (dbsubst-type ci f dbsub)))
			 fill-constraints)
		   (setq dbsub (cons ai (cons f dbsub))))))))))

(defun n-1-to-0-p (n args)
  (if (> n 0)
      (let ((k (- n 1)))
	(if (equal k (car args))
	    (n-1-to-0-p k (cdr args))
	  nil))
    (if args
	nil
      t)))

(defun compose-theta-1 (x a theta)
  (mapcar #'(lambda (p)
	      (let ((y (car p))
		    (b (cdr p)))
;		(setf (get y 'dbtype) (normalize (subst-type-1 x a (get y 'dbtype))))
		(cons y (normalize (subst-1 x a b)))))
	  theta))

(defun compose-thetas (theta2 theta)
  (mapcar #'(lambda (p)
	      (let ((y (car p))
		    (b (cdr p)))
;		(setf (get y 'dbtype) (normalize (simul-subst-type theta2 (get y 'dbtype))))
		(cons y (normalize (simul-subst theta2 b)))))
	  theta))

(defun extend-theta-by-id (dom theta)
  (dolist (x dom)
    (unless (assoc (car x) theta)
      (push (cons (car x) (car x)) theta)))
  theta)

(defun subst-1-dpairs (x b dpairs)
  (mapcar #'(lambda (p)
	      (list (subst-ctx-1 x b (car p)) ; normalizes
		    (normalize (subst-1 x b (cadr p)))
		    (normalize (subst-1 x b (caddr p)))
		    (normalize-type (subst-type-1 x b (cadddr p)))))
	  dpairs))

(defun subst-1-fill-constraints (x b fcs)
  (mapcar #'(lambda (p)
	      (list (subst-ctx-1 x b (car p)) ; normalizes
		    (normalize (subst-1 x b (cadr p)))
		    (normalize-type (subst-type-1 x b (caddr p)))))
	  fcs))

(defun rename-dpairs (phi dpairs)
  (mapcar #'(lambda (p)
	      (list (rename-ctx phi (car p))
		    (simul-subst phi (cadr p))
		    (simul-subst phi (caddr p))
		    (simul-subst-type phi (cadddr p))))
	  dpairs))

(defun rename-fill-constraints (phi fcs)
  (mapcar #'(lambda (p)
	      (list (rename-ctx phi (car p))
		    (simul-subst phi (cadr p))
		    (simul-subst-type phi (caddr p))))
	  fcs))

; returns trm (db closed), return type (in ctx) and new evars
(defun gen-imitation-term (trm tp ctx)
  (multiple-value-bind
   (trm1 tp1 evars1) 
   (general-term trm tp ctx)
   (values (normalize trm1) tp1 evars1)))

(defun gen-imitation-for-type (trm tp dtp)
  (gen-imitation-term trm tp (dtp-argctx dtp)))

; returns trm (db closed), return type (in ctx) and new evars
(defun imitation-term (h ctx)
  (general-term h (get h 'dbtype) ctx))

(defun imitation-for-type (h dtp)
  (imitation-term h (dtp-argctx dtp)))

; returns trm (db closed), return type (in ctx) and new evars
(defun projection-term (i ctx)
  (general-term i (dbshift-type-n (1+ i) (nth i ctx)) ctx))

(defun projection-for-type (i dtp)
  (projection-term i (dtp-argctx dtp)))

; returns trm (db closed), return type (in ctx) and new evars w/types
(defun general-term (trm dtp ctx)
  (let ((evars nil)
	(n (- (length ctx) 1)))
    (loop while (dpi-p dtp) do
	  (let* ((dom (dpi-dom dtp))
		 (x (intern-gensym))
		 (xtp dom)
		 (xtrm x))
	    (do ((i n (- i 1))
		 (c ctx (cdr c)))
		((null c))
		(setq xtp (dpi (car c) xtp))
		(setq xtrm (app xtrm i)))
	    (setf (get x 'evar) t)
	    (push (cons x xtp) evars)
	    (setq trm (app trm xtrm))
	    (setq dtp (dbsubst-type-0 (dpi-cod dtp) xtrm))))
    (dolist (c ctx)
      (setq trm (lam trm)))
    (values trm dtp evars)))

(defun unif-trm-fills-type (trm tp ftp &optional ctx)
  (if (dpi-p ftp)
      (let ((trm (unif-trm-fills-type trm tp (dpi-cod ftp) (ctx-cons (dpi-dom ftp) ctx))))
	(if trm
	    (lam trm)
	  nil))
    (multiple-value-bind
     (trm2 tp2 evars2)
     (general-term trm tp ctx)
     (let ((dpairs
	    (cond ((and (pf-p ftp) (pf-p tp2))
		   (list (list ctx (pf-prop ftp) (pf-prop tp2) (prop))))
		  ((and (dclass-p ftp) (dclass-p tp2))
		   (list (list ctx (dclass-pred ftp) (dclass-pred tp2) *pred*)))
		  ((and (univ-p ftp) (univ-p tp2)) nil)
		  ((and (prop-p ftp) (prop-p tp2)) nil)
		  (t 'fail))))
       (if (eq dpairs 'fail)
	   nil
	 (let ((fcl (mapcar #'(lambda (x)
				(list nil (car x) (cdr x)))
			    evars2)))
	   (multiple-value-bind
	    (fail cevars theta dpairs2 fcl2)
	    (simplify-constraints evars2 evars2 nil dpairs fcl)
	    (if (and (not fail) (not cevars) (not dpairs2) (not fcl2))
		(simul-subst theta trm2)
	      nil))))))))

(defun trm-easily-fills (evar etp trm tp 
			      original-evars current-evars theta
			      dpairs
			      fill-constraints)
  (multiple-value-bind
   (fail current-evars theta dpairs fill-constraints)
   (add-constraints-equal-types (list (list nil etp tp))
				original-evars current-evars theta
				dpairs fill-constraints)
   (if fail
       fail
     (simplify-constraints original-evars 
			   (remove evar current-evars :key #'car)
			   (if (assoc evar original-evars)
			       (acons evar trm 
				      (compose-theta-1 evar trm theta))
			     (compose-theta-1 evar trm theta))
			   (subst-1-dpairs evar trm dpairs)
			   (subst-1-fill-constraints evar trm fill-constraints)))))

(defun add-constraints-equal-types (tpdpairs
				    original-evars current-evars theta
				    dpairs fill-constraints)
  (if tpdpairs
      (let ((ctx (caar tpdpairs))
	    (tp1 (cadar tpdpairs))
	    (tp2 (caddar tpdpairs)))
	(if (dpi-p tp1)
	    (if (dpi-p tp2)
		(add-constraints-equal-types (cons (list ctx (dpi-dom tp1) (dpi-dom tp2))
						   (cons (list (ctx-cons (dpi-dom tp1) ctx) (dpi-cod tp1) (dpi-cod tp2))
							 (cdr tpdpairs)))
					     original-evars current-evars theta
					     dpairs fill-constraints)
	      t)
	  (if (dpi-p tp2)
	      t
	    (if (dclass-p tp1)
		(if (dclass-p tp2)
		    (add-constraints-equal-types (cdr tpdpairs)
						 original-evars current-evars theta
						 (cons (list ctx (dclass-pred tp1) (dclass-pred tp2) *pred*)
						       dpairs)
						 fill-constraints)
		  t)
	      (if (dclass-p tp2)
		  t
		(if (pf-p tp1)
		    (if (pf-p tp2)
			(add-constraints-equal-types (cdr tpdpairs)
						     original-evars current-evars theta
						     (cons (list ctx (pf-prop tp1) (pf-prop tp2) (prop))
							   dpairs)
						     fill-constraints)
		      t)
		  (if (pf-p tp2)
		      t
		    (if (eq tp1 tp2) ; use eq, since tp1, tp2 are obj/prop
			(add-constraints-equal-types (cdr tpdpairs)
						     original-evars current-evars theta
						     dpairs
						     fill-constraints)
		      t))))))))
    (values nil current-evars theta dpairs fill-constraints)))

(defun preunify-msv (original-evars current-evars theta
				    dpairs
				    fill-constraints msv
				    &optional stoponsucc)
  (preunify-msva
   original-evars
   (list (list current-evars (extend-theta-by-id original-evars theta)
	       dpairs fill-constraints
	       (mapcar #'(lambda (x) (cons (car x) msv)) current-evars)))
   stoponsucc))

(defun preunify-msva (original-evars unif-states &optional stoponsucc)
  (let ((succ nil)
	(done nil)
	(delayed nil))
    (loop until (or done (null unif-states)) do
	  (let* ((unif-state (pop unif-states))
		 (cevars (car unif-state))
		 (theta (cadr unif-state))
		 (dpairs (nth 2 unif-state))
		 (fill-constraints (nth 3 unif-state))
		 (msva (nth 4 unif-state)))
	    (when (> *verbose* 80)
	      (format t "Unif loop:~%~d~%~d~%" cevars theta)
	      (dolist (dpair dpairs)
		(format t "dpair~%~d~%~d~%~d~%"
			(output-term-string (cadr dpair))
			(output-term-string (caddr dpair))
			(output-type-string (cadddr dpair))
			)
		(sanity-check (cadr dpair) (cadddr dpair) (car dpair) cevars)
		(sanity-check (caddr dpair) (cadddr dpair) (car dpair) cevars)
		)
	      (dolist (fc fill-constraints)
		(format t "fill-constraint~%~d~%~d~%"
			(output-term-string (cadr fc))
			(output-type-string (caddr fc)))
		(sanity-check (cadr fc) (caddr fc) (car fc) cevars)
		)
	      )
	    (multiple-value-bind
	     (fail2 cevars2 theta2 dpairs2 fill-constraints2)
	     (simplify-constraints original-evars cevars theta
				   dpairs
				   fill-constraints)
	     (unless fail2
	       (dolist (cevar cevars2)
		 (unless (assoc (car cevar) msva)
		   (let ((prev (get (car cevar) 'split-from)))
		     (when prev
		       (push (cons (car cevar) (msv prev msva)) msva)))))
	       (multiple-value-bind
		(dp ctx flex rig tp evar righ msv)
		(find-flex-rigid-dpair-msva dpairs2 msva)
		(if dp
		    (let* ((evartp (cdr (assoc evar cevars2)))
			   (evarctx (dtp-argctx evartp)))
		      (when (> *verbose* 70)
			(format t "Working on Flex-Rigid~%~d~%~d~%~d~%~d~%Rig Head ~d~%Evar ~d~%"
				ctx
				(output-term-string flex)
				(output-term-string rig)
				(output-type-string tp)
				righ evar))
		      (decf msv)
		      (unless (numberp righ) ; if debruijn, don't imitate
			(when (> *verbose* 88) (format t "Trying Preunif ~d Imitation ~d~%" evar righ))
			(let* ((msva3 msva)
			       (evars3 cevars2)
			       (dpairs3 dpairs2)
			       (fill-constraints3 fill-constraints2))
			  (multiple-value-bind
			   (trm4 dtp4 evars4)
			   (imitation-term righ evarctx)
			   (when (or (compatible-types-p tp dtp4)
				     (and (dclass-p dtp4) (or (pf-p tp) (obj-p tp))))
			     (when (> *verbose* 80) (format t "Preunif ~d Imitating ~d~%" evar righ))
			     (if (and (dclass-p dtp4) (pf-p tp))
				 (progn
				   (setq dtp4 (pf (normalize (app (dclass-pred dtp4) (fst (app-n-1-to-0 (length evarctx) trm4))))))
				   (setq trm4 (normalize
					       (lam-ctx evarctx
							(snd (app-n-1-to-0 (length evarctx) trm4))))))
			       (when (and (dclass-p dtp4) (obj-p tp))
				 (setq dtp4 (obj))
				 (setq trm4 
				       (normalize 
					(lam-ctx evarctx
						 (fst (app-n-1-to-0 (length evarctx) trm4)))))))
			     (when (or (not *unif-debug*)
				       (unif-debug-query evar trm4))
			       (push (list nil evar trm4 evartp) dpairs3)
			       (dolist (x evars4)
				 (push (cons (car x) msv) msva3)
				 (push x evars3)
				 (push (list nil (car x) (cdr x)) fill-constraints3))
			       (push (list evars3 theta2 dpairs3 fill-constraints3 msva3)
				     unif-states))))))
		      (let ((i 0)) ; projections
			(do ((etp evartp (dpi-cod etp)))
			    ((not (dpi-p etp)))
			    (let* ((msva3 msva)
				   (evars3 cevars2)
				   (dpairs3 dpairs2)
				   (fill-constraints3 fill-constraints2))
			      (when (> *verbose* 88) (format t "Trying Preunif ~d Projection ~d~%" evar i))
			      (multiple-value-bind
			       (trm4 dtp4 evars4)
			       (projection-term i evarctx)
			       (incf i)
			       (when (or (compatible-types-p tp dtp4)
					 (and (dclass-p dtp4) (or (pf-p tp) (obj-p tp))))
				 (when (> *verbose* 80) (format t "Preunif ~d Projecting ~d~%" evar (- i 1)))
				 (if (and (dclass-p dtp4) (pf-p tp))
				     (progn
				       (setq dtp4 (pf (normalize (app (dclass-pred dtp4) (fst (app-n-1-to-0 (length evarctx) trm4))))))
				       (setq trm4 (normalize
						   (lam-ctx evarctx
							    (snd (app-n-1-to-0 (length evarctx) trm4))))))
				   (when (and (dclass-p dtp4) (obj-p tp))
				     (setq dtp4 (obj))
				     (setq trm4 
					   (normalize 
					    (lam-ctx evarctx
						     (fst (app-n-1-to-0 (length evarctx) trm4)))))))
				 (when (or (not *unif-debug*)
					   (unif-debug-query evar trm4))
				   (push (list nil evar trm4 evartp) dpairs3)
				   (dolist (x evars4)
				     (push (cons (car x) msv) msva3)
				     (push x evars3)
				     (push (list nil (car x) (cdr x)) fill-constraints3))
				   (push (list evars3 theta2 dpairs3 fill-constraints3 msva3)
					 unif-states))))))))
		  (if (find-flex-rigid-dpair dpairs2)
		      (progn
			(push (list cevars2 theta2 dpairs2 fill-constraints2 msva) delayed)
			)
		    (progn
		      (push (list cevars2 theta2 dpairs2 fill-constraints2 msva) succ)
		      (when (and stoponsucc
				 (not fill-constraints2))
			(setq done t))))))))))
    (values succ unif-states delayed)))

(defun fill-msv (original-evars current-evars theta
				dpairs
				fill-constraints msv
				usable
				&optional stoponsucc)
  (fill-msva
   original-evars
   (list (list current-evars (extend-theta-by-id original-evars theta)
	       dpairs fill-constraints
	       (mapcar #'(lambda (x) (cons (car x) msv)) current-evars)))
   usable
   stoponsucc))

(defun fill-msva (original-evars unif-states usable &optional stoponsucc)
  (let ((succ nil)
	(done nil)
	(delayed nil))
    (loop until (or done (null unif-states)) do
	  (multiple-value-bind
	   (succ1 unif-states1 delayed1)
	   (preunify-msva original-evars unif-states stoponsucc)
	   (setq unif-states nil)
	   (dolist (unif-state (append succ1 unif-states1 delayed1))
	     (let ((evars (car unif-state))
		   (theta (cadr unif-state))
		   (dpairs (nth 2 unif-state))
		   (fill-constraints (nth 3 unif-state))
		   (msva (nth 4 unif-state))
		   (msv nil)
		   )
	       (when (> *verbose* 80)
		 (format t "Fill loop:~%")
		 (print-unif-state unif-state))
	       (let ((x (find-if #'(lambda (x)
				     (and (dtype-returns-pf-p (cdr x))
					  (> (msv (car x) msva) 1)))
				 evars)))
		 (unless x
		   (setq x (find-if #'(lambda (x)
					(and (dtype-returns-pf-p (cdr x))
					     (> (msv (car x) msva) 0)))
				    evars)))
		 (unless x
		   (setq x (find-if #'(lambda (x)
					(> (msv (car x) msva) 0))
				    evars)))
		 (if x
		     (let* ((evar (car x))
			    (evartp (cdr x)))
		       (multiple-value-bind
			(evarctx tp)
			(dtp-argctx evartp)
			(when (> *verbose* 72)
			  (format t "Filling ~d~%" x))
			(setq msv (- (msv (car x) msva) 1))
			(dolist (i usable)
			  (let* ((msva3 msva)
				 (evars3 evars)
				 (dpairs3 dpairs)
				 (fill-constraints3 fill-constraints))
			    (when (> *verbose* 88) (format t "Trying Fill ~d Imitation ~d~%" i evar))
			    (multiple-value-bind
			     (trm4 dtp4 evars4)
			     (if (consp i)
				 (gen-imitation-term i (cdr i) evarctx)
			       (imitation-term i evarctx))
			     (when (or (compatible-types-p tp dtp4)
				       (and (dclass-p dtp4) (or (pf-p tp) (obj-p tp))))
			       (when (> *verbose* 80) (format t "Fill ~d Imitating ~d~%" i evar))
			       (if (and (dclass-p dtp4) (pf-p tp))
				   (progn
				     (setq dtp4 (pf (normalize (app (dclass-pred dtp4) (fst (app-n-1-to-0 (length evarctx) trm4))))))
				     (setq trm4 (normalize
						 (lam-ctx evarctx
							  (snd (app-n-1-to-0 (length evarctx) trm4))))))
				 (when (and (dclass-p dtp4) (obj-p tp))
				   (setq dtp4 (obj))
				   (setq trm4 
					 (normalize 
					  (lam-ctx evarctx
						   (fst (app-n-1-to-0 (length evarctx) trm4)))))))
			       (push (list nil evar trm4 evartp) dpairs3)
			       (dolist (x evars4)
				 (push (cons (car x) msv) msva3)
				 (push x evars3)
				 (push (list nil (car x) (cdr x)) fill-constraints3))
			       (if (and evars4 (= msv 0))
				   (push (list evars3 theta dpairs3 fill-constraints3 msva3)
					 delayed)
				 (push (list evars3 theta dpairs3 fill-constraints3 msva3)
				       unif-states))))))
			(let ((i 0)) ; projections
			  (do ((etp evartp (dpi-cod etp)))
			      ((not (dpi-p etp)))
			      (let* ((msva3 msva)
				     (evars3 evars)
				     (dpairs3 dpairs)
				     (fill-constraints3 fill-constraints))
				(when (> *verbose* 88) (format t "Trying Fill ~d Projection ~d~%" evar i))
				(multiple-value-bind
				 (trm4 dtp4 evars4)
				 (projection-term i evarctx)
				 (incf i)
				 (when (or (compatible-types-p tp dtp4)
					   (and (dclass-p dtp4) (or (pf-p tp) (obj-p tp))))
				   (when (> *verbose* 80) (format t "Fill ~d Projecting ~d~%" evar (- i 1)))
				   (if (and (dclass-p dtp4) (pf-p tp))
				       (progn
					 (setq dtp4 (pf (normalize (app (dclass-pred dtp4) (fst (app-n-1-to-0 (length evarctx) trm4))))))
					 (setq trm4 (normalize
						     (lam-ctx evarctx
							      (snd (app-n-1-to-0 (length evarctx) trm4))))))
				     (when (and (dclass-p dtp4) (obj-p tp))
				       (setq dtp4 (obj))
				       (setq trm4
					     (normalize 
					      (lam-ctx evarctx
						       (fst (app-n-1-to-0 (length evarctx) trm4)))))))
				   (push (list nil evar trm4 evartp) dpairs3)
				   (dolist (x evars4)
				     (push (cons (car x) msv) msva3)
				     (push x evars3)
				     (push (list nil (car x) (cdr x)) fill-constraints3))
				   (if (and evars4 (= msv 0))
				       (push (list evars3 theta dpairs3 fill-constraints3 msva3)
					     delayed)
				     (push (list evars3 theta dpairs3 fill-constraints3 msva3)
					   unif-states)))))))))
		   (if evars
		       (push (list evars theta dpairs fill-constraints msva) delayed)
		     (if (or dpairs fill-constraints)
			 (fail "How can there be constraints with no more evars?" theta dpairs fill-constraints)
		       (progn
			 (push (list nil theta nil nil nil) succ)
			 (when stoponsucc
			   (setq done t)))))))))))
    (values succ unif-states delayed)))

(defun find-flex-rigid-dpair (dpairs)
  (let ((done nil)
	(dp nil)
	(ctx nil)
	(flex nil)
	(rig nil)
	(tp nil)
	(evar nil)
	(righ nil)
	)
    (loop until (or done (null dpairs)) do
	  (let* ((d (pop dpairs))
		 (h1 (term-extr-head (cadr d)))
		 (h2 (term-extr-head (caddr d))))
	    (if (evar-p h1) 
		(when (rigid-p h2)
		  (setq done t)
		  (setq dp d)
		  (setq ctx (car d))
		  (setq flex (cadr d))
		  (setq rig (caddr d))
		  (setq evar h1)
		  (setq righ h2)
		  (setq tp (cadddr d)))
	      (when (evar-p h2)
		(setq done t)
		(setq dp d)
		(setq ctx (car d))
		(setq flex (caddr d))
		(setq rig (cadr d))
		(setq evar h2)
		(setq righ h1)
		(setq tp (cadddr d))))))
    (values dp ctx flex rig tp evar righ)))

(defun find-flex-rigid-dpair-msva (dpairs msva)
  (let ((done nil)
	(dp nil)
	(ctx nil)
	(flex nil)
	(rig nil)
	(tp nil)
	(evar nil)
	(msv nil)
	(righ nil)
	)
    (loop until (or done (null dpairs)) do
	  (let* ((d (pop dpairs))
		 (h1 (term-extr-head (cadr d)))
		 (h2 (term-extr-head (caddr d))))
	    (if (evar-p h1) 
		(when (rigid-p h2)
		  (let ((e (assoc h1 msva)))
		    (when (and e (> (cdr e) 0))
		      (setq done t)
		      (setq dp d)
		      (setq ctx (car d))
		      (setq flex (cadr d))
		      (setq rig (caddr d))
		      (setq evar h1)
		      (setq msv (cdr e))
		      (setq righ h2)
		      (setq tp (cadddr d)))))
	      (when (evar-p h2)
		(let ((e (assoc h2 msva)))
		  (when (and e (> (cdr e) 0))
		    (setq done t)
		    (setq dp d)
		    (setq ctx (car d))
		    (setq flex (caddr d))
		    (setq rig (cadr d))
		    (setq evar h2)
		    (setq msv (cdr e))
		    (setq righ h1)
		    (setq tp (cadddr d))))))))
    (values dp ctx flex rig tp evar righ msv)))

(defun dtp-argctx (dtp)
  (let ((ctx *emptyctx*))
    (loop while (dpi-p dtp) do
	  (setq ctx (ctx-cons (dpi-dom dtp) ctx))
	  (setq dtp (dpi-cod dtp)))
    (values ctx dtp)))

(defun fill-guess (x xtp dtp &optional (imits *global-sigma*))
  (multiple-value-bind
   (ctx atp)
   (dtp-argctx xtp)
   (let ((succ nil))
     (dolist (i imits)
       (when (> *verbose* 88) (format t "Trying Fill Guess Imitation ~d~%" i))
       (multiple-value-bind
	(trm tp evars)
	(imitation-term i ctx)
	(when (compatible-types-p tp atp)
	  (when (> *verbose* 80) (format t "Fill Guess Imitating ~d~%" i))
	  (setq succ
		(append
		 succ
		 (preunify-msv (acons x xtp evars) (acons x xtp evars) nil
			       (list (list nil x trm xtp))
			       (cons (list nil x dtp)
				     (cons (list nil x xtp)
					   (mapcar #'(lambda (e) (list nil (car e) (cdr e)))
						   evars)))
			       2))))))
     (dotimes (i (length ctx))
       (when (> *verbose* 88) (format t "Trying Fill Guess Projection ~d~%" i))
       (multiple-value-bind
	(trm tp evars)
	(projection-term i ctx)
	(when (compatible-types-p tp atp)
	  (when (> *verbose* 80) (format t "Fill Guess Projecting ~d~%" i))
	  (setq succ
		(append
		 succ
		 (preunify-msv (acons x xtp evars) (acons x xtp evars) nil
			       (list (list nil x trm xtp))
			       (cons (list nil x dtp)
				     (cons (list nil x xtp)
					   (mapcar #'(lambda (e) (list nil (car e) (cdr e)))
						   evars)))
			       2))))))
     succ)))

(defun compatible-types-p (tp atp)
  (or (and (pf-p tp) (pf-p atp))
      (and (dclass-p tp) (dclass-p atp))
      (eq tp atp))) ; obj/prop

(defun msv (x msva)
  (let ((a (assoc x msva)))
    (if a
	(cdr a)
      0)))

(defun fill-claim-msv (name msv)
  (let ((x (intern-gensym))
	(usable nil))
    (setf (get x 'evar) t)
    (dolist (c *global-sigma*)
      (when (< (get c 'timestamp) (get name 'timestamp))
	(push c usable)))
    (let* ((tp (get name 'dbtype))
	   (evars (list (cons x tp)))
	   (succ (fill-msv evars evars nil nil (list (list nil x tp)) msv usable t)))
      (if succ
	  (let* ((theta (cadar succ))
		 (trm (cdr (assoc x theta))))
	    (if (ctx-term-type-p nil trm tp)
		(progn
		  (when (> *verbose* 5)
		    (format t "Fill-msv ~d suggested term~%~d~%to fill claim ~d~%"
			  msv
			  (output1-normal-string trm)
			  name))
		  (setf (get name 'filled) trm)
		  trm
		  )
	      (progn
		(when (> *verbose* 5)
		  (format t "Fill-msv ~d suggested ill-typed term~%~d~%to fill claim ~d~%"
			  msv
			  (output1-normal-string trm)
			  name))
		nil)))
	(progn
	  (when (> *verbose* 5)
	    (format t "Fill-msv ~d failed to fill claim ~d~%" msv name))
	  nil)))))

(defun print-unif-state (unif-state)
  (format t "Unif State:~%")
  (let* ((evars (car unif-state))
	 (theta (cadr unif-state))
	 (dpairs (caddr unif-state))
	 (fill-constraints (cadddr unif-state))
	 (pfvars (remove-if-not #'(lambda (x)
				    (dtype-returns-pf-p (cdr x)))
				evars))
	 (propvars (remove-if-not #'(lambda (x)
				      (dtype-returns-prop-p (cdr x)))
				  evars))
	 (objvars (remove-if-not #'(lambda (x)
				     (dtype-returns-obj-p (cdr x)))
				 evars))
	 )
    (when pfvars
      (format t "Free Pf Vars: ~d~%" (mapcar #'car pfvars))
      (dolist (z pfvars)
	(format t "~d:~d~%" (car z) (output1-type-string (cdr z)))))
    (when propvars
      (format t "Free Prop Vars: ~d~%" (mapcar #'car propvars)))
    (when objvars
      (format t "Free Obj Vars: ~d~%" (mapcar #'car objvars)))
    (when theta
      (format t "theta:~%")
      (dolist (p theta)
	(format t "~d -> ~d~%" (car p) (output1-normal-string (cdr p)))))
    (dolist (dpair dpairs)
      (format t "dpair~%~d~%~d~%~d~%~d~%"
	      (car dpair)
	      (output-term-string (cadr dpair))
	      (output-term-string (caddr dpair))
	      (output-type-string (cadddr dpair))
	      )
      (sanity-check (cadr dpair) (cadddr dpair) (car dpair) evars)
      (sanity-check (caddr dpair) (cadddr dpair) (car dpair) evars)
      )
    (dolist (fc fill-constraints)
      (format t "fill-constraint~%~d~%~d~%~d~%"
	      (car fc)
	      (output-term-string (cadr fc))
	      (output-type-string (caddr fc)))
      (sanity-check (cadr fc) (caddr fc) (car fc) evars)
      )))

(defun sanity-check (trm tp ctx evars)
  (sanity-check-2 (lam-ctx ctx trm) (dtype-erasure (dpi-ctx ctx tp)) nil evars))

(defun dtype-erasure (tp)
  (cond ((dpi-p tp)
	 (cons (dtype-erasure (dpi-dom tp))
	       (dtype-erasure (dpi-cod tp))))
	((dclass-p tp) 'CLASS)
	((pf-p tp) 'PF)
	((obj-p tp) 'OBJ)
	((prop-p tp) 'PROP)
	(t nil)))

(defun sanity-check-2 (trm stp &optional sctx evars)
  (cond ((lam-p trm)
	 (if (consp stp)
	     (sanity-check-2 (lam-body trm) (cdr stp) (cons (car stp) sctx) evars)
	   (fail "lam for nonfn tp erasure" trm stp sctx)))
	((pair-p trm)
	 (if (eq stp 'CLASS)
	     (and (sanity-check-2 (pair-fst trm) 'OBJ sctx evars)
		  (sanity-check-2 (pair-snd trm) 'PF sctx evars))
	   (fail "pair for nonclass tp erasure")))
	(t
	 (let ((estp (sanity-check-3 trm sctx evars)))
	   (when estp
	     (unless (equal stp estp)
	       (fail "insane type erasures" trm stp estp sctx)))))))

(defun sanity-check-3 (trm &optional sctx evars)
  (cond ((app-p trm)
	 (let ((fstp (sanity-check-3 (app-func trm) sctx evars)))
	   (if fstp
	       (if (consp fstp)
		   (progn
		     (sanity-check-2 (app-arg trm) (car fstp) sctx evars)
		     (cdr fstp))
		 (fail "app of nonfn tp erasure" trm fstp sctx))
	     (progn
	       (sanity-check-3 (app-arg trm) sctx evars)
	       nil))))
	((fst-p trm)
	 (sanity-check-2 (fst-arg trm) 'CLASS sctx evars))
	((snd-p trm)
	 (sanity-check-2 (snd-arg trm) 'CLASS sctx evars))
	((numberp trm)
	 (nth trm sctx))
	((symbolp trm)
	 (if (get trm 'dbtype)
	     (dtype-erasure (get trm 'dbtype))
	   (let ((a (assoc trm evars)))
	     (if a
		 (dtype-erasure (cdr a))
	       (fail "Unknown symbol " trm sctx evars)))))
	((or (lam-p trm) (pair-p trm)) nil) ; not normal?
	(t (fail "unknown term case" trm))))

; a version that does not preserve order; probably exponential in worst case
(defun quick-ctx-fill (ctx tp &optional (depth 1) (justone t))
  (if (dpi-p tp)
      (let ((trml (quick-ctx-fill (ctx-cons (dpi-dom tp) ctx) (dpi-cod tp) depth justone)))
	(mapcar #'(lambda (trm)
		    (lam trm))
		trml))
    (let ((trml nil)
	  (ctx2 nil))
      (when (pf-p tp)
	(setq justone t))
      (do ((ctx2 ctx (cdr ctx2))
	   (i 0 (1+ i)))
	  ((or (and trml justone) (null ctx2))
	   trml)
	  (if (dpi-p (car ctx2))
	      (when (> depth 0)
		(let ((argsl (quick-ctx-fill-args ctx 
						  (dbshift-type-n (1+ i) (car ctx2))
						  (- depth 1) justone)))
		  (do ((argsl2 argsl (cdr argsl2)))
		      ((or (and trml justone) (null argsl2)))
		      (let ((z (app-n i (car argsl2))))
			(when (ctx-term-type-p ctx z tp)
			  (push z trml))))))
	    (when (ctx-term-type-p ctx i tp)
	      (push i trml)))))))

(defun quick-ctx-fill-args (ctx tp &optional (depth 1) (justone t))
  (if (dpi-p tp)
      (let ((arg1l (quick-ctx-fill ctx (dpi-dom tp) depth
				   (if (dpi-p (dpi-cod tp))
				       nil
				     justone)))
	    (argsl nil))
	(do ((arg1l2 arg1l (cdr arg1l2)))
	    ((or (and argsl justone) (null arg1l2))
	     argsl)
	    (let* ((arg1 (car arg1l2))
		   (tp2 (dbsubst-type-0 (dpi-cod tp) arg1))
		   (argsl2 (quick-ctx-fill-args ctx tp2 depth justone)))
	      (setq argsl
		    (append argsl
			    (mapcar #'(lambda (args2)
					(cons arg1 args2)
					)
				    argsl2))))))
    (list nil)))

; if h is an extraction, then the values returned are extractions
; otherwise, the values may not be normal
(defun quick-ctx-instances (h htp ctx &optional (depth 1))
  (let ((argsl (quick-ctx-fill-args ctx htp depth nil)))
    (mapcar #'(lambda (args) (app-n h args)) argsl)))

(defun quick-ctx-forward (usable ctx &optional (depth 1))
  (let ((ret nil))
    (dolist (u usable)
      (if (consp u)
	  (setq ret (append (quick-ctx-instances (car u) (cdr u) ctx depth)
			    ret))
	(setq ret (append (quick-ctx-instances u (get u 'dbtype) ctx depth)
			  ret))))
    (dotimes (i (length ctx))
      (let ((tp (ctx-extract-type ctx i)))
	(setq ret (append (quick-ctx-instances i tp ctx depth)
			  ret))))
    ret))

; this is hopefully not exponential (though that's far from clear - even doubtful),
; but still includes eta expansions of vars
(defun quick-ordered-ctx-fill (ctx tp &optional (depth 1) (justone t) (ub nil) (reorderbd 0))
  (if (dpi-p tp)
      (let ((trml (quick-ordered-ctx-fill (ctx-cons (dpi-dom tp) ctx) (dpi-cod tp) depth justone
					  (if ub (1+ ub) nil)
					  reorderbd)))
	(mapcar #'(lambda (trm)
		    (lam trm))
		trml))
    (let ((trml nil)
	  (ctx2 nil))
      (when (pf-p tp)
	(setq justone t))
      (do ((ctx2 ctx (cdr ctx2))
	   (i 0 (1+ i)))
	  ((or (and trml justone) (null ctx2) (and ub (>= i (+ reorderbd ub))))
	   trml)
	  (if (dpi-p (car ctx2))
	      (when (> depth 0)
		(let ((argsl (quick-ordered-ctx-fill-args ctx 
							  (dbshift-type-n (1+ i) (car ctx2))
							  (- depth 1) justone i reorderbd)))
		  (do ((argsl2 argsl (cdr argsl2)))
		      ((or (and trml justone) (null argsl2)))
		      (let ((z (app-n i (car argsl2))))
			(when (ctx-term-type-p ctx z tp)
			  (push z trml))))))
	    (when (ctx-term-type-p ctx i tp)
	      (push i trml)))))))

(defun quick-ordered-ctx-fill-args (ctx tp &optional (depth 1) (justone t) (ub nil) (reorderbd 0))
  (if (dpi-p tp)
      (let ((arg1l (quick-ordered-ctx-fill ctx (dpi-dom tp) depth
					   (if (dpi-p (dpi-cod tp))
					       nil
					     justone)
					   ub
					   reorderbd))
	    (argsl nil))
	(do ((arg1l2 arg1l (cdr arg1l2)))
	    ((or (and argsl justone) (null arg1l2))
	     argsl)
	    (let* ((arg1 (car arg1l2))
		   (tp2 (dbsubst-type-0 (dpi-cod tp) arg1))
		   (argsl2 (quick-ordered-ctx-fill-args ctx tp2 depth justone
							(lam-app-head arg1)
							reorderbd)))
	      (setq argsl
		    (append argsl
			    (mapcar #'(lambda (args2)
					(cons arg1 args2)
					)
				    argsl2))))))
    (list nil)))

; if h is an extraction, then the values returned are extractions
; otherwise, the values may not be normal
(defun quick-ordered-ctx-instances (h htp ctx &optional (depth 1) (reorderbd 0))
  (let ((argsl (quick-ordered-ctx-fill-args ctx htp depth nil nil reorderbd)))
    (mapcar #'(lambda (args) (app-n h args)) argsl)))

; check if a type is the type of something in ctx, 'up to eta'
; should be linear in size of ctx + number of pi's on tp
(defun quick-eta-ctx-instances (ctx tp &optional (justone t))
  (if (dpi-p tp)
      (mapcar #'(lambda (trm)
		  (lam trm))
	      (quick-eta-ctx-instances (ctx-cons (dpi-dom tp) ctx) (dpi-cod tp)))
    (let ((trml nil)
	  (ctx2 nil))
      (when (pf-p tp)
	(setq justone t))
      (do ((ctx2 ctx (cdr ctx2))
	   (i 0 (1+ i)))
	  ((or (and trml justone) (null ctx2))
	   trml)
	  (let ((trm (quick-eta-ctx-instances-1 ctx
						(dbshift-type-n (1+ i) (car ctx2))
						i
						tp)))
	    (when trm
	      (push trm trml)))))))

(defun quick-eta-ctx-instances-1 (ctx ctp trm atp)
  (multiple-value-bind
   (cctx catp)
   (dtp-argctx ctp)
   (let ((n (length cctx)))
     (dotimes (i (length cctx))
       (decf n)
       (setq trm (app trm n)))
     (if (ctx-term-type-p ctx trm atp)
	 trm
       (if (and (obj-p atp) (ctx-term-type-p ctx (fst trm) atp))
	   (fst trm)
	 (if (and (pf-p atp) (ctx-term-type-p ctx (snd trm) atp))
	     (snd trm)
	   nil))))))

(defun quick-eta-ctx-pair-instances (ctx tp)
  (if (dpi-p tp)
      (mapcar #'(lambda (trm)
		  (lam trm))
	      (quick-eta-ctx-pair-instances (ctx-cons (dpi-dom tp) ctx) (dpi-cod tp)))
    (quick-eta-ctx-pair-instances-0 ctx (dclass-pred tp))))

(defun quick-eta-ctx-pair-instances-0 (ctx pred)
  (let ((trml nil)
	(ctx2 nil))
    (do ((ctx2 ctx (cdr ctx2))
	 (i 0 (1+ i)))
	((null ctx2)
	 trml)
	(when (pf-p (car ctx2))
	  (let* ((ctp (dbshift-type-n (1+ i) (car ctx2)))
		 (trml2 (quick-eta-ctx-pair-instances-1
			 ctx ctp (cdr ctx2) i
			 pred (pf-prop ctp))))
	    (setq trml (append trml2 trml)))))))

(defun quick-eta-ctx-pair-instances-1 (ctx ctp ctx2 i pred prop &optional (justone t))
  (let ((trml nil))
    (do ((ctx3 ctx2 (cdr ctx3))
	 (j (1+ i) (1+ j)))
	((or (null ctx3)) trml)
	(if (obj-p (car ctx3))
	    (when (ctx-terms-eq-type ctx (normalize (app pred j)) prop (prop))
	      (push (pair j i) trml))
	  (when (and (dclass-p (car ctx3))
		     (ctx-terms-eq-type ctx (normalize (app pred (fst j))) prop (prop)))
	    (push (pair (fst j) i) trml))))))

; now back to something that uses evars...
(defun quick-fill-gap (ctx tp usable &optional (justone t) (newgaps 0) (hence nil))
  (case *quick-fill-gap-method*
	(B (if (and justone (= newgaps 0))
	       (let ((pftrm (quick-fill-gap-B ctx tp usable)))
		 (list (list pftrm)))
	     (quick-fill-gap-A ctx tp usable justone newgaps hence)))
	(t (quick-fill-gap-A ctx tp usable justone newgaps hence))))

(defun quick-fill-gap-A (ctx tp usable &optional (justone t) (newgaps 0) (hence nil))
  (if (dpi-p tp)
;      (mapcar #'(lambda (a)
;		  (cons (lam (car a)) (cdr a)))
      (quick-fill-gap-A (ctx-cons (dpi-dom tp) ctx) (dpi-cod tp) usable justone newgaps hence)
;	      )
    (let ((done (if (and *quick-fill-gap-special-cases* (= newgaps 0) justone)
		    (quick-fill-gap-special-cases ctx tp)
		  nil)))
      (if done
	  done
	(progn
	  (if (and *quick-fill-gap-simplify* (= newgaps 0))
	      (quick-fill-gap-simplify ctx tp usable justone newgaps hence *quick-fill-gap-simplify*)
	    (quick-fill-gap-atom-f ctx tp usable justone newgaps hence)))))))

; do some basic logical decomposition (just and/or for now)
(defun quick-fill-gap-simplify (ctx tp usable justone newgaps hence simpdepth)
  (if (> simpdepth 0)
      (if (pf-p tp)
	  (let ((C (pf-prop tp)))
	  (if (and (app-p C) (app-p (app-func C)))
	    (let* ((A (app-arg (app-func C)))
		   (B (app-arg C))
		   (or-in-ctx nil))
	      (do ((ctx9 ctx (cdr ctx9))
		   (k 0 (1+ k)))
		  ((or or-in-ctx (null ctx9)))
		  (when (and (pf-p (car ctx9))
			     (eq (term-extr-head (pf-prop (car ctx9))) '|or|)
			     (not (member-ctx (pf (dbshift-n (1+ k) (app-arg (app-func (pf-prop (car ctx9)))))) ctx))
			     (not (member-ctx (pf (dbshift-n (1+ k) (app-arg (pf-prop (car ctx9))))) ctx)))
		    (setq or-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
;		     (format t "or-in-ctx = ~d~%" or-in-ctx) ; delete me
	      (if or-in-ctx
		  (let* ((k (car or-in-ctx))
			 (disjtp (cdr or-in-ctx))
			 (disj (pf-prop disjtp))
			 (disjl (app-arg (app-func disj)))
			 (disjr (app-arg disj))
			 (C1 (dbshift-n 1 C))
			 (Cpf1 (quick-fill-gap-simplify (ctx-cons (pf disjl) ctx) (pf C1) usable justone newgaps nil (- simpdepth 1))))
		    (if Cpf1
			(let ((Cpftrm1 (normalize (app-n-1-to-0 (1+ (length ctx)) (caar Cpf1)))))
			  (if (nintrm-p 0 Cpftrm1)
			      (let* ((Cpf2 (quick-fill-gap-simplify (ctx-cons (pf disjr) ctx) (pf C1) usable justone newgaps nil (- simpdepth 1))))
				(if Cpf2
				    (let ((Cpftrm2 (normalize (app-n-1-to-0 (1+ (length ctx)) (caar Cpf2)))))
				      (if (nintrm-p 0 Cpftrm2)
					  (list
					   (list
					    (normalize
					     (lam-ctx ctx
						      (app-n '|orE|
							     (list disjl disjr
								   k
								   C
								   (lam Cpftrm1)
								   (lam Cpftrm2)))))
					    nil))
					(list (list (lam-ctx ctx (dbshift-n -1 Cpftrm2))
						    nil))))
				  (quick-fill-gap-atom-f ctx tp usable justone newgaps hence)))
			    (list (list (lam-ctx ctx (dbshift-n -1 Cpftrm1))
					nil))))
		      (quick-fill-gap-atom-f ctx tp usable justone newgaps hence)))
		(cond ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|and|))
		   (let* ((A (app-arg (app-func C)))
			  (B (app-arg C))
			  (Apf (quick-fill-gap-simplify ctx (pf A) usable justone newgaps nil (- simpdepth 1))))  ; forget hence
		     (if Apf
			 (let ((Bpf (quick-fill-gap-simplify ctx (pf B) usable justone newgaps nil (- simpdepth 1)))) ; forget hence
			   (if Bpf
			       (list
				(list
				 (normalize
				  (lam-ctx ctx
					   (app-n '|andI|
						  (list A B
							(app-n-1-to-0 (length ctx) (caar Apf))
							(app-n-1-to-0 (length ctx) (caar Bpf))))))
				 nil))
			     (quick-fill-gap-atom-f ctx tp usable justone newgaps hence)))
		       (quick-fill-gap-atom-f ctx tp usable justone newgaps hence))))
		  ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|or|))
		   (let ((Apf (quick-fill-gap-simplify ctx (pf A) usable justone newgaps nil (- simpdepth 1))))
		     (if Apf
			 (list (list
				(normalize
				 (lam-ctx ctx (app-n '|orIL| (list A B (app-n-1-to-0 (length ctx) (caar Apf))))))
				nil))
		       (let ((Bpf (quick-fill-gap-simplify ctx (pf B) usable justone newgaps nil (- simpdepth 1))))
			 (if Bpf
			     (list
			      (list
			       (normalize
				(lam-ctx ctx
					 (app-n '|orIR|
						(list A B
						      (app-n-1-to-0 (length ctx) (caar Bpf))))))
			       nil))
			   (quick-fill-gap-atom-f ctx tp usable justone newgaps hence))))))
		  (t (quick-fill-gap-atom-f ctx tp usable justone newgaps hence)))))
	    (quick-fill-gap-atom-f ctx tp usable justone newgaps hence)))
	nil)
    (quick-fill-gap-atom-f ctx tp usable justone newgaps hence)))

(defun quick-fill-gap-atom-f (ctx tp usable &optional (justone t) (newgaps 0) (hence nil))
  (when (= newgaps 0) (setq usable (filter-usable-for-gap ctx tp usable)))
  (quick-fill-gap-atom ctx tp usable justone newgaps hence))

(defun quick-fill-gap-atom (ctx tp usable &optional (justone t) (newgaps 0) (hence nil))
  (let ((ret nil))
    (dotimes (i (length ctx))
      (unless (and justone ret)
	(setq ret (append (quick-fill-gap-using i (ctx-extract-type ctx i) ctx tp justone newgaps hence)
			  ret))))
    (dolist (uf *quick-fill-gap-external-agents*)
      (unless (and justone ret)
	(let ((f (funcall (caddr uf) ctx tp usable)))
	  (when (and f
		     (ctx-term-type-p nil f (dpi-ctx ctx tp)))
	    (setq ret (list (list f)))))))
    (unless *quick-fill-gap-only-external*
      (dolist (u usable)
	(unless (and justone ret)
	  (if (consp u)
	      (setq ret (append (quick-fill-gap-using (car u) (cdr u) ctx tp justone newgaps hence)
				ret))
	    (setq ret (append (quick-fill-gap-using u (get u 'dbtype) ctx tp justone newgaps hence)
			      ret))))))
    ret))

(defun quick-fill-gap-using (h htp ctx tp &optional (justone t) (newgaps 0) (hence nil))
  (let ((ret nil))
    (multiple-value-bind
     (trm1 tp1 evars1) 
     (general-term h htp ctx)
     (when (or (compatible-types-p tp1 tp) (and (dclass-p tp1) (or (pf-p tp) (obj-p tp))))
       (if (and (dclass-p tp1) (pf-p tp))
	   (progn
	     (setq tp1 (pf (normalize (app (dclass-pred tp1) (fst (app-n-1-to-0 (length ctx) trm1))))))
	     (setq trm1 (normalize (lam-ctx ctx (snd (app-n-1-to-0 (length ctx) trm1))))))
	 (when (and (dclass-p tp1) (obj-p tp))
	   (setq tp1 (obj))
	   (setq trm1 (normalize (lam-ctx ctx (fst (app-n-1-to-0 (length ctx) trm1)))))))
       (when (> *verbose* 80) (format t "Trying to fill using ~d~%" h))
       (let ((unif-states
	      (preunify-msv evars1 evars1 nil
					; dpairs
			    (cond ((and (pf-p tp1) (pf-p tp))
				   (list (list ctx (pf-prop tp) (pf-prop tp1) (prop))))
				  ((dclass-p tp)
				   (list (list ctx (dclass-pred tp) (dclass-pred tp1) *pred*)))
				  (t nil))
					; fill-constraints
			    (mapcar #'(lambda (x)
					(list nil (car x) (cdr x)))
				    evars1)
					; msv
			    *preunify-msv-goal*)))
	 (dolist (unif-state unif-states)
	   (unless (and ret justone)
	     (let* ((cevars (car unif-state))
		    (theta (cadr unif-state))
		    (dpairs (nth 2 unif-state))
		    (fill-constraints (nth 3 unif-state)))
	       (if (and hence (not (numberp h))) ; debruijns are already hences...
		   (setq ret (append 
			      (quick-fill-gap-hence ctx trm1 evars1 cevars theta dpairs fill-constraints
						    justone newgaps)
			      ret))
		 (setq ret (append 
			    (quick-fill-gap-pfevars ctx trm1 evars1 cevars theta dpairs fill-constraints
						    justone newgaps)
			    ret)))))))))
    ret))

; first try to unify some pfevar with last assumption put into ctx
(defun quick-fill-gap-hence (ctx trm1 evars1 cevars theta dpairs fill-constraints justone newgaps)
  (let ((i 0)
	(ret nil))
    (do ((ctx2 ctx (cdr ctx2)))
	((or (null ctx2) (dtype-returns-pf-p (car ctx2)))
	 (unless ctx2 (setq i nil)))
	(incf i))
    (when i
      (dolist (fc fill-constraints)
	(unless (and justone ret)
	  (let ((psi (car fc))
		(ftrm (cadr fc))
		(ftp (caddr fc))
		(j i))
	    (do ((psi2 psi (cdr psi2)))
		((or (null psi2) (equal psi2 ctx))
		 (unless psi2 (setq j nil)))
		(incf j))
	    (when (and j (pf-p ftp))
	      (multiple-value-bind
	       (projtrm projtp projevars)
	       (projection-term j psi)
	       (when (pf-p projtp) ; should always happen, but who knows
		 (when (> *verbose* 80) (format t "Trying to use ~d :: ~d for hence~%" j projtp))
		 (let* ((cevars2 (append cevars projevars))
			(unif-states
			 (preunify-msv evars1 cevars2 theta
				       (cons (list psi (pf-prop projtp) (pf-prop ftp) (prop)) dpairs)
				       (append fill-constraints
					       (mapcar #'(lambda (x)
							   (list nil (car x) (cdr x)))
						       projevars))
				       *preunify-msv-hence*)))
		   (dolist (unif-state unif-states)
		     (unless (and justone ret)
		       (let* ((cevars (car unif-state))
			      (theta (cadr unif-state))
			      (dpairs (nth 2 unif-state))
			      (fill-constraints (nth 3 unif-state)))
			 (setq ret (append 
				    (quick-fill-gap-pfevars ctx trm1 evars1 cevars theta dpairs fill-constraints
							    justone newgaps)
				    ret)))))))))))))
    ret))

(defun quick-fill-gap-pfevars (ctx trm1 evars1 cevars theta dpairs fill-constraints justone newgaps &optional (loopbd 3))
  (if (> loopbd 0)
      (let ((ret nil))
	(dolist (e cevars)
	  (unless (and justone ret)
	    (let ((x (car e))
		  (xtp (cdr e)))
	      (multiple-value-bind
	       (psi ftp)
	       (dtp-argctx xtp)
	       (when (pf-p ftp)
		 (when (and (std-declared-p '|eq| '|eqI|)
			    (app-p (pf-prop ftp))
			    (app-p (app-func (pf-prop ftp)))
			    (eq (app-func (app-func (pf-prop ftp))) '|eq|) ; special case of reflexivity premiss
			    )
		   (let* ((rpftrm (lam-ctx psi
					   (app '|eqI| (app-arg (pf-prop ftp)))))
			  (rpftp (app (app '|eq| (app-arg (pf-prop ftp))) (app-arg (pf-prop ftp))))
			  (cevars2 (mapcar #'(lambda (z)
					       (cons (car z)
						     (normalize-type (subst-type-1 x rpftrm (cdr z)))))
					   (remove x cevars :key #'car)))
			  (unif-states
			   (preunify-msv
			    evars1 cevars2
			    (compose-theta-1 x rpftrm theta)
			    (cons (list psi (pf-prop rpftp) (pf-prop ftp) (prop)) ; x cannot occur in anything in this new dpair; no need to substitute
				  (subst-1-dpairs x rpftrm dpairs))
			    (subst-1-fill-constraints x rpftrm fill-constraints)
			    *preunify-msv-supp*)))
		     (dolist (unif-state unif-states)
		       (unless (and justone ret)
			 (let* ((cevars (car unif-state))
				(theta (cadr unif-state))
				(dpairs (nth 2 unif-state))
				(fill-constraints (nth 3 unif-state)))
			   (setq ret (append 
				      (quick-fill-gap-pfevars ctx trm1 evars1 cevars theta dpairs fill-constraints
							      justone newgaps (- loopbd 1))
				      ret)))))))
		 (let ((j 0))
		   (do ((psi2 psi (cdr psi2)))
		       ((or (null psi2)
			    (and *ctx-for-premiss-bd*
				 (> j *ctx-for-premiss-bd*))))
		       (multiple-value-bind
			(projtrm projtp projevars)
			(projection-term j psi)
			(incf j)
			(when (pf-p projtp)
			  (when (> *verbose* 80) (format t "Trying to use ~d :: ~d for remaining pfevars~%" (- j 1) projtp))
			  (let* ((cevars2 (append projevars
						  (mapcar #'(lambda (z)
							      (cons (car z)
								    (normalize-type (subst-type-1 x projtrm (cdr z)))))
							  (remove x cevars :key #'car))))
				 (unif-states
				  (preunify-msv
				   evars1 cevars2
				   (compose-theta-1 x projtrm theta)
				   (cons (list psi (pf-prop projtp) (pf-prop ftp) (prop)) ; x cannot occur in anything in this new dpair; no need to substitute
					 (subst-1-dpairs x projtrm dpairs))
				   (append (subst-1-fill-constraints x projtrm fill-constraints)
					   (mapcar #'(lambda (x)
						       (list nil (car x) (cdr x)))
						   projevars))
				   *preunify-msv-supp*)))
			    (dolist (unif-state unif-states)
			      (unless (and justone ret)
				(let* ((cevars (car unif-state))
				       (theta (cadr unif-state))
				       (dpairs (nth 2 unif-state))
				       (fill-constraints (nth 3 unif-state)))
				  (setq ret (append 
					     (quick-fill-gap-pfevars ctx trm1 evars1 cevars theta dpairs fill-constraints
								     justone newgaps (- loopbd 1))
					     ret)))))))))))))))
	(if (and ret justone)
	    ret
	  (append (quick-fill-gap-final ctx trm1 evars1 cevars theta dpairs fill-constraints
					justone newgaps)
		  ret)))
    (quick-fill-gap-final ctx trm1 evars1 cevars theta dpairs fill-constraints
			  justone newgaps)))

(defun quick-fill-gap-final (ctx trm1 evars1 cevars theta dpairs fill-constraints justone newgaps &optional delayed-pfvars)
  (let ((zevars (set-difference cevars delayed-pfvars :key #'car)))
    (if zevars
	(let ((evar (find-if-not #'(lambda (ev)
				     (dtype-free-evars (cdr ev)))
				 zevars))
	      (ret nil))
	  (if evar
	      (let ((fills (quick-eta-ctx-instances *emptyctx* (cdr evar) nil)))
		(dolist (ftrm fills)
		  (unless (and ret justone)
		    (multiple-value-bind
		     (fail cevars2 theta2 dpairs2 fill-constraints2)
		     (simplify-constraints evars1 cevars theta
					   (cons (list nil (car evar) ftrm (cdr evar))
						 dpairs)
					   fill-constraints)
		     (unless fail
		       (setq ret (append ret (quick-fill-gap-final ctx trm1 evars1 cevars2 theta2
								   dpairs2 fill-constraints2
								   justone newgaps delayed-pfvars)))))))
		(when (dtype-returns-dclass-p (cdr evar))
		  (let ((pairfills (quick-eta-ctx-pair-instances *emptyctx* (cdr evar))))
		    (dolist (ftrm pairfills)
		      (unless (and ret justone)
			(multiple-value-bind
			 (fail cevars2 theta2 dpairs2 fill-constraints2)
			 (simplify-constraints evars1 cevars theta
					       (cons (list nil (car evar) ftrm (cdr evar))
						     dpairs)
					       fill-constraints)
			 (unless fail
			   (setq ret (append ret (quick-fill-gap-final ctx trm1 evars1 cevars2 theta2
								       dpairs2 fill-constraints2
								       justone newgaps delayed-pfvars)))))))))
		(when (and (> newgaps 0) (dtype-returns-pf-p (cdr evar)) (not fills))
		  (setq ret (append ret (quick-fill-gap-final ctx trm1 evars1 cevars theta
							      dpairs fill-constraints justone 
							      (- newgaps 1)
							      (cons evar delayed-pfvars)))))
		ret)
	    nil))
      (list (list (normalize (simul-subst theta trm1)) delayed-pfvars)))))

(defun unif-debug-query (evar trm)
  (format t "[y/n] Really Try ~d |-> ~d?[n]"
	  evar
	  (output1-normal-string trm nil t))
  (string-equal (read-line) "y"))

(defun quick-fill-gap-special-cases (ctx tp)
  (cond ((pf-p tp)
	 (quick-fill-gap-special-cases-pf ctx (pf-prop tp)))
	(t nil)))

; the point here is to handle some second-order things that might
; be hard for unification - especially, dallE, dexI, dsetconstrI, dsetconstrEL, dsetconstrER,
; defns and equations
(defun quick-fill-gap-special-cases-pf (ctx prop)
  (or (quick-fill-gap-special-cases-pf-inset ctx prop)
      (quick-fill-gap-special-cases-pf-ctx ctx prop)
      (quick-fill-gap-special-cases-pf-dallE ctx prop)
      (quick-fill-gap-special-cases-pf-dexI ctx prop)
      (quick-fill-gap-special-cases-pf-setenum ctx prop) ; write this
      (quick-fill-gap-special-cases-pf-dsetconstrI ctx prop)
      (quick-fill-gap-special-cases-pf-dsetconstrEL ctx prop)
      (quick-fill-gap-special-cases-pf-dsetconstrER ctx prop)
      (quick-fill-gap-special-cases-pf-defn-fold-head ctx prop)
      (quick-fill-gap-special-cases-pf-defn-unfold-head ctx prop)
      (when (and *auto-gen-congruence* (> *congruences-stage* 1))
	(quick-fill-gap-special-cases-pf-equation ctx prop))
      ))

(defun quick-fill-gap-special-cases-pf-inset (ctx prop)
  (when (and (app-p prop) (app-p (app-func prop))
	     (eq (app-func (app-func prop)) '|in|)
	     (fst-p (app-arg prop)))
    (let* ((trm (fst-arg (app-arg prop)))
	   (tp (ctx-extract-type ctx trm)))
      (when (and (dclass-p tp) (app-p (dclass-pred tp))
		 (ctx-extract-eq-type ctx (app-func prop) (dclass-pred tp)))
	(list (list (lam-ctx ctx (snd trm)) nil))))))
  
(defun quick-fill-gap-special-cases-pf-ctx (ctx prop)
  (let ((done nil)
	(n (length ctx)))
    (do ((i 0 (1+ i)))
	((or done (>= i n))
	 done)
	(let ((tpi (ctx-extract-type ctx i)))
	  (if (dclass-p tpi)
	      (when (ctx-terms-eq-type ctx (normalize (app (dclass-pred tpi) (fst i))) prop (prop))
		(setq done (list (list (lam-ctx ctx (snd i)) nil))))
	    (when (and (pf-p tpi)
		       (ctx-terms-eq-type ctx (pf-prop tpi) prop (prop)))
	      (setq done (list (list (lam-ctx ctx i) nil)))))))))
  
(defun quick-fill-gap-special-cases-pf-dallE (ctx prop)
  (let ((done nil)
	(n (length ctx)))
    (do ((i 0 (1+ i)))
	((or done (>= i n))
	 done)
	(let ((tpi (ctx-extract-type ctx i)))
	  (when (pf-p tpi)
	    (let ((propi (pf-prop tpi)))
	      (when (and (app-p propi)
			 (app-p (app-func propi))
			 (eq (app-func (app-func propi)) '|dall|))
		(let ((A (app-arg (app-func propi)))
		      (phi (app-arg propi)))
		  (do ((j 0 (1+ j))) ; look for a member of A, or a pf that something is in A
		      ((or done (>= j n)))
		      (let ((tpj (ctx-extract-type ctx j)))
			(if (dclass-p tpj)
			    (when (and (app-p (dclass-pred tpj))
				       (eq (app-func (dclass-pred tpj)) '|in|)
				       (ctx-terms-eq-type ctx (app-arg (dclass-pred tpj)) A (obj))
				       (ctx-terms-eq-type ctx (normalize (app phi j)) prop (prop)))
			      (setq done
				    (list (list (lam-ctx ctx
							 (app-n '|dallE|
								(list A phi i j)))
						nil))))
			  (when (and (pf-p tpj)
				     (app-p (pf-prop tpj))
				     (app-p (app-func (pf-prop tpj)))
				     (eq (app-func (app-func (pf-prop tpj))) '|in|)
				     (ctx-terms-eq-type ctx
							(app-arg (app-func (pf-prop tpj)))
							A (obj))
				     (ctx-terms-eq-type ctx (normalize (app phi 
									    (pair (app-arg (pf-prop tpj))
										  j)))
							prop (prop)))
			    (setq done
				  (list (list (lam-ctx ctx
						       (app-n '|dallE|
							      (list A phi i
								    (pair (app-arg (pf-prop tpj))
									  j))))
					      nil)))))))))))))))

(defun quick-fill-gap-special-cases-pf-dexI (ctx prop)
  (when (and (app-p prop)
	     (app-p (app-func prop))
	     (eq (app-func (app-func prop)) '|dex|))
    (let ((done nil)
	  (n (length ctx))
	  (A (app-arg (app-func prop)))
	  (phi (app-arg prop)))
      (do ((j 0 (1+ j)))
	  ((or done (>= j n))
	   done)
	  (let ((tpj (ctx-extract-type ctx j)))
	    (if (dclass-p tpj)
		(when (and (app-p (dclass-pred tpj))
			   (eq (app-func (dclass-pred tpj)) '|in|)
			   (ctx-terms-eq-type ctx (app-arg (dclass-pred tpj)) A (obj)))
		  (let ((phij (normalize (app phi j))))
		    (do ((i 0 (1+ i)))
			((or done (>= i n)))
			(let ((tpi (ctx-extract-type ctx i)))
			  (when (and (pf-p tpi)
				     (ctx-terms-eq-type ctx (pf-prop tpi) phij (prop)))
			    (setq done
				  (list (list (lam-ctx ctx
						       (app-n '|dexI|
							      (list A phi j i)))
					      nil))))))))
	      (when (and (pf-p tpj)
			 (app-p (pf-prop tpj))
			 (app-p (app-func (pf-prop tpj)))
			 (eq (app-func (app-func (pf-prop tpj))) '|in|)
			 (ctx-terms-eq-type ctx
					    (app-arg (app-func (pf-prop tpj)))
					    A (obj)))
		(let* ((jp (pair (app-arg (pf-prop tpj)) j))
		       (phij (normalize (app phi jp))))
		  (do ((i 0 (1+ i)))
		      ((or done (>= i n)))
		      (let ((tpi (ctx-extract-type ctx i)))
			(when (and (pf-p tpi)
				   (ctx-terms-eq-type ctx (pf-prop tpi) phij (prop)))
			  (setq done
				(list (list (lam-ctx ctx
						     (app-n '|dexI|
							    (list A phi jp i)))
					    nil))))))))))))))

(defun quick-fill-gap-special-cases-pf-setenum (ctx prop)
  (when (and (app-p prop)
	     (app-p (app-func prop))
	     (eq (app-func (app-func prop)) '|in|))
    (let ((r (quick-fill-gap-special-cases-pf-setenum-1 ctx (app-arg prop) (app-arg (app-func prop)))))
	   
      (if r
	  (list (list (lam-ctx ctx r)))
	nil))))

(defun quick-fill-gap-special-cases-pf-setenum-1 (ctx x enumset)
  (when (and (app-p enumset) (app-p (app-func enumset))
	     (eq (app-func (app-func enumset))
		 '|setadjoin|))
    (if (ctx-terms-eq-type ctx
			   x
			   (app-arg (app-func enumset))
			   (obj))
	(app-l '|setadjoinIL|
	       x
	       (app-arg enumset))
      (let ((r (quick-fill-gap-special-cases-pf-setenum-1
		ctx x (app-arg enumset))))
	(if r
	    (app-l '|setadjoinIR|
		   (app-arg (app-func enumset))
		   (app-arg enumset)
		   x
		   r)
	  nil)))))

; like dexI, find a pattern for this...
(defun quick-fill-gap-special-cases-pf-dsetconstrI (ctx prop)
  (when (and (app-p prop)
	     (app-p (app-func prop))
	     (eq (app-func (app-func prop)) '|in|)
	     (app-p (app-arg (app-func prop)))
	     (app-p (app-func (app-arg (app-func prop))))
	     (eq (app-func (app-func (app-arg (app-func prop))))
		 '|dsetconstr|))
    (let ((done nil)
	  (n (length ctx))
	  (x (app-arg prop))
	  (A (app-arg (app-func (app-arg (app-func prop)))))
	  (phi (app-arg (app-arg (app-func prop)))))
      (do ((j 0 (1+ j)))
	  ((or done (>= j n))
	   done)
	  (let ((tpj (ctx-extract-type ctx j)))
	    (if (dclass-p tpj)
		(when (and (app-p (dclass-pred tpj))
			   (eq (app-func (dclass-pred tpj)) '|in|)
			   (ctx-terms-eq-type ctx (app-arg (dclass-pred tpj)) A (obj))
			   (ctx-terms-eq-type ctx x (fst j) (obj)))
		  (let ((phij (normalize (app phi j))))
		    (do ((i 0 (1+ i)))
			((or done (>= i n)))
			(let ((tpi (ctx-extract-type ctx i)))
			  (when (and (pf-p tpi)
				     (ctx-terms-eq-type ctx (pf-prop tpi) phij (prop)))
			    (setq done
				  (list (list (lam-ctx ctx
						       (app-n '|dsetconstrI|
							      (list A phi j i)))
					      nil))))))))
	      (when (and (pf-p tpj)
			 (app-p (pf-prop tpj))
			 (app-p (app-func (pf-prop tpj)))
			 (eq (app-func (app-func (pf-prop tpj))) '|in|)
			 (ctx-terms-eq-type ctx
					    (app-arg (app-func (pf-prop tpj)))
					    A (obj))
			 (ctx-terms-eq-type ctx x
					    (app-arg (pf-prop tpj))
					    (obj))
			 )
		(let* ((jp (pair x j))
		       (phij (normalize (app phi jp))))
		  (do ((i 0 (1+ i)))
		      ((or done (>= i n)))
		      (let ((tpi (ctx-extract-type ctx i)))
			(when (and (pf-p tpi)
				   (ctx-terms-eq-type ctx (pf-prop tpi) phij (prop)))
			  (setq done
				(list (list (lam-ctx ctx
						     (app-n '|dsetconstrI|
							    (list A phi jp i)))
					    nil))))))))))))))

; the phi really doesn't matter here - different sort of pattern to identify - essentially fo
(defun quick-fill-gap-special-cases-pf-dsetconstrEL (ctx prop)
  (when (and (app-p prop)
	     (app-p (app-func prop))
	     (eq (app-func (app-func prop)) '|in|))
    (let ((done nil)
	  (n (length ctx))
	  (x (app-arg prop))
	  (A (app-arg (app-func prop))))
      (do ((i 0 (1+ i)))
	  ((or done (>= i n))
	   done)
	  (let ((tpi (ctx-extract-type ctx i)))
	    (when (pf-p tpi)
	      (let ((propi (pf-prop tpi)))
		(when (and (app-p propi)
			   (app-p (app-func propi))
			   (eq (app-func (app-func propi)) '|in|)
			   (app-p (app-arg (app-func propi)))
			   (app-p (app-func (app-arg (app-func propi))))
			   (eq (app-func (app-func (app-arg (app-func propi)))) '|dsetconstr|)
			   (ctx-terms-eq-type ctx x (app-arg propi) (obj))
			   (ctx-terms-eq-type ctx A
					      (app-arg (app-func (app-arg (app-func propi))))
					      (obj)))
		  (let ((phi (app-arg (app-arg (app-func propi)))))
		    (setq done
			  (list (list (lam-ctx ctx
					       (app-n '|dsetconstrEL|
						      (list A phi x i)))
				      nil))))))))))))

; like dallE, find a pattern
(defun quick-fill-gap-special-cases-pf-dsetconstrER (ctx prop)
  (let ((done nil)
	(n (length ctx)))
    (do ((i 0 (1+ i)))
	((or done (>= i n))
	 done)
	(let ((tpi (ctx-extract-type ctx i)))
	  (when (pf-p tpi)
	    (let ((propi (pf-prop tpi)))
	      (when (and (app-p propi)
			 (app-p (app-func propi))
			 (eq (app-func (app-func propi)) '|in|)
			 (app-p (app-arg (app-func propi)))
			 (app-p (app-func (app-arg (app-func propi))))
			 (eq (app-func (app-func (app-arg (app-func propi)))) '|dsetconstr|))
		(let* ((x (app-arg propi))
		       (A (app-arg (app-func (app-arg (app-func propi)))))
		       (phi (app-arg (app-arg (app-func propi))))
		       (phix (normalize (app phi
					     (pair x
						   (app-n '|dsetconstrEL|
							  (list A phi x i)))))))
		  (when (ctx-terms-eq-type ctx phix prop (prop))
		    (setq done
			  (list (list (lam-ctx ctx
					       (app-n '|dsetconstrER|
						      (list A phi x i)))
				      nil))))))))))))

(defun quick-fill-gap-special-cases-pf-defn-fold-head (ctx prop)
  (let* ((name (term-extr-head prop)))
    (when (and (symbolp name) (abbrevname-p name))
      (let* ((args (term-extr-args prop))
	     (e1 (app-n (intern (format nil "~d#F" name)) args))
	     (e1tp (ctx-extract-type ctx e1)))
	(when (and e1tp (dpi-p e1tp)
		   (pf-p (dpi-dom e1tp)))
	  (let ((uprop (pf-prop (dpi-dom e1tp)))
		(n (length ctx))
		(done nil))
	    (do ((j 0 (1+ j)))
		((or done (>= j n)) done)
		(let ((ctp (ctx-extract-type ctx j)))
		  (when (and (pf-p ctp) (ctx-terms-eq-type ctx (pf-prop ctp) uprop (prop)))
		    (setq done 
			  (list (list (lam-ctx ctx (app e1 j))
				      nil))))))))))))

(defun quick-fill-gap-special-cases-pf-defn-unfold-head (ctx prop)
  (let ((done nil)
	(n (length ctx)))
    (do ((j 0 (1+ j)))
	((or done (>= j n)) done)
	(let ((ctp (ctx-extract-type ctx j)))
	  (when (and (pf-p ctp)
		     (symbolp (term-extr-head (pf-prop ctp)))
		     (abbrevname-p (term-extr-head (pf-prop ctp))))
	    (let* ((cprop (pf-prop ctp))
		   (name (term-extr-head cprop))
		   (args (term-extr-args cprop))
		   (h (intern (format nil "~d#U" name)))
		   (e (app (app-n h args) j))
		   (etp (ctx-extract-type ctx e)))
	      (when (and etp (pf-p etp)
			 (ctx-terms-eq-type ctx (pf-prop etp) prop (prop)))
		(setq done (list (list (lam-ctx ctx e) nil))))))))))

(defun quick-fill-gap-special-cases-pf-equation (ctx prop)
  (let ((done nil)
	(n (length ctx))
	(eqns nil)
	(equivs nil))
    (do ((j 0 (1+ j)))
	((or done (>= j n))
	 done)
	(let ((tpj (ctx-extract-type ctx j)))
	  (when (and (pf-p tpj)
		     (app-p (pf-prop tpj))
		     (app-p (app-func (pf-prop tpj))))
	    (cond ((eq (app-func (app-func (pf-prop tpj))) '|eq|)
		   (push (list j (app-arg (app-func (pf-prop tpj))) (app-arg (pf-prop tpj))) eqns))
		  ((eq (app-func (app-func (pf-prop tpj))) '|equiv|)
		   (push (list j (app-arg (app-func (pf-prop tpj))) (app-arg (pf-prop tpj))) equivs))))))
    (when (and (app-p prop) (app-p (app-func prop)))
      (cond ((eq (app-func (app-func prop)) '|eq|)
	     (let ((eqpf (congruence-make-equation-pf ctx (app-arg (app-func prop)) (app-arg prop) (obj) eqns equivs)))
	       (when eqpf
		 (setq done (list (list (lam-ctx ctx eqpf) nil))))))
	    ((eq (app-func (app-func prop)) '|equiv|)
	     (let ((eqpf (congruence-make-equation-pf ctx (app-arg (app-func prop)) (app-arg prop) (prop) eqns equivs)))
	       (when eqpf
		 (setq done (list (list (lam-ctx ctx eqpf) nil))))))))
    (or done
	(do ((j 0 (1+ j)))
	    ((or done (>= j n))
	     done)
	    (let ((tpj (ctx-extract-type ctx j)))
	      (when (pf-p tpj)
		(let* ((propj (pf-prop tpj))
		       (equivpf (congruence-make-equation-pf
				 ctx propj prop (prop) eqns equivs)))
		  (when equivpf
		    (setq done (list (list (lam-ctx ctx
						    (app-n '|equivEimp1|
							   (list propj prop equivpf j)))
					   nil)))))))))))

(defun filter-usable-for-gap (ctx tp usable)
  (if *filter-usable-for-gap*
      (if (pf-p tp)
	  (let ((aprems (abstract-prems ctx))
		(aconc (abstract-trm (pf-prop tp)))
		(r (list nil))
		)
	    (dolist (c usable (cdr r))
	      (when (and (sigelt-prooflike-p c)
			 (match-aprems (sigelt-aprems c) aprems)
			 (match-atrm (sigelt-aconc c) aconc))
		(nconc r (list c))))
	    )
	nil)
    usable))

(defun sigelt-prooflike-p (c)
  (if (get c 'prooflike)
      (cdr (get c 'prooflike))
    (let ((p (or (dtype-returns-pf-p (get c 'dbtype))
		 (dtype-returns-dclass-p (get c 'dbtype)))))
      (setf (get c 'prooflike) (cons t p))
      p)))

(defun sigelt-aprems (c)
  (if (get c 'aprems)
      (cdr (get c 'aprems))
    (progn
      (compute-sigelt-aconc-aprems c)
      (cdr (get c 'aprems)))))

(defun sigelt-aconc (c)
  (if (get c 'aconc)
      (get c 'aconc)
    (progn
      (compute-sigelt-aconc-aprems c)
      (get c 'aconc))))

(defun compute-sigelt-aconc-aprems (c)
  (do ((ctx nil (ctx-cons (dpi-dom tp) ctx))
       (tp (get c 'dbtype) (dpi-cod tp)))
      ((null (dpi-p tp))
       (cond ((pf-p tp)
	      (let ((aprems (abstract-prems ctx))
		    (aconc (abstract-trm (pf-prop tp))))
		(setf (get c 'aprems) (cons t aprems))
		(setf (get c 'aconc) aconc)
		))
	     ((dclass-p tp)
	      (let ((aprems (abstract-prems ctx))
		    (aconc (abstract-trm
			    (normalize (app (dclass-pred tp)
					    (fst (app-n-1-to-0 (length ctx) c)))))))
		(setf (get c 'aprems) (cons t aprems))
		(setf (get c 'aconc) aconc)
		))
	     (t
	      (setf (get c 'prooflike) (cons t nil))
	      (setf (get c 'aprems) (cons t nil))
	      nil)))))

(defun unif-atrm (a1 a2)
  (if (or (eq a1 '*) (eq a2 '*))
      t
    (if (and (consp a1) (consp a2) (eq (car a1) (car a2)))
	(unif-atrm (cdr a1) (cdr a2))
      nil)))

(defun match-atrm (a1 a2)
  (if (eq a1 '*)
      t
    (if (and (consp a1) (consp a2) (eq (car a1) (car a2)))
	(match-atrm (cdr a1) (cdr a2))
      nil)))

(defun match-aprem (ap al1 al2)
  (or (find-if #'(lambda (y) (unif-atrm y ap)) al1)
      (find-if #'(lambda (y) (match-atrm ap (car y))) al2))) ; might want to refine this

(defun match-aprems (al1 al2)
  (if al1
      (if (match-aprem (caar al1) (cdar al1) al2)
	  (match-aprems (cdr al1) al2)
	nil)
    t))

(defun abstract-prems (ctx)
  (if ctx
      (let ((p (abstract-prem (car ctx))))
	(if p
	    (cons p
		  (abstract-prems (cdr ctx)))
	  (abstract-prems (cdr ctx))))
    nil))

(defun abstract-prem (tp &optional ahyps)
  (if (dpi-p tp)
      (let ((dom (dpi-dom tp)))
	(if (pf-p dom)
	    (abstract-prem (dpi-cod tp)
			   (cons (abstract-trm (pf-prop dom)) ahyps))
	  (if (dclass-p dom)
	      (abstract-prem (dpi-cod tp)
			     (cons (abstract-trm
				    (normalize
				     (app
				      (dclass-pred dom)
				      (fst 0))))
				   ahyps))
	    (abstract-prem (dpi-cod tp)
			   ahyps))))
    (if (pf-p tp)
	(cons (abstract-trm (pf-prop tp)) ahyps)
      nil)))

(defun abstract-trm (trm)
  (let ((h (term-head trm)))
    (if (numberp h)
	'*
      (if (member h '(|not| |in| |eq|))
	  (cons h (abstract-trm (term-arg1 trm)))
	(let ((a (term-arg1 trm)))
	  (if a
	      (cons h (abstract-trm-1 a))
	    (list h)))))))

(defun abstract-trm-1 (trm)
  (let ((h (term-head trm)))
    (if (numberp h)
	'*
      (list h))))
	  
(defun quick-fill-gap-B (ctx tp usable)
  (if (dpi-p tp)
      (quick-fill-gap-B (ctx-cons (dpi-dom tp) ctx) (dpi-cod tp) usable)
    (if (pf-p tp)
	(quick-fill-gap-B-pf ctx (pf-prop tp) usable)
      nil)))

(defun quick-fill-gap-B-pf (ctx prop usable)
  (let ((ret nil))
    (if ret
	ret
    (if (and (std-declared-p '|eq| '|eqI|)
	     (app-p prop)
	     (app-p (app-func prop))
	     (eq (app-func (app-func prop)) '|eq|)
	     (ctx-terms-eq-type ctx (app-arg (app-func prop)) (app-arg prop) (prop)))
	(lam-ctx ctx (app '|eqI| (app-arg prop)))
      (let ((ret (quick-eta-ctx-instances ctx (pf prop))))
	(if ret
	    (lam-ctx ctx (car ret))
	  (progn
	    (do ((i 0 (1+ i)))
		((or ret (>= i (length ctx))
		     (and *ctx-for-premiss-bd*
			  (>= i *ctx-for-premiss-bd*))))
		(setq ret (quick-fill-gap-B-using ctx prop i (ctx-extract-type ctx i))))
	    (setq usable (filter-usable-for-gap ctx (pf prop) usable))
	    (dolist (uf *quick-fill-gap-external-agents*)
	      (unless ret
		(let ((f (funcall (caddr uf) ctx tp usable)))
		  (when (and f
			     (ctx-term-type-p nil f (dpi-ctx ctx tp)))
		    (setq ret f)))))
	    (if ret
		ret
	      (unless *quick-fill-gap-only-external*
		(do ((u usable (cdr u)))
		    ((or ret (null u)) ret)
		    (if (consp (car u))
			(setq ret (quick-fill-gap-B-using ctx prop (caar u) (cdar u)))
		      (setq ret (quick-fill-gap-B-using ctx prop (car u) (get (car u) 'dbtype))))))))))))))

(defun quick-fill-gap-B-using (ctx prop trm tp)
  (let ((cl
	 (simplify-clause
	  (pftrm-to-clause ctx prop trm tp))))
    (if cl
	(quick-fill-gap-B-pfvars cl ctx)
      nil)))

(defun quick-fill-gap-B-pfvars (cl ctx)
  (let ((pfvars (nth 3 cl)))
    (if pfvars
	(let* ((pfvar (car pfvars))
	       (pfvartp (get pfvar 'dbtype))
	       (ret nil))
	  (when (std-declared-p '|eq| '|eqI|)
	    (multiple-value-bind
	     (imtrm imevars impfvars)
	     (imitation-term-pf-B '|eqI| (dtp-argctx pfvartp)) ; no new pfvars here
	     (let ((cl2 (simplify-clause (clause-subst pfvar imtrm cl))))
	       (when cl2
		 (setq ret (quick-fill-gap-B-pfvars cl2 ctx))))))
	  (if ret
	      ret
	    (do ((i 0 (1+ i)))
		((or ret (>= i (length ctx))
		     (and *ctx-for-premiss-bd*
			  (>= i *ctx-for-premiss-bd*))))
		(when (or (dtype-returns-pf-p (nth i ctx))
			  (dtype-returns-dclass-p (nth i ctx)))
		  (multiple-value-bind
		   (prtrm prevars prpfvars)
		   (projection-term-pf-B i (dtp-argctx pfvartp)) ; any new pfvars must be msv 0
		   (when (or (null prpfvars) (not (equal (get pfvar 'msv) 0)))
		     (dolist (x prpfvars)
		       (setf (get x 'msv) 0))
		     (let ((cl2 (simplify-clause (clause-subst pfvar prtrm cl))))
		       (when cl2
			 (setq ret (quick-fill-gap-B-pfvars cl2 ctx))))))))))
      (if (or (nth 2 cl) (nth 4 cl)) ; left over evars or dpairs (should be enough to check evars) -- fail! should this ever happen? it could if some rule has extraneous object dependencies -- should I disallow such a thing?  or I could just trivially fill them in here...(constant false or constant emptyset)
	  nil
	(lam-ctx ctx (cadr cl)))))) ; otherwise succeed

; a clause is (<ctx> <pfterm> <evars> <pfvars> <dpairs>)  [or NIL for failure]
; here a dpair is a list of (<ctx> <opentrm1> <closedtrm2> <tp>) (ie, matching)
; where we assume <ctx> | <closedtrm2> : <tp>
; and we want <ctx> | theta(<opentrm1>) = <closedtrm2> : <tp>
; <tp> should never return a proof type.
(defun simplify-clause (cl)
  (if cl
      (let ((ctx (nth 0 cl))
	    (pfterm (nth 1 cl))
	    (evars (nth 2 cl))
	    (pfvars (nth 3 cl))
	    (dpairs (nth 4 cl))
	    (done nil))
	(loop until done do
	      (let ((rrdiff (find-if #'(lambda (dp)
					 (and (not (dpi-p (cadddr dp)))
					      (not (dclass-p (cadddr dp)))
					      (not (evar-p (term-extr-head (cadr dp))))
					      (not (equal (term-extr-head (cadr dp))
							  (term-extr-head (caddr dp))))))
				     dpairs)))
		(if rrdiff
		    (setq done 'FAIL)
		  (let ((rrsame (find-if #'(lambda (dp)
					     (and (not (dpi-p (cadddr dp)))
						  (not (dclass-p (cadddr dp)))
						  (not (evar-p (term-extr-head (cadr dp))))
						  (equal (term-extr-head (cadr dp))
							 (term-extr-head (caddr dp)))))
					 dpairs)))
		    (if rrsame
			(progn
			  (setq dpairs (remove rrsame dpairs))
			  (let ((trm1i (if (fst-p (cadr rrsame))
					   (fst-arg (cadr rrsame))
					 (cadr rrsame)))
				(trm2i (if (fst-p (caddr rrsame))
					   (fst-arg (caddr rrsame))
					 (caddr rrsame))))
			    (do ((trm1 trm1i (app-func trm1))
				 (trm2 trm2i (app-func trm2)))
				((or (not (app-p trm1)) (not (app-p trm2)))
				 (unless (equal trm1 trm2) (format t "problem 1") (setq *rrsame* rrsame) (break) (setq done 'FAIL)) ; should not happen
				 )
				(let ((atp (dpi-dom (ctx-extract-type (car rrsame) (app-func trm2)))))
				  (unless (dtype-returns-pf-p atp)
				    (push (list (car rrsame) (app-arg trm1) (app-arg trm2) atp)
					  dpairs))))))
		      (let ((func (find-if #'(lambda (dp)
					       (dpi-p (cadddr dp)))
					   dpairs)))
			(if func
			    (setq dpairs
				  (cons (list (ctx-cons (dpi-dom (cadddr func)) (car func))
					      (gen-lam-body (cadr func))
					      (gen-lam-body (caddr func))
					      (dpi-cod (cadddr func)))
					(remove func dpairs)))
			  (let ((p (find-if #'(lambda (dp)
						(dclass-p (cadddr dp)))
					    dpairs)))
			    (if p
				(setq dpairs
				      (cons (list (car p)
						  (gen-pair-fst (cadr func))
						  (gen-pair-fst (caddr func))
						  (obj))
					    (remove p dpairs)))
			      (let ((frpatt (find-if #'(lambda (dp)
							 (and (not (dpi-p (cadddr dp)))
							      (not (dclass-p (cadddr dp)))
							      (evar-pattern-p (cadr dp))))
						     dpairs)))
				(if frpatt
				    (let* ((ctx2 (car frpatt))
					   (trm1 (cadr frpatt))
					   (trm2 (caddr frpatt))
					   (tp2 (cadddr frpatt))
					   (evar1 (term-extr-head trm1))
					   (h2 (term-extr-head trm2)))
				      (if (numberp h2)
					  ; project, if possible
					  (let ((i (find-frpatt-projection-num trm1 h2)))
					    (if i
						(multiple-value-bind
						 (prtrm prevars prpfvars)
						 (projection-term-B i (dtp-argctx (get evar1 'dbtype)))
						 (dolist (x evars)
						   (unless (eq x evar1)
						     (setf (get x 'dbtype)
							   (normalize-type (subst-type-1 evar1 prtrm (get x 'dbtype))))))
						 (dolist (x pfvars)
						   (setf (get x 'dbtype)
							 (normalize-type (subst-type-1 evar1 prtrm (get x 'dbtype)))))
						 (setq evars (append prevars (remove evar1 evars)))
						 (setq pfvars (append prpfvars pfvars))
						 (setq pfterm (normalize (subst-1 evar1 prtrm pfterm)))
						 (setq dpairs (mapcar #'(lambda (dp)
									  (list (car dp)
										(normalize (subst-1 evar1 prtrm (cadr dp)))
										(caddr dp)
										(cadddr dp)))
								      dpairs)))
					      (setq done 'fail))) ; no projection works
					(multiple-value-bind
					 (imtrm imevars impfvars)
					 (imitation-term-B h2 (dtp-argctx (get evar1 'dbtype)))
					 (dolist (x evars)
					   (unless (eq x evar1)
					     (setf (get x 'dbtype)
						   (normalize-type (subst-type-1 evar1 imtrm (get x 'dbtype))))))
					 (dolist (x pfvars)
					   (setf (get x 'dbtype)
						 (normalize-type (subst-type-1 evar1 imtrm (get x 'dbtype)))))
					 (setq evars (append imevars (remove evar1 evars)))
					 (setq pfvars (append impfvars pfvars))
					 (setq pfterm (normalize (subst-1 evar1 imtrm pfterm)))
					 (setq dpairs (mapcar #'(lambda (dp)
								  (list (car dp)
									(normalize (subst-1 evar1 imtrm (cadr dp)))
									(caddr dp)
									(cadddr dp)))
							      dpairs)))))
				  (setq done t))))))))))))
	(if (eq done 'FAIL)
	    nil
	  (list ctx pfterm evars pfvars dpairs)))
    nil))

(defun clause-subst (v trm cl)
  (dolist (x (nth 2 cl))
    (unless (eq x v)
      (setf (get x 'dbtype)
	    (normalize-type (subst-type-1 v trm (get x 'dbtype))))))
  (dolist (x (nth 3 cl))
    (unless (eq x v)
      (setf (get x 'dbtype)
	    (normalize-type (subst-type-1 v trm (get x 'dbtype))))))
  (list (car cl) (normalize (subst-1 v trm (cadr cl)))
	(remove v (caddr cl))
	(remove v (cadddr cl))
	(mapcar #'(lambda (dp)
		    (list (car dp)
			  (normalize (subst-1 v trm (cadr dp)))
			  (caddr dp)
			  (cadddr dp)))
		(nth 4 cl))))

; returns a generic term with h at the head, of type obj or prop (not pf or class)
; and with split evars (so it's isomorphic to the Curried versions)
(defun imitation-term-B (h ctx)
  (imitation-term-B-2 h (get h 'dbtype) ctx))

(defun imitation-term-B-2 (trm tp ctx)
  (if (dpi-p tp)
      (let ((dom (dpi-dom tp)))
	(if (dtype-returns-pf-p dom)
	    (let* ((evar1 (intern-gensym))
		  (trm1 (app-n-1-to-0 (length ctx) evar1)))
	      (setf (get evar1 'evar) t)
	      (setf (get evar1 'dbtype) (dpi-ctx ctx dom))
	      (multiple-value-bind
	       (imtrm imevars impfvars)
	       (imitation-term-B-2 (app trm trm1) (normalize-type (dbsubst-type-0 (dpi-cod tp) trm1)) ctx)
	       (values imtrm imevars (cons evar1 impfvars))))
	  (if (dtype-returns-dclass-p dom)
	      (let* ((evar1 (intern-gensym))
		    (evar2 (intern-gensym))
		    (trm1 (app-n-1-to-0 (length ctx) evar1))
		    (trm2 (app-n-1-to-0 (length ctx) evar2)))
		(setf (get evar1 'evar) t)
		(setf (get evar2 'evar) t)
		(setf (get evar1 'dbtype) (dpi-ctx ctx (obj)))
		(setf (get evar2 'dbtype) (dpi-ctx ctx (pf (normalize (app (dclass-pred dom) trm1)))))
		(multiple-value-bind
		 (imtrm imevars impfvars)
		 (imitation-term-B-2 (app trm (pair trm1 trm2)) (normalize-type (dbsubst-type-0 (dpi-cod tp) (pair trm1 trm2))) ctx)
		 (values imtrm (cons evar1 imevars) (cons evar2 impfvars))))
	    (let* ((evar1 (intern-gensym))
		  (trm1 (app-n-1-to-0 (length ctx) evar1)))
	      (setf (get evar1 'evar) t)
	      (setf (get evar1 'dbtype) (dpi-ctx ctx dom))
	      (multiple-value-bind
	       (imtrm imevars impfvars)
	       (imitation-term-B-2 (app trm trm1) (normalize-type (dbsubst-type-0 (dpi-cod tp) trm1)) ctx)
	       (values imtrm (cons evar1 imevars) impfvars))))))
    (if (dclass-p tp)
	(values (lam-ctx ctx (fst trm)) nil nil)
      (values (lam-ctx ctx trm) nil nil))))

; returns a generic term with h at the head, of type obj or prop (not pf or class)
; and with split evars (so it's isomorphic to the Curried versions)
(defun projection-term-B (h ctx)
  (projection-term-B-2 h (ctx-extract-type ctx h) ctx))

(defun projection-term-B-2 (trm tp ctx)
  (if (dpi-p tp)
      (let ((dom (dpi-dom tp)))
	(if (dtype-returns-pf-p dom)
	    (let* ((evar1 (intern-gensym))
		  (trm1 (app-n-1-to-0 (length ctx) evar1)))
	      (setf (get evar1 'evar) t)
	      (setf (get evar1 'dbtype) (dpi-ctx ctx dom))
	      (multiple-value-bind
	       (imtrm imevars impfvars)
	       (projection-term-B-2 (app trm trm1) (normalize-type (dbsubst-type-0 (dpi-cod tp) trm1)) ctx)
	       (values imtrm imevars (cons evar1 impfvars))))
	  (if (dtype-returns-dclass-p dom)
	      (let* ((evar1 (intern-gensym))
		    (evar2 (intern-gensym))
		    (trm1 (app-n-1-to-0 (length ctx) evar1))
		    (trm2 (app-n-1-to-0 (length ctx) evar2)))
		(setf (get evar1 'evar) t)
		(setf (get evar2 'evar) t)
		(setf (get evar1 'dbtype) (dpi-ctx ctx (obj)))
		(setf (get evar2 'dbtype) (dpi-ctx ctx (pf (normalize (app (dclass-pred dom) trm1)))))
		(multiple-value-bind
		 (imtrm imevars impfvars)
		 (projection-term-B-2 (app trm (pair trm1 trm2)) (normalize-type (dbsubst-type-0 (dpi-cod tp) (pair trm1 trm2))) ctx)
		 (values imtrm (cons evar1 imevars) (cons evar2 impfvars))))
	    (let* ((evar1 (intern-gensym))
		  (trm1 (app-n-1-to-0 (length ctx) evar1)))
	      (setf (get evar1 'evar) t)
	      (setf (get evar1 'dbtype) (dpi-ctx ctx dom))
	      (multiple-value-bind
	       (imtrm imevars impfvars)
	       (projection-term-B-2 (app trm trm1) (normalize-type (dbsubst-type-0 (dpi-cod tp) trm1)) ctx)
	       (values imtrm (cons evar1 imevars) impfvars))))))
    (if (dclass-p tp)
	(values (lam-ctx ctx (fst trm)) nil nil)
      (values (lam-ctx ctx trm) nil nil))))

(defun imitation-term-pf-B (h ctx)
  (imitation-term-pf-B-2 h (get h 'dbtype) ctx))

(defun imitation-term-pf-B-2 (trm tp ctx)
  (if (dpi-p tp)
      (let ((dom (dpi-dom tp)))
	(if (dtype-returns-pf-p dom)
	    (let* ((evar1 (intern-gensym))
		  (trm1 (app-n-1-to-0 (length ctx) evar1)))
	      (setf (get evar1 'evar) t)
	      (setf (get evar1 'dbtype) (dpi-ctx ctx dom))
	      (multiple-value-bind
	       (imtrm imevars impfvars)
	       (imitation-term-pf-B-2 (app trm trm1) (normalize-type (dbsubst-type-0 (dpi-cod tp) trm1)) ctx)
	       (values imtrm imevars (cons evar1 impfvars))))
	  (if (dtype-returns-dclass-p dom)
	      (let* ((evar1 (intern-gensym))
		    (evar2 (intern-gensym))
		    (trm1 (app-n-1-to-0 (length ctx) evar1))
		    (trm2 (app-n-1-to-0 (length ctx) evar2)))
		(setf (get evar1 'evar) t)
		(setf (get evar2 'evar) t)
		(setf (get evar1 'dbtype) (dpi-ctx ctx (obj)))
		(setf (get evar2 'dbtype) (dpi-ctx ctx (pf (normalize (app (dclass-pred dom) trm1)))))
		(multiple-value-bind
		 (imtrm imevars impfvars)
		 (imitation-term-pf-B-2 (app trm (pair trm1 trm2)) (normalize-type (dbsubst-type-0 (dpi-cod tp) (pair trm1 trm2))) ctx)
		 (values imtrm (cons evar1 imevars) (cons evar2 impfvars))))
	    (let* ((evar1 (intern-gensym))
		  (trm1 (app-n-1-to-0 (length ctx) evar1)))
	      (setf (get evar1 'evar) t)
	      (setf (get evar1 'dbtype) (dpi-ctx ctx dom))
	      (multiple-value-bind
	       (imtrm imevars impfvars)
	       (imitation-term-pf-B-2 (app trm trm1) (normalize-type (dbsubst-type-0 (dpi-cod tp) trm1)) ctx)
	       (values imtrm (cons evar1 imevars) impfvars))))))
    (if (dclass-p tp)
	(values (lam-ctx ctx (snd trm)) nil nil)
      (values (lam-ctx ctx trm) nil nil))))

; returns a generic term with h at the head, of type obj or prop (not pf or class)
; and with split evars (so it's isomorphic to the Curried versions)
(defun projection-term-pf-B (h ctx)
  (projection-term-pf-B-2 h (ctx-extract-type ctx h) ctx))

(defun projection-term-pf-B-2 (trm tp ctx)
  (if (dpi-p tp)
      (let ((dom (dpi-dom tp)))
	(if (dtype-returns-pf-p dom)
	    (let* ((evar1 (intern-gensym))
		  (trm1 (app-n-1-to-0 (length ctx) evar1)))
	      (setf (get evar1 'evar) t)
	      (setf (get evar1 'dbtype) (dpi-ctx ctx dom))
	      (multiple-value-bind
	       (imtrm imevars impfvars)
	       (projection-term-pf-B-2 (app trm trm1) (normalize-type (dbsubst-type-0 (dpi-cod tp) trm1)) ctx)
	       (values imtrm imevars (cons evar1 impfvars))))
	  (if (dtype-returns-dclass-p dom)
	      (let* ((evar1 (intern-gensym))
		    (evar2 (intern-gensym))
		    (trm1 (app-n-1-to-0 (length ctx) evar1))
		    (trm2 (app-n-1-to-0 (length ctx) evar2)))
		(setf (get evar1 'evar) t)
		(setf (get evar2 'evar) t)
		(setf (get evar1 'dbtype) (dpi-ctx ctx (obj)))
		(setf (get evar2 'dbtype) (dpi-ctx ctx (pf (normalize (app (dclass-pred dom) trm1)))))
		(multiple-value-bind
		 (imtrm imevars impfvars)
		 (projection-term-pf-B-2 (app trm (pair trm1 trm2)) (normalize-type (dbsubst-type-0 (dpi-cod tp) (pair trm1 trm2))) ctx)
		 (values imtrm (cons evar1 imevars) (cons evar2 impfvars))))
	    (let* ((evar1 (intern-gensym))
		  (trm1 (app-n-1-to-0 (length ctx) evar1)))
	      (setf (get evar1 'evar) t)
	      (setf (get evar1 'dbtype) (dpi-ctx ctx dom))
	      (multiple-value-bind
	       (imtrm imevars impfvars)
	       (projection-term-pf-B-2 (app trm trm1) (normalize-type (dbsubst-type-0 (dpi-cod tp) trm1)) ctx)
	       (values imtrm (cons evar1 imevars) impfvars))))))
    (if (dclass-p tp)
	(values (lam-ctx ctx (snd trm)) nil nil)
      (values (lam-ctx ctx trm) nil nil))))

(defun find-frpatt-projection-num (a j &optional (n 0))
  (cond ((fst-p a) (find-frpatt-projection-num (fst-arg a) j n))
	((snd-p a) (find-frpatt-projection-num (snd-arg a) j n))
	((app-p a)
	 (multiple-value-bind
	  (i tp)
	  (find-frpatt-projection-num (app-func a) j (1+ n))
	  (if i
	      i
	    (if tp
		(if (dpi-p tp)
		    (if (dtype-returns-pf-p (dpi-dom tp))
			(values nil (normalize-type (dbsubst-type-0 (dpi-cod tp) (app-arg a))))
		      (if (dclass-p (dpi-dom tp))
			  (let ((a1 (gen-pair-fst (app-arg a))))
			    (when (fst-p a1)
			      (setq a1 (fst-arg a1)))
			    (if (equal a1 j)
				n
			      (values nil (normalize-type (dbsubst-type-0 (dpi-cod tp) (app-arg a))))))
			(if (equal (app-arg a) j)
			    n
			  (values nil (normalize-type (dbsubst-type-0 (dpi-cod tp) (app-arg a)))))))
		  (progn (format t "problem 2") (break)))
	      nil))))
	((evar-p a) (values nil (get a 'dbtype)))
	(t nil)))

(defun evar-pattern-p (a)
  (cond ((fst-p a) (evar-pattern-p (fst-arg a)))
	((snd-p a) (evar-pattern-p (snd-arg a)))
	((app-p a)
	 (multiple-value-bind
	  (tp used)
	  (evar-pattern-p (app-func a))
	  (if tp
	      (if (dpi-p tp)
		  (if (dtype-returns-pf-p (dpi-dom tp))
		      (values (normalize-type (dbsubst-type-0 (dpi-cod tp) (app-arg a)))
			      used)
		    (if (dclass-p (dpi-dom tp))
			(let ((a1 (gen-pair-fst (app-arg a))))
			  (when (fst-p a1)
			    (setq a1 (fst-arg a1)))
			  (if (and (numberp a1)
				   (not (member a1 used :test #'equal)))
			      (values (normalize-type (dbsubst-type-0 (dpi-cod tp) (app-arg a)))
				      (cons a1 used))
			    nil))
		      (if (and (numberp (app-arg a))
			       (not (member (app-arg a) used :test #'equal)))
			  (values (normalize-type (dbsubst-type-0 (dpi-cod tp) (app-arg a)))
				  (cons (app-arg a) used))
			nil)))
		(break))
	    nil)))
	((evar-p a) (values (get a 'dbtype) nil))
	(t nil)))

(defun pftrm-to-clause (ctx prop trm tp &optional evars pfvars)
  (if (dpi-p tp)
      (multiple-value-bind
       (arg evars1 pfvars1)
       (pftrm-to-clause-arg ctx (dpi-dom tp))
       (pftrm-to-clause ctx prop (app trm arg)
			(normalize-type (dbsubst-type-0 (dpi-cod tp) arg))
			(append evars1 evars)
			(append pfvars1 pfvars)))
    (if (pf-p tp)
	(list ctx (normalize trm) evars pfvars (list (list ctx (pf-prop tp) prop (prop))))
      nil)))

(defun pftrm-to-clause-arg (ctx dom)
  (if (dpi-p dom)
      (multiple-value-bind
       (arg evars1 pfvars1)
       (pftrm-to-clause-arg (ctx-cons (dpi-dom dom) ctx) (dpi-cod dom))
       (values (lam arg) evars1 pfvars1))
    (if (pf-p dom)
	(let* ((evar1 (intern-gensym))
	       (trm1 (app-n-1-to-0 (length ctx) evar1)))
	  (setf (get evar1 'evar) t)
	  (setf (get evar1 'dbtype) (dpi-ctx ctx dom))
	  (values trm1 nil (list evar1)))
      (if (dclass-p dom)
	  (let* ((evar1 (intern-gensym))
		 (evar2 (intern-gensym))
		 (trm1 (app-n-1-to-0 (length ctx) evar1))
		 (trm2 (app-n-1-to-0 (length ctx) evar2)))
	    (setf (get evar1 'evar) t)
	    (setf (get evar2 'evar) t)
	    (setf (get evar1 'dbtype) (dpi-ctx ctx (obj)))
	    (setf (get evar2 'dbtype) (dpi-ctx ctx (pf (normalize (app (dclass-pred dom) trm1)))))
	    (values (pair trm1 trm2) (list evar1) (list evar2)))
	(let* ((evar1 (intern-gensym))
	      (trm1 (app-n-1-to-0 (length ctx) evar1)))
	  (setf (get evar1 'evar) t)
	  (setf (get evar1 'dbtype) (dpi-ctx ctx dom))
	  (values trm1 (list evar1) nil))))))

(defun remove-external-fill-gap-agent (name)
  (let ((a (assoc name *quick-fill-gap-external-agents*)))
    (when a
      (when (and (streamp (cadr a))
		 (open-stream-p (cadr a)))
	(close (cadr a)))
      (setq *quick-fill-gap-external-agents*
	    (remove a *quick-fill-gap-external-agents*)))))

(defun add-external-fill-gap-agent (name mach sock)
  (let ((s (create-socket mach sock)))
    (format s "SCUNAK-FILL~%")
    (force-output s)
    (push
     (list name
	   s
	   #'(lambda (ctx pftp usable)
	       (if (and (streamp s)
			(open-stream-p s))
		   (progn
		     (format s "~S~%" (list 'SCUNAK-FILL-REQUEST ctx pftp))
		     (force-output s)
		     (read-external-fill-gap-agent s))
		 nil)))
     *quick-fill-gap-external-agents*)))

(defun add-external-fill-gap-agent-usable (name mach sock)
  (let ((s (create-socket mach sock)))
    (format s "SCUNAK-FILL~%")
    (force-output s)
    (push
     (list name
	   s
	   #'(lambda (ctx pftp usable)
	       (if (and (streamp s)
			(open-stream-p s))
		   (progn
		     (format s "~S~%" (list 'SCUNAK-FILL-REQUEST ctx pftp (cons 'USABLE usable)))
		     (force-output s)
		     (read-external-fill-gap-agent s))
		 nil)))
     *quick-fill-gap-external-agents*)))

(defun read-external-fill-gap-agent (s)
  (do ((r (read s nil '(ANSWER NIL)) (read s nil '(ANSWER nil))))
      ((and (consp r) (eq (car r) 'ANSWER))
       (cadr r))
      (if (consp r)
	  (case (car r)
		(SIGELT
		 (let ((name (if (stringp (cadr r)) (intern (cadr r)) (cadr r))))
		   (cond ((constname-p name)
			  (format s "~S~%" (list 'CONST name (get name 'dbtype))))
			 ((abbrevname-p name)
			  (format s "~S~%" (list 'ABBREV name (get name 'dbtype) (get name 'defn))))
			 ((claimname-p name)
			  (format s "~S~%" (list 'CLAIM name (get name 'dbtype))))
			 (t
			  (format s "~S~%" (list 'UNKNOWN name))))
		   (force-output s)))
		(LISP
		 (format s "~S~%" (eval (cadr r)))
		 (force-output s))
		(t nil))
	nil)))

