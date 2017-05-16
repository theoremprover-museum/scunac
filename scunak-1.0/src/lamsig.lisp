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
; April 2006

; lambda sigma calculus, based on DHK00

; Terms  : 0 | (APP <Term> . <Term>) | (LAM . <Term>) | (PAIR <Term> . <Term>) | (FST . <Term>) | (SND . <Term>) | (SUBST <Term> . <Subst>)
; Substs : ID | UP | (PUSH <Term> . <Subst>) | (COMPOSE <Subst> . <Subst>)

; DepTypes : (DPI <DepType> <DepType>) | (DCLASS <Term>) | (PF <Term>) | OBJ | PROP | (TPSUBST <DepType> . <Subst>)

; Contexts : NIL | (<DepType> . <Context>)

; note that terms and types and contexts from dtt.lisp are terms/types/contexts here, except deBruijn other than 0

(defun trm-subst (trm subst)
  (cons 'SUBST (cons trm subst)))

(defun trm-subst-trm (trm)
  (cadr trm))

(defun trm-subst-subst (trm)
  (cddr trm))

(defun trm-subst-p (trm)
  (and (consp trm)
       (eq (car trm) 'SUBST)))

(defun tp-subst (tp subst)
  (cons 'TPSUBST (cons tp subst)))

(defun tp-subst-tp (tp)
  (cadr tp))

(defun tp-subst-subst (tp)
  (cddr tp))

(defun tp-subst-p (tp)
  (and (consp tp)
       (eq (car tp) 'TPSUBST)))

(defun subst-id ()
  'ID)

(defun subst-up ()
  'UP)

(defun subst-push (trm s)
  (cons 'PUSH (cons trm s)))

(defun subst-push-trm (s)
  (cadr s))

(defun subst-push-subst (s)
  (cddr s))

(defun subst-compose (s s2)
  (cons 'COMPOSE (cons s s2)))

(defun subst-compose-fst (s)
  (cadr s))

(defun subst-compose-snd (s)
  (cddr s))

(defun subst-id-p (s)
  (eq s 'ID))

(defun subst-up-p (s)
  (eq s 'UP))

(defun subst-push-p (s)
  (and (consp s)
       (eq (car s) 'PUSH)))

(defun subst-compose-p (s)
  (and (consp s)
       (eq (car s) 'COMPOSE)))

(defun n-ups (n)
  (if (> n 1)
      (subst-compose (subst-up) (n-ups (- n 1)))
    (if (= n 1)
	(subst-up)
      (subst-id))))

(defun n-ups-p (s &optional (n 1))
  (if (subst-up-p s)
      n
    (if (and (subst-compose-p s)
	     (subst-up-p (subst-compose-fst s)))
	(n-ups-p (subst-compose-snd s) (1+ n))
      nil)))

(defun precook-term (trm &optional (n 0))
  (cond ((lam-p trm) (lam (precook-term (lam-body trm) (1+ n))))
	((app-p trm) (app (precook-term (app-func trm) n) (precook-term (app-arg trm) n)))
	((pair-p trm) (pair (precook-term (pair-fst trm) n) (precook-term (pair-snd trm) n)))
	((fst-p trm) (fst (precook-term (fst-arg trm) n)))
	((snd-p trm) (snd (precook-term (snd-arg trm) n)))
	((numberp trm)
	 (precook-db trm))
	(t
	 (if (get trm 'evar)
	     (precook-evar trm n)
	   trm))))

(defun precook-db (trm)
  (if (> trm 0)
      (trm-subst 0 (n-ups trm))
    0))

(defun precook-evar (trm n)
  (if (> n 0)
      (trm-subst trm (n-ups n))
    trm))

(defun precook-type (tp &optional (n 0))
  (cond ((dpi-p tp)
	 (dpi (precook-type (dpi-dom tp) n)
	      (precook-type (dpi-cod tp) (1+ n))))
	((dclass-p tp)
	 (dclass (precook-term (dclass-pred tp) n)))
	((pf-p tp)
	 (pf (precook-term (pf-prop tp) n)))
	(t tp)))

(defun precook-ctx (ctx)
  (if (consp ctx)
      (ctx-cons (precook-type (car ctx))
		(precook-ctx (cdr ctx)))
    nil))

(defun postcook-term (trm &optional (n 0))
  (cond ((lam-p trm) (lam (postcook-term (lam-body trm) (1+ n))))
	((app-p trm) (app (postcook-term (app-func trm) n) (postcook-term (app-arg trm) n)))
	((pair-p trm) (pair (postcook-term (pair-fst trm) n) (postcook-term (pair-snd trm) n)))
	((fst-p trm) (fst (postcook-term (fst-arg trm) n)))
	((snd-p trm) (snd (postcook-term (snd-arg trm) n)))
	((numberp trm) trm)
	((trm-subst-p trm)
	 (let ((sl (postcook-subst (trm-subst-subst trm)))
	       (trm2 (postcook-term (trm-subst-trm trm))))
	   (dolist (s sl)
	     (setq trm2 (normalize (dbsubst trm2 (car s) (cdr s)))))
	   trm2))
	(t trm)))

(defun postcook-subst (s)
  (cond ((subst-id-p s) (list (cons #'identity 'ID)))
	((subst-up-p s) (list (cons #'1+ 'ID)))
	((subst-push-p s)
	 (let ((l (postcook-subst (subst-push-subst s))))
	   (cons (cons #'identity (cons (subst-push-trm s) (car l))) (cdr l))))
	((subst-compose-p s)
	 (append (postcook-subst (subst-compose-fst s))
		 (postcook-subst (subst-compose-snd s))))
	(t nil)))

(defun postcook-type (tp &optional (n 0))
  (cond ((dpi-p tp)
	 (dpi (postcook-type (dpi-dom tp) n)
	      (postcook-type (dpi-cod tp) (1+ n))))
	((dclass-p tp)
	 (dclass (postcook-term (dclass-pred tp) n)))
	((pf-p tp)
	 (pf (postcook-term (pf-prop tp) n)))
	((tp-subst-p tp)
	 (let ((sl (postcook-subst (tp-subst-subst tp)))
	       (tp2 (postcook-type (tp-subst-tp tp))))
	   (dolist (s sl)
	     (setq tp2 (normalize-type (dbsubst-type tp2 (car s) (cdr s)))))
	   tp2))
	(t tp)))

(defun postcook-ctx (ctx)
  (if (consp ctx)
      (ctx-cons (postcook-type (car ctx))
		(postcook-ctx (cdr ctx)))
    nil))

(defun ls-beta-redex-p (trm)
  (and (app-p trm) (lam-p (app-func trm))))
  
(defun ls-beta-reduce (trm)
  (trm-subst (lam-body (app-func trm)) (subst-push (app-arg trm) (subst-id))))

(defun ls-app-redex-p (trm)
  (and (trm-subst-p trm)
       (app-p (trm-subst-trm trm))))

(defun ls-app-reduce (trm)
  (app (trm-subst (app-func (trm-subst-trm trm)) (trm-subst-subst trm))
       (trm-subst (app-arg (trm-subst-trm trm)) (trm-subst-subst trm))))

(defun ls-varcons-redex-p (trm)
  (and (trm-subst-p trm)
       (equal (trm-subst-trm trm) 0)
       (subst-push-p (trm-subst-subst trm))))

(defun ls-varcons-reduce (trm)
  (subst-push-trm (trm-subst-subst trm)))

(defun ls-id-redex-p (trm)
  (and (trm-subst-p trm)
       (subst-id-p (trm-subst-subst trm))))

(defun ls-id-reduce (trm)
  (trm-subst-trm trm))

(defun ls-abs-redex-p (trm)
  (and (trm-subst-p trm)
       (lam-p (trm-subst-trm trm))))

(defun ls-abs-reduce (trm)
  (lam (trm-subst (lam-body (trm-subst-trm trm))
		  (subst-push 0 (subst-compose (trm-subst-subst trm) (subst-up))))))

(defun ls-clos-redex-p (trm)
  (and (trm-subst-p trm)
       (trm-subst-p (trm-subst-trm trm))))

(defun ls-clos-reduce (trm)
  (trm-subst (trm-subst-trm (trm-subst-trm trm))
	     (subst-compose (trm-subst-subst (trm-subst-trm trm))
			    (trm-subst-subst trm))))

(defun ls-idl-redex-p (s)
  (and (subst-compose-p s)
       (subst-id-p (subst-compose-fst s))))

(defun ls-idl-reduce (s)
  (subst-compose-snd s))

(defun ls-idr-redex-p (s)
  (and (subst-compose-p s)
       (subst-id-p (subst-compose-snd s))))

(defun ls-idr-reduce (s)
  (subst-compose-fst s))

(defun ls-shiftcons-redex-p (s)
  (and (subst-compose-p s)
       (subst-up-p (subst-compose-fst s))
       (subst-push-p (subst-compose-snd s))))

(defun ls-shiftcons-reduce (s)
  (subst-push-subst (subst-compose-snd s)))

(defun ls-assenv-redex-p (s)
  (and (subst-compose-p s)
       (subst-compose-p (subst-compose-fst s))))

(defun ls-assenv-reduce (s)
  (subst-compose (subst-compose-fst (subst-compose-fst s))
		 (subst-compose (subst-compose-snd (subst-compose-fst s))
				(subst-compose-snd s))))

(defun ls-mapenv-redex-p (s)
  (and (subst-compose-p s)
       (subst-push-p (subst-compose-fst s))))

(defun ls-mapenv-reduce (s)
  (subst-push (trm-subst (subst-push-trm (subst-compose-fst s))
			 (subst-compose-snd s))
	      (subst-compose (subst-push-subst (subst-compose-fst s))
			     (subst-compose-snd s))))

(defun ls-varshift-redex-p (s)
  (and (subst-push-p s)
       (equal (subst-push-trm s) 0)
       (subst-up-p (subst-push-subst s))))

(defun ls-varshift-reduce (s)
  (subst-id))

(defun ls-scons-redex-p (s)
  (and (subst-push-p s)
       (trm-subst-p (subst-push-trm s))
       (equal (trm-subst-trm (subst-push-trm s)) 0)
       (subst-compose-p (subst-push-subst s))
       (subst-up-p (subst-compose-fst (subst-push-subst s)))
       (equal (subst-compose-snd (subst-push-subst s)) (trm-subst-subst (subst-push-trm s)))))

(defun ls-scons-reduce (s)
  (trm-subst-subst (subst-push-trm s)))

; reductions for pairs (not in DHK):
(defun ls-fst-redex-p (trm)
  (and (fst-p trm) (pair-p (fst-arg trm))))

(defun ls-snd-redex-p (trm)
  (and (snd-p trm) (pair-p (snd-arg trm))))

(defun ls-fst-reduce (trm)
  (pair-fst (fst-arg trm)))

(defun ls-snd-reduce (trm)
  (pair-snd (snd-arg trm)))

(defun ls-fst-subst-redex-p (trm)
  (and (trm-subst-p trm)
       (fst-p (trm-subst-trm trm))))

(defun ls-fst-subst-reduce (trm)
  (fst (trm-subst (fst-arg (trm-subst-trm trm)) (trm-subst-subst trm))))

(defun ls-snd-subst-redex-p (trm)
  (and (trm-subst-p trm)
       (snd-p (trm-subst-trm trm))))

(defun ls-snd-subst-reduce (trm)
  (snd (trm-subst (snd-arg (trm-subst-trm trm)) (trm-subst-subst trm))))

(defun ls-pair-subst-redex-p (trm)
  (and (trm-subst-p trm)
       (pair-p (trm-subst-trm trm))))

(defun ls-pair-subst-reduce (trm)
  (pair (trm-subst (pair-fst (trm-subst-trm trm)) (trm-subst-subst trm))
	(trm-subst (pair-snd (trm-subst-trm trm)) (trm-subst-subst trm))))

; reductions for deptypes with expl substs:
(defun dpi-subst-redex-p (tp)
  (and (tp-subst-p tp)
       (dpi-p (tp-subst-tp tp))))

(defun dpi-subst-reduce (tp)
  (dpi (tp-subst (dpi-dom (tp-subst-tp tp)) (tp-subst-subst tp))
       (tp-subst (dpi-cod (tp-subst-tp tp))
		 (subst-push 0 (subst-compose (tp-subst-subst tp) (subst-up))))))

(defun dclass-subst-redex-p (tp)
  (and (tp-subst-p tp)
       (dclass-p (tp-subst-tp tp))))

(defun dclass-subst-reduce (tp)
  (dclass (trm-subst (dclass-pred (tp-subst-tp tp)) (tp-subst-subst tp))))

(defun pf-subst-redex-p (tp)
  (and (tp-subst-p tp)
       (pf-p (tp-subst-tp tp))))

(defun pf-subst-reduce (tp)
  (pf (trm-subst (pf-prop (tp-subst-tp tp)) (tp-subst-subst tp))))

(defun obj-subst-redex-p (tp)
  (and (tp-subst-p tp)
       (obj-p (tp-subst-tp tp))))

(defun obj-subst-reduce (tp)
  (obj))

(defun prop-subst-redex-p (tp)
  (and (tp-subst-p tp)
       (prop-p (tp-subst-tp tp))))

(defun prop-subst-reduce (tp)
  (prop))

(defun tp-clos-redex-p (tp)
  (and (tp-subst-p tp)
       (tp-subst-p (tp-subst-tp tp))))

(defun tp-clos-reduce (tp)
  (tp-subst (tp-subst-tp (tp-subst-tp tp))
	    (subst-compose (tp-subst-subst (tp-subst-tp tp))
			   (tp-subst-subst tp))))

; multiple reductions
(defun weak-head-reduce (trm)
  (do ((trm2 trm (weak-head-reduce-1 trm2))
       (prev nil trm2))
      ((eq trm2 prev)
       trm2)))

(defun weak-head-reduce-1 (trm)
  (if (app-p trm)
      (let ((trm2 (weak-head-reduce-1 (app-func trm))))
	(if (eq trm2 (app-func trm))
	    (weak-head-reduce-2 trm)
	  (app trm2 (app-arg trm))))
    (if (fst-p trm)
	(let ((trm2 (weak-head-reduce-1 (fst-arg trm))))
	  (if (eq trm2 (fst-arg trm))
	      (weak-head-reduce-2 trm)
	    (fst trm2)))
      (if (snd-p trm)
	  (let ((trm2 (weak-head-reduce-1 (snd-arg trm))))
	    (if (eq trm2 (snd-arg trm))
		(weak-head-reduce-2 trm)
	      (snd trm2)))
	(if (trm-subst-p trm)
	    (let ((trm2 (weak-head-reduce-1 (trm-subst-trm trm))))
	      (if (eq trm2 (trm-subst-trm trm))
		  (let ((s2 (weak-subst-reduce-1 (trm-subst-subst trm))))
		    (if (eq s2 (trm-subst-subst trm))
			(weak-head-reduce-2 trm)
		      (trm-subst trm2 s2)))
		(trm-subst trm2 (trm-subst-subst trm))))
	  (weak-head-reduce-2 trm))))))

(defun weak-subst-reduce-1 (s)
  (if (and (subst-compose-p s)
	   (subst-up-p (subst-compose-fst s)))
      (let ((s2 (weak-subst-reduce-1 (subst-compose-snd s))))
	(if (eq s2 (subst-compose-snd s))
	    (weak-subst-reduce-2 s)
	  (subst-compose (subst-up) s2)))
    (weak-subst-reduce-2 s)))

(defun weak-head-reduce-2 (trm)
  (cond ((ls-beta-redex-p trm)
	 (ls-beta-reduce trm))
	((ls-app-redex-p trm)
	 (ls-app-reduce trm))
	((ls-varcons-redex-p trm)
	 (ls-varcons-reduce trm))
	((ls-id-redex-p trm)
	 (ls-id-reduce trm))
	((ls-abs-redex-p trm)
	 (ls-abs-reduce trm))
	((ls-clos-redex-p trm)
	 (ls-clos-reduce trm))
	((ls-fst-redex-p trm)
	 (ls-fst-reduce trm))
	((ls-snd-redex-p trm)
	 (ls-snd-reduce trm))
	((ls-fst-subst-redex-p trm)
	 (ls-fst-subst-reduce trm))
	((ls-snd-subst-redex-p trm)
	 (ls-snd-subst-reduce trm))
	((ls-pair-subst-redex-p trm)
	 (ls-pair-subst-reduce trm))
	(t trm)))

(defun weak-subst-reduce-2 (s)
  (cond ((ls-idl-redex-p s)
	 (ls-idl-reduce s))
	((ls-idr-redex-p s)
	 (ls-idr-reduce s))
	((ls-shiftcons-redex-p s)
	 (ls-shiftcons-reduce s))
	((ls-assenv-redex-p s)
	 (ls-assenv-reduce s))
	((ls-mapenv-redex-p s)
	 (ls-mapenv-reduce s))
	((ls-varshift-redex-p s)
	 (ls-varshift-reduce s))
	((ls-scons-redex-p s)
	 (ls-scons-reduce s))
	(t s)))

(defun weak-type-reduce (tp)
  (do ((tp2 tp (weak-type-reduce-1 tp2))
       (prev nil tp2))
      ((eq tp2 prev)
       tp2)))

(defun weak-type-reduce-1 (tp)
  (cond ((tp-clos-redex-p tp)
	 (tp-clos-reduce tp))
	((dpi-subst-redex-p tp)
	 (dpi-subst-reduce tp))
	((dclass-subst-redex-p tp)
	 (dclass-subst-reduce tp))
	((pf-subst-redex-p tp)
	 (pf-subst-reduce tp))
	((obj-subst-redex-p tp)
	 (obj-subst-reduce tp))
	((prop-subst-redex-p tp)
	 (prop-subst-reduce tp))
	(t tp)))
       
; type checking
(defun ctx-normal-eq-in-type-F (ctx trm1 trm2 tp)
  (cond ((dpi-p tp)
	 (ctx-normal-eq-in-type-F
	  (ctx-cons (dpi-dom tp) ctx)
	  (app (trm-subst trm1 (subst-up)) 0)
	  (app (trm-subst trm2 (subst-up)) 0)
	  (weak-type-reduce (dpi-cod tp))))
	((dclass-p tp)
	 (let ((phi (dclass-pred tp))
	       (f (fst trm1)))
	   (and
	    (ctx-normal-eq-in-type-F ctx f (fst trm2) (obj))
	    (ctx-normal-eq-in-type-F ctx (snd trm1) (snd trm2)
				     (pf (app phi f))))))
	((pf-p tp)
	 (if (equal trm1 trm2) ; short cut if already equal (to prevent duplicating computation) -- makes a huge difference on leftInvOfInjProp
	     (let* ((trm1h (weak-head-reduce trm1))
		    (tp1 (ctx-extr-eq-in-type-F ctx trm1h trm1h)))
	       (if (and tp1 (pf-p tp1))
		   (ctx-normal-eq-in-type-F ctx (pf-prop tp1) (pf-prop tp) (prop))
		 nil))
	   (let* ((trm1h (weak-head-reduce trm1))
		  (tp1 (ctx-extr-eq-in-type-F ctx trm1h trm1h)))
	     (if (and tp1 (pf-p tp1))
		 (let* ((trm2h (weak-head-reduce trm2))
			(tp2 (ctx-extr-eq-in-type-F ctx trm2h trm2h)))
		   (if (and tp2 (pf-p tp2))
		       (let ((ntp (pf-prop tp)))
			 (and (ctx-normal-eq-in-type-F ctx (pf-prop tp1) ntp (prop))
			      (ctx-normal-eq-in-type-F ctx (pf-prop tp2) ntp (prop))))
		     nil))
	       nil))))
	((or (obj-p tp) (prop-p tp)) ; obj or prop
	 (let ((tp1 (ctx-extr-eq-in-type-F ctx (weak-head-reduce trm1) (weak-head-reduce trm2))))
	   (and tp1 (equal tp1 tp))))
	(t nil))) ; should not happen

(defun ctx-extr-eq-in-type-F (ctx trm1 trm2)
  (cond ((app-p trm1)
	 (if (app-p trm2)
	     (let ((ftp (ctx-extr-eq-in-type-F ctx (app-func trm1) (app-func trm2))))
	       (if (and ftp (dpi-p ftp))
		   (let ((dom (dpi-dom ftp))
			 (a (app-arg trm1)))
		     (if (ctx-normal-eq-in-type-F ctx a (app-arg trm2) (weak-type-reduce dom))
			 (weak-type-reduce
			  (tp-subst (dpi-cod ftp)
				    (subst-push a (subst-id))))
		       nil))
		 nil))
	   nil))
	((fst-p trm1)
	 (if (fst-p trm2)
	     (let ((tp (ctx-extr-eq-in-type-F ctx (fst-arg trm1) (fst-arg trm2))))
	       (if (and tp (dclass-p tp))
		   (obj)
		 nil))
	   nil))
	((snd-p trm1)
	 (if (snd-p trm2)
	     (let ((tp (ctx-extr-eq-in-type-F ctx (snd-arg trm1) (snd-arg trm2))))
	       (if (and tp (dclass-p tp))
		   (pf (app (dclass-pred tp) (fst (snd-arg trm1))))
		 nil))
	   nil))
	((equal trm1 0)
	 (if (equal trm2 0)
	     (weak-type-reduce
	      (tp-subst (car ctx) (subst-up)))
	   nil))
	((and (trm-subst-p trm1)
	      (equal (trm-subst-trm trm1) 0))
	 (let ((n (n-ups-p (trm-subst-subst trm1))))
	   (if (and n
		    (trm-subst-p trm2)
		    (equal (trm-subst-trm trm2) 0)
		    (equal n (n-ups-p (trm-subst-subst trm2))))
	       (weak-type-reduce
		(tp-subst (nth n ctx) (n-ups (1+ n))))
	     nil)))
	((symbolp trm1)
	 (if (eq trm1 trm2)
	     (ls-symbol-type trm1)
	   (if (and (trm-subst-p trm2)
		    (equal trm1 (trm-subst-trm trm2)))
	       (ls-symbol-type trm1)
	     nil)))
	((and (trm-subst-p trm1)
	      (symbolp (trm-subst-trm trm1)))
	 (if (and (trm-subst-p trm2)
		  (equal (trm-subst-trm trm1) (trm-subst-trm trm2)))
	     (ls-symbol-type (trm-subst-trm trm1))
	   (if (and (symbolp trm2) (eq (trm-subst-trm trm1) trm2))
	       (ls-symbol-type trm2)
	     nil)))
	(t nil)))

(defun ls-symbol-type (trm)
  (let ((tp (get trm 'ls-dbtype)))
    (if tp
	tp
      (let ((tp0 (get trm 'dbtype)))
	(if tp0
	    (let ((tp (precook-type tp0)))
	      (setf (get trm 'ls-dbtype) tp)
	      tp)
	  nil)))))
