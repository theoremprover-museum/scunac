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

; Author: Chad E Brown
; October 2005

; terms with blanks.  Blanks can be _ or ?
; later I may treat _ and ? differently
; plus we allow the user to leave out "Apps" and leave out "const"/"abbrev"/"bvar" and just put name
; (except in binders)

; coercefn takes a term (of type fromtp), a fromtp and a totp
; and either returns NIL or a term of type totp
(defun add-coercion-to-state (coercefn mctx theory-state)
  (if theory-state
      (if (eq (caar theory-state) 'COERCIONS)
	  (cons (cons 'COERCIONS (acons mctx coercefn (cdar theory-state)))
		(cdr theory-state))
	(cons (car theory-state)
	      (add-coercion-to-state coercefn mctx (cdr theory-state))))
    (list (list 'COERCIONS (cons mctx coercefn)))))

; might want to do more classification here (by the four simple types x whether it's a function type)
; also might want to do subsumption checking (w/pf irrelevance)
(defun add-to-extended-ctx (prefix term dtype theory-state)
  (when (> *verbose* 90)
    (format t "Adding to Extended Ctx:~%~d~%|- ~d~% : ~d~2%"
	    prefix term dtype))
;  (unless (check-deptype-normal (beta-normalize term) dtype prefix)
;    (setq *term* term *dtype* dtype *prefix* prefix)
;    (break))
  (add-to-extended-ctx-0 prefix term dtype theory-state))

(defun add-to-extended-ctx-0 (prefix term dtype theory-state)
  (if theory-state
      (if (eq (caar theory-state) 'EXTENDED-CTX)
	  (cons (cons 'EXTENDED-CTX (cons (list prefix term dtype) (cdar theory-state)))
		(cdr theory-state))
	(cons (car theory-state)
	      (add-to-extended-ctx-0 prefix term dtype (cdr theory-state))))
    (list (list 'EXTENDED-CTX (list prefix term dtype)))))
	  
;(defun add-type-predictor-to-state (h fn theory-state)
;  (cons (list 'TYPE-PREDICTOR h fn) theory-state))

; dtp - predeptype
(defun deptype-fill-in-blanks (dtp &optional *theory-state* prefix)
  (if (consp dtp)
      (case (car dtp)
	    (PF
	     (multiple-value-bind
	      (trm info fail)
	      (normal-fill-in-blanks (cdr dtp) (prop) *theory-state* prefix)
	      (if trm
		  (values (pf trm) info)
		(values nil info fail))))
	    (DPI
	     (let ((name (cadr dtp))
		   (predom (caddr dtp))
		   (precod (cdddr dtp)))
	       (when (stringp name)
		 (setq name (intern name)))
	       (if (symbolp name)
		   (multiple-value-bind
		    (dom info fail)
		    (deptype-fill-in-blanks predom *theory-state* prefix)
		    (if dom
			(let ((savebvar (get name 'bvar))
			      (savedbtype (get name 'dbtype)))
			  (setf (get name 'bvar) t)
			  (setf (get name 'dbtype) dom)
			  (multiple-value-bind
			   (cod info2 fail)
			   (deptype-fill-in-blanks precod
						   *theory-state*
						   (cons (list name dom) prefix))
			   (setf (get name 'bvar) savebvar)
			   (setf (get name 'dbtype) savedbtype)
			   (if cod
			       (values (dpi dom (quick-db-type name 0 cod)) (append info info2))
			     (values nil nil fail))))))
		 (values nil nil (format nil "~d for ~d~%is not a bvar" name dtp)))))
	    (DARR
	     (multiple-value-bind
	      (dom info fail)
	      (deptype-fill-in-blanks (cadr dtp) *theory-state* prefix)
	      (if dom
		  (multiple-value-bind
		   (cod info2 fail)
		   (deptype-fill-in-blanks (cddr dtp) *theory-state* prefix)
		   (if cod
		       (values (dpi dom cod) (append info info2))
		     (values nil nil fail)))
		(values nil nil fail))))
	    (t
	     (multiple-value-bind
	      (trm etp info fail)
	      (extr-fill-in-blanks-1 dtp *theory-state* prefix)
	      (if trm
		  (cond ((obj-p etp)
			 (values (set2class trm) info))
			((heq etp *pred*)
			 (values (dclass trm) info))
			((prop-p etp)
			 (values (pf trm) info))
			((dclass-p etp)
			 (values (set2class (fst trm)) info))
			(t (values nil nil (format nil "Cannot make a type from the ~d ~%~d" etp trm))))
		(values nil info fail)))))
    (case dtp
	  ((OBJ |obj|) (obj))
	  ((PROP |prop|) (prop))
	  (t
	   (multiple-value-bind
	    (trm etp info fail)
	    (extr-fill-in-blanks-1 dtp *theory-state* prefix)
	    (if trm
		(cond ((obj-p etp)
		       (values (set2class trm) info))
		      ((heq etp *pred*)
		       (values (dclass trm) info))
		      ((prop-p etp)
		       (values (pf trm) info))
		      ((dclass-p etp)
		       (values (set2class (fst trm)) info))
		      (t (values nil nil (format nil "Cannot make a type from the ~d ~%~d" etp trm))))
	      (values nil info fail)))))))

; Now dtp is a real deptype (maybe with info?)
; note that PAIRs cannot be extractions because we cannot
; extract the class type (determined by PHI) from <A:obj;P:pf (PHI A)>,
; though we can extract A and (PHI A).
(defun normal-fill-in-blanks (trm dtp &optional *theory-state* prefix info)
  (if (consp trm)
      (if (eq (car trm) 'LAM)
	  (let ((x (cadr trm)))
	    (if (or (symbolp x) (stringp x))
		(lambda-fill-in-blanks (list x) (cddr trm) dtp *theory-state* prefix info)
	      (if (consp x)
		  (let ((z (find-if-not #'(lambda (z) (or (symbolp z) (stringp z))) x)))
		    (if z
			(values nil nil (format nil "~d for ~d~%is not a bvar" x trm))
		      (lambda-fill-in-blanks x (cddr trm) dtp *theory-state* prefix info)))
		(values nil nil (format nil "bad lambda var(s) ~d" x)))))
	(if (eq (car trm) 'PAIR)
	    (if (dclass-p dtp)
		(multiple-value-bind
		 (trm1 info fail)
		 (normal-fill-in-blanks (cadr trm) (obj) *theory-state* prefix info)
		 (if fail
		     (values nil nil fail)
		   (multiple-value-bind
		    (trm2 info2 fail2)
		    (normal-fill-in-blanks (cddr trm)
					   (pf (normalize (pair-prop dtp trm1)))
					   *theory-state* prefix info)
		    (if fail2
			(values nil nil fail2)
		      (values (pair trm1 trm2) (append info info2))))))
	      (values nil nil (format nil "Pair not of class type")))
	  (app-fill-in-blanks (car trm) (cdr trm) dtp *theory-state* prefix info)))
    (case trm
	  (_
	   (let ((e (intern-gensym)))
	     (setf (get e 'EVAR) t)
	     (setf (get e 'DBTYPE) dtp)
	     (values e
		     (cons (list 'EVAR e dtp) info))))
	  (?
	   (let ((fdtp (prefix-dpi-db prefix dtp)))
	     (let ((e (intern-gensym)))
	       (setf (get e 'EVAR) t)
	       (setf (get e 'DBTYPE) fdtp)
	       (values (app-n e (reverse (mapcar #'car prefix)))
		       (cons (list 'EVAR e fdtp) info)))))
	  (t
	   (app-fill-in-blanks trm nil dtp *theory-state* prefix info)))))

(defun lambda-fill-in-blanks (xl body dtp *theory-state* prefix &optional info)
  (if xl
      (if (dpi-p dtp)
	  (let* ((foo (car xl))
		 (name (if (symbolp foo) foo (intern foo)))
		 (dom (dpi-dom dtp)))
	    (let ((savebvar (get name 'bvar))
		  (savedbtype (get name 'dbtype)))
	      (setf (get name 'bvar) t)
	      (setf (get name 'dbtype) dom)
	      (multiple-value-bind
	       (trm info fail)
	       (lambda-fill-in-blanks
		(cdr xl) body
		(dbsubst-type-0 (dpi-cod dtp) name)
		*theory-state*
		(cons (list name dom) prefix)
		info)
	       (setf (get name 'bvar) savebvar)
	       (setf (get name 'dbtype) savedbtype)
	       (if fail
		   (values nil nil fail)
		 (values (lam (quick-db-term name 0 trm)) info)))))
	(values nil nil (format nil "Lambda before ~d~%cannot have type ~d" body dtp)))
    (normal-fill-in-blanks body dtp *theory-state* prefix info)))

(defun extr-fill-in-blanks (extr dtp *theory-state* prefix &optional info)
  (if (consp extr)
      (app-fill-in-blanks (car extr) (cdr extr) dtp *theory-state* prefix info)
    (app-fill-in-blanks extr nil dtp *theory-state* prefix info)))

; returns extracted type as well (assumes no given type info)
(defun extr-fill-in-blanks-1 (extr *theory-state* prefix &optional info)
  (if (consp extr)
      (case (car extr)
	    (_INTERNAL-APP
	     (values nil nil nil (format nil "cannot infer type of internal func ~d" extr)))
	    (_CLASSCONSTRUCTOR
	     (multiple-value-bind
	      (a info fail)
	      (extr-fill-in-blanks extr *pred* *theory-state* prefix info)
	      (values a *pred* info fail)))
	    ((_SETCONSTRUCTOR _PAIRSETCONSTRUCTOR)
	     (multiple-value-bind
	      (a info fail)
	      (extr-fill-in-blanks extr (obj) *theory-state* prefix info)
	      (values a (obj) info fail)))
	    (_SETENUM
	     (multiple-value-bind
	      (a info fail)
	      (extr-fill-in-blanks extr (obj) *theory-state* prefix info)
	      (values a (obj) info fail)))
	    (t
	     (multiple-value-bind
	      (htrm dtp)
	      (fill-in-blanks-name-lookup (car extr) prefix)
	      (if htrm
		  (app-fill-in-blanks-1 (car extr) dtp (cdr extr) *theory-state* prefix info)
		(values nil nil nil (format nil "Unrecognized head ~d" (car extr)))))))
    (multiple-value-bind
     (htrm dtp)
     (fill-in-blanks-name-lookup extr prefix)
     (if htrm
	 (app-fill-in-blanks-1 extr dtp nil *theory-state* prefix info)
       (values nil nil nil (format nil "Unrecognized head ~d" extr))))))

(defun app-fill-in-blanks (h args dtp *theory-state* prefix &optional info)
  (multiple-value-bind
   (trm etp info fail)
   (app-fill-in-blanks-0 h args dtp *theory-state* prefix t info)
   (if fail
       (values nil nil fail)
; change this subtype constraint to (1) check for equality
; and (2) if not equal, put in an evar for coercion -
     (if (ctx-types-eq *emptyctx* etp dtp)
	 (values trm info)
       (multiple-value-bind
	(trm2 fail2)
	(automatic-coercion trm etp dtp *theory-state* prefix)
	(if fail2
	    ; try trivial unification
	    (multiple-value-bind
	     (trm3 info3 fail3)
	     (unif-fill-in-blanks trm etp dtp info prefix)
	     (if fail3
		 (progn ; add an evar to coerce (underspecified)
		   (when (> *verbose* 50)
		     (format t "COERCE:~%~d~%~d~%Extracted ~d~%Expected ~d~%"
			     (cons h args)
			trm
			etp
			dtp))
		   (let ((fdtp (prefix-dpi-db prefix (dpi etp dtp))))
		     (let ((e (intern-gensym)))
		       (setf (get e 'EVAR) t)
		       (setf (get e 'DBTYPE) fdtp)
		       (values (app (app-n e (reverse (mapcar #'cadr prefix)))
				    trm)
			       (append info
				       (list (list 'EVAR e fdtp
						   (format nil "Subgoal: Show $~d$ has type $~d$~%"
							   (term-direct-latex trm)
							   (dtype-direct-latex dtp)
							   )
						   trm
						   dtp
						   etp
						   )))))))
	       (values trm3 info3)))
	  (values trm2 info)))))))

(defun unif-fill-in-blanks (trm etp dtp info prefix)
  (if (or (and (pf-p etp) (pf-p dtp))
	  (and (dclass-p etp) (dclass-p dtp)))
      (let ((evars (mapcar #'(lambda (y) (cons (cadr y) (caddr y)))
			   (remove-if-not #'(lambda (x) (eq (car x) 'EVAR)) info))))
	(multiple-value-bind
	 (succ unif-states delayed)
	 (preunify-msv evars evars nil
					; dpairs
		       (if (pf-p etp)
			   (list (list nil (pf-prop etp) (pf-prop dtp) (prop)))
			 (list (list nil (dclass-pred etp) (dclass-pred dtp) *pred*)))
					; fill
		       nil
					; msv
		       0
					; stop on success
		       t)
	 (if succ
	     (let* ((cevars2 (caar succ))
		    (theta2 (cadar succ))
		    (etp2 (normalize-type (simul-subst-type theta2 etp)))
		    (dtp2 (normalize-type (simul-subst-type theta2 dtp))))
	       (if (ctx-types-eq *emptyctx* etp2 dtp2) ; don't trust unification, not sure why
		   (values (normalize (simul-subst theta2 trm))
			   (append
			    (remove-if #'(lambda (x)
					   (and (eq (car x) 'EVAR)
						(let ((a (assoc (cadr x) theta2)))
						  (and a (not (eq (car a) (cdr a)))))))
				       info)
			    (mapcar #'(lambda (x)
					(list 'EVAR (car x) (cdr x)
					      "Unification Variable"))
				    (remove-if #'(lambda (x)
						   (assoc (car x) evars))
					       cevars2))))
		 (values nil nil "Could not unify types")))
	   (values nil nil "Could not unify types"))))
    (values nil nil "Could not unify types")))

; special cases we want to coerce eagerly (without adding an evar)
; any class -> obj (via fst)
; class -> pf (via snd)
; a pf with head definition folding/unfolding
(defun automatic-coercion (trm fromtp totp *theory-state* prefix)
  (when (> *verbose* 51)
    (format t "Trying to coerce ~d from ~d to ~d~%" trm fromtp totp))
  (cond ((and (obj-p totp) (dclass-p fromtp))
	 (fst trm))
	((and (dclass-p fromtp)
	      (pf-p totp)
	      (ctx-terms-eq-type *emptyctx* (pf-prop totp) (normalize (pair-prop fromtp (fst trm))) (prop)))
	 (snd trm))
	((and *universal-set* (obj-p fromtp) (dclass-p totp)
	      (app-p (dclass-pred totp))
	      (eq (app-func (dclass-pred totp)) '|in|)
	      (eq (app-arg (dclass-pred totp)) *universal-set*))
	 (pair trm (app *universal-set-pf* trm)))
	((and *universal-set* (dclass-p fromtp) (dclass-p totp)
	      (app-p (dclass-pred totp))
	      (eq (app-func (dclass-pred totp)) '|in|)
	      (eq (app-arg (dclass-pred totp)) *universal-set*))
	 (pair (fst trm) (app *universal-set-pf* (fst trm))))
	((and (pf-p fromtp)
	      (pf-p totp)
	      (head-unfolds-to (pf-prop fromtp) (pf-prop totp) (prop)))
	 (explicit-reln-defn-unfold trm (pf-prop fromtp)))
	((and (pf-p fromtp)
	      (pf-p totp)
	      (head-unfolds-to (pf-prop totp) (pf-prop fromtp) (prop)))
	 (explicit-reln-defn-fold trm (pf-prop totp)))
	((and (pf-p fromtp) ; coerce from |- (a::{x:A|phi x}) to |- (a::A)
	      (pf-p totp)
	      (app-p (pf-prop fromtp))
	      (app-p (app-func (pf-prop fromtp)))
	      (eq (app-func (app-func (pf-prop fromtp))) '|in|)
	      (app-p (pf-prop totp))
	      (app-p (app-func (pf-prop totp)))
	      (eq (app-func (app-func (pf-prop totp))) '|in|)
	      (ctx-terms-eq-type *emptyctx* (app-arg (pf-prop fromtp)) (app-arg (pf-prop totp)) (obj))
	      (app-p (app-arg (app-func (pf-prop fromtp))))
	      (app-p (app-func (app-arg (app-func (pf-prop fromtp)))))
	      (eq (app-func (app-func (app-arg (app-func (pf-prop fromtp))))) '|dsetconstr|)
	      (ctx-terms-eq-type *emptyctx*
				 (app-arg (app-func (app-arg (app-func (pf-prop fromtp))))) ; bounding set
				 (app-arg (app-func (pf-prop totp))) (obj)))
	 (app-l '|dsetconstrEL|
		(app-arg (app-func (app-arg (app-func (pf-prop fromtp))))) ; bounding set
		(app-arg (app-arg (app-func (pf-prop fromtp)))) ; property
		(app-arg (pf-prop fromtp))
		trm))
	(t
	 (let ((a (assoc 'COERCIONS *theory-state*)))
	   (do ((sl (cdr a) (cdr sl))
		(done nil))
	       ((or (null sl) done)
		(if done
		    (progn
		      (when (> *verbose* 50)
			(format t "Coerced ~d from ~d to ~d~%" trm fromtp totp))
		      done)
		  (if (and (dclass-p fromtp) (dclass-p totp)) ; try again with pairs
		      (multiple-value-bind
		       (trm2 fail2)
		       (automatic-coercion (snd trm)
					   (pf (normalize (app (dclass-pred fromtp) (fst trm))))
					   (pf (normalize (app (dclass-pred totp) (fst trm))))
					   *theory-state* prefix)
		       (if trm2
			   (values (pair (fst trm) trm2) nil)
			 (values nil fail2)))
		    (values nil t))))
	       (when (> *verbose* 55)
		 (format t "Trying to coerce using ~d~%" (cdar sl))
		 )
	       (setq done (funcall (cdar sl) trm fromtp totp)))))))

; prop has defn at head
(defun explicit-reln-defn-unfold (trm prop)
  (app (explicit-reln-defn-unfold-2 prop) trm))
	     
(defun explicit-reln-defn-unfold-2 (prop)
  (if (app-p prop)
      (app (explicit-reln-defn-unfold-2 (app-func prop)) (app-arg prop))
    ; otherwise, must be an abbrev
    (if (and (symbolp prop) (get prop 'abbrev))
	(auto-gen-name prop "U")
      (fail "not an abbrev " prop))))

(defun explicit-reln-defn-fold (trm prop)
  (app (explicit-reln-defn-fold-2 prop) trm))
	     
(defun explicit-reln-defn-fold-2 (prop)
  (if (app-p prop)
      (app (explicit-reln-defn-fold-2 (app-func prop)) (app-arg prop))
    ; otherwise, must be an abbrev
    (if (and (symbolp prop) (get prop 'abbrev))
	(auto-gen-name prop "F")
      (fail "not an abbrev " prop))))

(defun app-fill-in-blanks-99 (pretrm etp *theory-state* prefix &optional (allow-newvars t) info)
  (if (consp pretrm)
      (app-fill-in-blanks-0 (car pretrm) (cdr pretrm) etp *theory-state* prefix allow-newvars info)
    (app-fill-in-blanks-0 pretrm nil etp *theory-state* prefix allow-newvars info)))

; returns (trm extracteddeptype info[evars,unif,subtype constraints] fail-msg)
(defun app-fill-in-blanks-0 (h args etp *theory-state* prefix &optional (allow-newvars t) info)
  (case h
	(_INTERNAL-APP
	 (let ((funname (car args))) ; must be a name
	   (multiple-value-bind
	    (ftrm dtp)
	    (fill-in-blanks-name-lookup funname prefix)
	    (if (and ftrm (internal-fn-tp-p dtp))
		(let ((fdom (internal-fn-dom dtp))
		      (fcod (internal-fn-cod dtp)))
		  (app-fill-in-blanks-1
		   (app
		    (app 
		     (app '|Ap|
			  fdom) fcod) ftrm)
		   (dpi (SET2CLASS fdom)
			(SET2CLASS fcod))
		   (cdr args)
		   *theory-state* prefix
		   info))
	      (values nil nil nil (format nil "~d does not name a function" funname))))))
	(_CLASSCONSTRUCTOR
	 (let ((xname (car args))) ; must be a name
	   (when (stringp xname) (setq xname (intern xname)))
	   (let ((savebvar (get xname 'bvar))
		 (savedbtype (get xname 'dbtype)))
	     (setf (get xname 'bvar) t)
	     (setf (get xname 'dbtype) (obj))
	     (multiple-value-bind
	      (body info fail)
	      (extr-fill-in-blanks (cadr args) (prop) *theory-state* (cons (list xname (obj)) prefix)
				   info)
	      (setf (get xname 'bvar) savebvar)
	      (setf (get xname 'dbtype) savedbtype)
	      (if fail
		  (values nil nil nil fail)
		(values (lam (quick-db-term xname 0 body)) *pred* info nil))))))
	(_SETCONSTRUCTOR
	 (let ((xname (car args))) ; must be a name
	   (when (stringp xname) (setq xname (intern xname)))
	   (multiple-value-bind
	    (bd info fail)
	    (extr-fill-in-blanks (cadr args) (obj) *theory-state* prefix info)
	    (if fail
		(values nil nil nil fail)
	      (let ((savebvar (get xname 'bvar))
		    (savedbtype (get xname 'dbtype)))
		(setf (get xname 'bvar) t)
		(setf (get xname 'dbtype) (dclass (app '|in| bd)))
		(multiple-value-bind
		 (body info2 fail2)
		 (extr-fill-in-blanks (caddr args) (prop) *theory-state* (cons (list xname (get xname 'dbtype)) prefix) info)
		 (setf (get xname 'bvar) savebvar)
		 (setf (get xname 'dbtype) savedbtype)
		 (if fail2
		     (values nil nil nil fail2)
		   (values (app (app '|dsetconstr| bd) (lam (quick-db-term xname 0 body))) (obj) info2 nil))))))))
	(_PAIRSETCONSTRUCTOR
	 (let ((xname (car args)) ; must be a name
	       (yname (cadr args))) ; must be a name
	   (when (stringp xname) (setq xname (intern xname)))
	   (when (stringp yname) (setq yname (intern yname)))
	   (multiple-value-bind
	    (bdset1 info fail)
	    (extr-fill-in-blanks (caddr args) (obj) *theory-state* prefix info)
	    (if fail
		(values nil nil nil fail)
	      (multiple-value-bind
	       (bdset2 info1 fail)
	       (extr-fill-in-blanks (cadddr args) (obj) *theory-state* prefix info)
	       (if fail
		   (values nil nil nil fail)
		 (let ((savebvar (get xname 'bvar))
		       (savedbtype (get xname 'dbtype))
		       (savebvar2 (get yname 'bvar))
		       (savedbtype2 (get yname 'dbtype)))
		   (setf (get xname 'bvar) t)
		   (setf (get xname 'dbtype) (dclass (app '|in| bdset1)))
		   (setf (get yname 'bvar) t)
		   (setf (get yname 'dbtype) (dclass (app '|in| bdset2)))
		   (multiple-value-bind
		    (body info2 fail2)
		    (extr-fill-in-blanks (nth 4 args) (prop) *theory-state* (cons (list xname (get xname 'dbtype)) prefix) info1)
		    (setf (get xname 'bvar) savebvar)
		    (setf (get xname 'dbtype) savedbtype)
		    (setf (get yname 'bvar) savebvar2)
		    (setf (get yname 'dbtype) savedbtype2)
		    (if fail2
			(values nil nil nil fail2)
		      (values (app (app (app '|dpsetconstr| bdset1) bdset2) (lam (lam (quick-db-term xname 1 (quick-db-term yname 0 body))))) (obj) info2 nil))))))))))
	(_SETENUM
	 (setq args (reverse args))
	 (multiple-value-bind
	  (trm info fail)
	  (extr-fill-in-blanks (pop args) (obj) *theory-state* prefix info)
;	  (setq trm (app '|unitset| trm))
	  (setq trm (app (app '|setadjoin| trm) '|emptyset|))
	  (loop while (and args (not fail)) do
		(multiple-value-bind
		 (e info2 fail)
		 (extr-fill-in-blanks (pop args) (obj) *theory-state* prefix info)
		 (unless fail
		   (setq trm (app (app '|setadjoin| e) trm)))
		 (setq info info2)))
	  (if fail
	      (values nil nil nil fail)
	    (values trm (obj) info nil))))
	(t
	 (multiple-value-bind
	  (htrm dtp)
	  (fill-in-blanks-name-lookup h prefix)
	  (if htrm
	      (app-fill-in-blanks-1 htrm dtp args *theory-state* prefix info)
	    (if (or args (not allow-newvars))
		(values nil nil nil (format nil "Unrecognized head ~d" h))
       ; in this function, new is okay - if we know the type
	      (let ((newvar (if (stringp h) (intern h) h)))
		(values newvar etp (cons (list 'NEWVAR newvar etp) info) nil))))))))

(defun fill-in-blanks-name-lookup (h prefix)
  (let ((b (assoc h prefix :test #'equal)))
    (if b
	(values (car b) (cadr b))
      (if (and (symbolp h) (get h 'dbtype))
	  (values h (get h 'dbtype))
	nil))))

; h is now a real term
; and dtp is the dtype of h
; returns (trm extracteddeptype info[evars,unif,subtype constraints] fail-msg)
(defun app-fill-in-blanks-1 (h dtp args *theory-state* prefix &optional info)
  (if args
      (if (dpi-p dtp)
	  (multiple-value-bind
	   (arg1 info1 fail1)
	   (normal-fill-in-blanks (car args) (dpi-dom dtp) *theory-state* prefix
				  info)
	   (if fail1
	       (values nil nil nil fail1)
	     (multiple-value-bind
	      (ret etp info2 fail2)
	      (app-fill-in-blanks-1
	       (app h arg1)
	       (normalize-type (dbsubst-type-0 (dpi-cod dtp) arg1))
	       (cdr args) *theory-state* prefix
	       info1)
	      (if fail2
		  (values nil nil nil fail2)
		(values ret etp info2)))))
	(if (and (dclass-p dtp)
		 (app-p (dclass-pred dtp))
		 (eq (app-func (dclass-pred dtp)) '|in|))
	    (let* ((s (app-arg (dclass-pred dtp)))
		   (h0 (when (app-p s) (term-extr-head s))))
	      (if (eq h0 '|funcSet|)
		  (let ((dom (app-arg (app-func s)))
			(cod (app-arg s)))
		    (multiple-value-bind
		     (arg1 info1 fail1)
		     (normal-fill-in-blanks (car args) (dclass (app '|in| dom)) *theory-state* prefix
					    info)
		     (if fail1
			 (values nil nil nil fail1)
		       (multiple-value-bind
			(ret etp info2 fail2)
			(app-fill-in-blanks-1
			 (app-l '|ap2| dom cod h arg1)
			 (normalize-type (dclass (app '|in| cod)))
			 (cdr args) *theory-state* prefix info1)
			(if fail2
			    (values nil nil nil fail2)
			  (values ret
				  etp
				  info2
				  ))))))
		(values nil nil nil (format nil "Extra Argument ~d " (car args)))))
	  (values nil nil nil (format nil "Extra Argument ~d " (car args)))))
    (values h dtp info nil)))

(defun remove-trivial-constraints (constrs)
  (if constrs
      (if (and (eq (caar constrs) 'SUBTYPE)
	       (equal-deptype (cadar constrs) (caddar constrs)))
	  (remove-trivial-constraints (cdr constrs))
	(cons (car constrs)
	      (remove-trivial-constraints (cdr constrs))))
    nil))

	  
; need to write this
(defun solve-preterm-constraints-dtype (dtp constrs)
  (let ((constrs2 (remove-trivial-constraints constrs)))
    (values dtp constrs2 nil)))

; need to write this
(defun solve-preterm-constraints-dtype-and-term (dtp trm constrs)
  (let ((constrs2 (remove-trivial-constraints constrs)))
    (values dtp trm constrs2 nil)))

(defun internal-fn-tp-p (dtp)
  (and (dclass-p dtp)
       (app-p (dclass-pred dtp))
       (app-p (app-func (dclass-pred dtp)))
       (eq (app-func (app-func (dclass-pred dtp))) '|func|)))

(defun internal-fn-dom (dtp)
  (app-arg (app-func (dclass-pred dtp))))

(defun internal-fn-cod (dtp)
  (app-arg (dclass-pred dtp)))

(defun set2class (a)
  (dclass (app '|in| a)))

