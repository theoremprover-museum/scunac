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
; March 2006

; returns nil if tp returns a pf type
; otherwise returns a type returning a pftype
; this is the original version, a new simpler version is partially
; implemented below (equal-pf-type).  The simpler version may not work, it's unclear.
(defun congruence-pf-type (tp trm)
  (congruence-pf-type-real *emptyctx* tp trm #'identity 'ID #'identity 'ID))

(defun congruence-pf-type-real (ctx tp trm f1 sub1 f2 sub2)
  (cond ((dpi-p tp)
	 (let ((ctp (congruence-pf-type-real ctx (dbshift-type-n 1 (dpi-dom tp)) 0 #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1)) #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2)))))
	   (if ctp
	       (let* ((a1 (dbsubst-type (dpi-dom tp) f1 sub1))
		      (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2)))
		      (dtp
		       (congruence-pf-type-real
			(ctx-cons ctp (ctx-cons b1 (ctx-cons a1 ctx)))
			(dpi-cod tp)
			(gen-lam-body trm)
			#'identity (cons 2 (cons #'(lambda (i) (+ 3 (funcall f1 i))) sub1))
			#'identity (cons 1 (cons #'(lambda (i) (+ 3 (funcall f2 i))) sub2))
			)))
		 (if dtp
		     (dpi a1 (dpi b1 (dpi ctp dtp)))
		   nil))
	       (let* ((a1 (dbsubst-type (dpi-dom tp) f1 sub1))
		      (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2)))
		      (dtp
		       (congruence-pf-type-real
			(ctx-cons b1 (ctx-cons a1 ctx))
			(dpi-cod tp)
			(gen-lam-body trm)
			#'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1))
			#'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))
			)))
		 (if dtp
		     (dpi a1 (dpi b1 dtp))
		   nil)))))
	((obj-p tp)
	 (pf (app (app '|eq| (dbsubst trm f1 sub1))
		  (dbsubst trm f2 sub2))))
	((dclass-p tp)
	 (pf (app (app '|eq| (fst (dbsubst trm f1 sub1)))
		  (fst (dbsubst trm f2 sub2)))))
	((prop-p tp)
	 (pf (app (app '|equiv| (dbsubst trm f1 sub1))
		  (dbsubst trm f2 sub2))))
	((pf-p tp) nil)
	(t nil)))

; returns an inhabitant of (congruence-pf-type tp trm), assuming all non-pf sig elts have a sig#Cong
(defun congruence-pf-term (tp trm)
  (if (dtype-returns-pf-p tp)
      nil
    (congruence-pf-normal *emptyctx* *emptyctx* tp trm #'identity 'ID #'identity 'ID #'identity 'ID)))

(defun congruence-pf-normal (ctx0 ctx tp trm f1 sub1 f2 sub2 f3 sub3)
  (cond ((dpi-p tp)
	 (if (dtype-returns-pf-p (dpi-dom tp))
	     (let* ((a1 (dbsubst-type (dpi-dom tp) f1 sub1))
		    (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2))))
	       (lam (lam (congruence-pf-normal
			  (ctx-cons (dpi-dom tp) ctx0)
			  (ctx-cons b1 (ctx-cons a1 ctx))
			  (dpi-cod tp)
			  (gen-lam-body trm)
			  #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1))
			  #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))
			  #'identity (cons 0 ; 0 is a dummy value
					   (cons #'(lambda (i) (+ 2 (funcall f3 i))) sub3))
			  ))))
	     (let* ((ctp (congruence-pf-type-real ctx (dbshift-type-n 1 (dpi-dom tp)) 0 #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1)) #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))))
		    (a1 (dbsubst-type (dpi-dom tp) f1 sub1))
		    (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2))))
	       (lam (lam (lam 
			  (congruence-pf-normal
			   (ctx-cons (dpi-dom tp) ctx0)
			   (ctx-cons ctp (ctx-cons b1 (ctx-cons a1 ctx)))
			   (dpi-cod tp)
			   (gen-lam-body trm)
			   #'identity (cons 2 (cons #'(lambda (i) (+ 3 (funcall f1 i))) sub1))
			   #'identity (cons 1 (cons #'(lambda (i) (+ 3 (funcall f2 i))) sub2))
			   #'identity (cons 0 (cons #'(lambda (i) (+ 3 (funcall f3 i))) sub3))
			   )))))))
	((dclass-p tp)
	 (congruence-pf-extr ctx0 ctx (gen-pair-fst trm) f1 sub1 f2 sub2 f3 sub3))
	(t
	 (congruence-pf-extr ctx0 ctx trm f1 sub1 f2 sub2 f3 sub3))))

(defun congruence-pf-extr (ctx0 ctx trm f1 sub1 f2 sub2 f3 sub3)
  (cond ((app-p trm)
	 (multiple-value-bind
	  (ctrm ftp)
	  (congruence-pf-extr ctx0 ctx (app-func trm) f1 sub1 f2 sub2 f3 sub3)
	  (if (dpi-p ftp)
	      (if (dtype-returns-pf-p (dpi-dom ftp))
		  (values (app (app ctrm
				    (dbsubst (app-arg trm) f1 sub1))
			       (dbsubst (app-arg trm) f2 sub2))
			  (normalize-type (dbsubst-type-0 (dpi-cod ftp) (app-arg trm))))
		(let ((ctrm2 (congruence-pf-normal ctx0 ctx (dpi-dom ftp) (app-arg trm) f1 sub1 f2 sub2 f3 sub3)))
		  (values (app (app (app ctrm
					 (dbsubst (app-arg trm) f1 sub1))
				    (dbsubst (app-arg trm) f2 sub2))
			       ctrm2)
			  (normalize-type (dbsubst-type-0 (dpi-cod ftp) (app-arg trm))))))
	    (fail "Type checking problem building congruence proof term" ctx0 trm ftp))))
	((snd-p trm)
	 (fail "Proof term sent to congruence-pf-extr" ctx0 trm))
	((fst-p trm)
	 (multiple-value-bind
	  (ctrm ftp)
	  (congruence-pf-extr ctx0 ctx (fst-arg trm) f1 sub1 f2 sub2 f3 sub3)
	  (values ctrm (obj))))
	((numberp trm)
	 (values (dbsubst trm f3 sub3)
		 (ctx-extract-type ctx0 trm)))
	(t
	 (let ((cc (auto-gen-name trm "Cong" nil)))
	   (if (and (get cc 'dbtype) (equal (get cc 'dbtype)
					    (congruence-pf-type (get trm 'dbtype) trm)))
	       (values cc (get trm 'dbtype))
	     (fail "No Congruence for object " trm))))))
	 
(defun congruence-abbrev-pf-term (a aeq)
  (let ((tp (get a 'dbtype))
	(trm (get a 'defn)))
    (if (dtype-returns-pf-p tp)
	nil
      (congruence-abbrev-pf-normal *emptyctx* *emptyctx* tp trm a aeq #'identity 'ID #'identity 'ID #'identity 'ID))))

(defun congruence-abbrev-pf-normal (ctx0 ctx tp trm a aeq f1 sub1 f2 sub2 f3 sub3)
  (cond ((dpi-p tp)
	 (if (dtype-returns-pf-p (dpi-dom tp))
	     (let* ((a1 (dbsubst-type (dpi-dom tp) f1 sub1))
		    (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2))))
	       (lam (lam (congruence-abbrev-pf-normal
			  (ctx-cons (dpi-dom tp) ctx0)
			  (ctx-cons b1 (ctx-cons a1 ctx))
			  (dpi-cod tp)
			  (gen-lam-body trm)
			  (gen-lam-body a)
			  (gen-lam-body aeq)
			  #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1))
			  #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))
			  #'identity (cons 0 ; 0 is a dummy value
					   (cons #'(lambda (i) (+ 2 (funcall f3 i))) sub3))
			  ))))
	     (let* ((ctp (congruence-pf-type-real ctx (dbshift-type-n 1 (dpi-dom tp)) 0 #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1)) #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))))
		    (a1 (dbsubst-type (dpi-dom tp) f1 sub1))
		    (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2))))
	       (lam (lam (lam 
			  (congruence-abbrev-pf-normal
			   (ctx-cons (dpi-dom tp) ctx0)
			   (ctx-cons ctp (ctx-cons b1 (ctx-cons a1 ctx)))
			   (dpi-cod tp)
			   (gen-lam-body trm)
			   (gen-lam-body a)
			   (gen-lam-body aeq)
			   #'identity (cons 2 (cons #'(lambda (i) (+ 3 (funcall f1 i))) sub1))
			   #'identity (cons 1 (cons #'(lambda (i) (+ 3 (funcall f2 i))) sub2))
			   #'identity (cons 0 (cons #'(lambda (i) (+ 3 (funcall f3 i))) sub3))
			   )))))))
	((dclass-p tp)
	 (let* ((trm1 (gen-pair-fst trm))
		(a1 (gen-pair-fst a))
		(ctrm (congruence-pf-extr ctx0 ctx trm1 f1 sub1 f2 sub2 f3 sub3)))
	   (app-n '|boxeq|
		  (list (dbsubst a1 f1 sub1)
			(dbsubst trm1 f1 sub1)
			(dbsubst a1 f2 sub2)
			(dbsubst trm1 f2 sub2)
			(dbsubst aeq f1 sub1)
			(dbsubst aeq f2 sub2)
			ctrm
			))))
	((obj-p tp)
	 (let ((ctrm (congruence-pf-extr ctx0 ctx trm f1 sub1 f2 sub2 f3 sub3)))
	   (app-n '|boxeq|
		  (list (dbsubst a f1 sub1)
			(dbsubst trm f1 sub1)
			(dbsubst a f2 sub2)
			(dbsubst trm f2 sub2)
			(dbsubst aeq f1 sub1)
			(dbsubst aeq f2 sub2)
			ctrm
			))))
	((prop-p tp)
	 (let ((ctrm (congruence-pf-extr ctx0 ctx trm f1 sub1 f2 sub2 f3 sub3)))
	   (app-n '|boxequiv|
		  (list (dbsubst a f1 sub1)
			(dbsubst trm f1 sub1)
			(dbsubst a f2 sub2)
			(dbsubst trm f2 sub2)
			(dbsubst aeq f1 sub1)
			(dbsubst aeq f2 sub2)
			ctrm
			))))
	(t (fail "problem - pf abbrev given for congruence" a))))

(defun congruence-make-equation-pf (ctx trm1 trm2 tp &optional eqns equivs)
  (if (dtype-returns-pf-p tp) ; should not have been called in this case
      nil
    (congruence-make-equation-pf-normal ctx ctx tp trm1 trm2
					#'identity 'ID #'identity 'ID #'identity 'ID
					0 eqns equivs)))

; n gives boundary between shared original ctx and local context separated by f's and sub's
(defun congruence-make-equation-pf-normal (ctx0 ctx tp trm1 trm2 f1 sub1 f2 sub2 f3 sub3 n eqns equivs)
  (cond ((dpi-p tp)
	 (if (dtype-returns-pf-p (dpi-dom tp))
	     (let* ((a1 (dbsubst-type (dpi-dom tp) f1 sub1))
		    (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2)))
		    (pftrm
		     (congruence-make-equation-pf-normal
		      (ctx-cons (dpi-dom tp) ctx0)
		      (ctx-cons b1 (ctx-cons a1 ctx))
		      (dpi-cod tp)
		      (gen-lam-body trm1)
		      (gen-lam-body trm2)
		      #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1))
		      #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))
		      #'identity (cons 0 ; 0 is a dummy value
				       (cons #'(lambda (i) (+ 2 (funcall f3 i))) sub3))
		      (1+ n) (esh1 eqns) (esh1 equivs)
		      )))
	       (if pftrm
		   (lam (lam pftrm))
		 nil))
	   (let* ((ctp (congruence-pf-type-real ctx (dbshift-type-n 1 (dpi-dom tp)) 0 #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1)) #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))))
		  (a1 (dbsubst-type (dpi-dom tp) f1 sub1))
		  (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2)))
		  (pftrm
		   (congruence-make-equation-pf-normal
		    (ctx-cons (dpi-dom tp) ctx0)
		    (ctx-cons ctp (ctx-cons b1 (ctx-cons a1 ctx)))
		    (dpi-cod tp)
		    (gen-lam-body trm1)
		    (gen-lam-body trm2)
		    #'identity (cons 2 (cons #'(lambda (i) (+ 3 (funcall f1 i))) sub1))
		    #'identity (cons 1 (cons #'(lambda (i) (+ 3 (funcall f2 i))) sub2))
		    #'identity (cons 0 (cons #'(lambda (i) (+ 3 (funcall f3 i))) sub3))
		    (1+ n) (esh1 eqns) (esh1 equivs)
		    )))
	     (if pftrm
		 (lam (lam (lam pftrm)))
	       nil))))
	((dclass-p tp)
	 (congruence-make-equation-pf-normal ctx0 ctx (obj) (gen-pair-fst trm1) (gen-pair-fst trm2) f1 sub1 f2 sub2 f3 sub3 n eqns equivs))
	((obj-p tp)
	 (let ((trm1s (dbsubst trm1 f1 sub1))
	       (trm2s (dbsubst trm2 f2 sub2)))
	   (if (ctx-terms-eq-type ctx trm1s trm2s (obj))
	       (app '|eqI| trm2s)
	   (if (ctx-terms-eq-type ctx0 trm1 trm2 (obj))
	       (congruence-make-equation-pf-1-extr ctx0 ctx trm1 f1 sub1 f2 sub2 f3 sub3 n)
	     (let ((done nil)
		   (h1 (term-extr-head trm1s))
		   (h2 (term-extr-head trm2s)))
	     ; check for defn here
	       (when (and (symbolp h1) (abbrevname-p h1))
		 (let* ((h1eqpf (app-n (intern (format nil "~d#Eq" h1)) (term-extr-args trm1s)))
			(h1eq (ctx-extract-type ctx h1eqpf)))
		   (when (and h1eq (pf-p h1eq)
			      (app-p (pf-prop h1eq))
			      (app-p (app-func (pf-prop h1eq)))
			      (eq (app-func (app-func (pf-prop h1eq))) '|eq|)
			      (ctx-terms-eq-type ctx trm1s (app-arg (app-func (pf-prop h1eq))) (obj))
			      (ctx-terms-eq-type ctx trm2s (app-arg (pf-prop h1eq)) (obj)))
		     (setq done h1eqpf)))
		 (unless done
		   (let* ((h1eqpf (app-n (intern (format nil "~d#Eq" h1)) (term-extr-args trm1)))
			  (h1eq (ctx-extract-type ctx0 h1eqpf)))
		     (when (and h1eq (pf-p h1eq)
				(app-p (pf-prop h1eq))
				(app-p (app-func (pf-prop h1eq)))
				(eq (app-func (app-func (pf-prop h1eq))) '|eq|)
				(ctx-terms-eq-type ctx0 trm1 (app-arg (app-func (pf-prop h1eq))) (obj))
				(ctx-terms-eq-type ctx0 trm2 (app-arg (pf-prop h1eq)) (obj)))
		       (let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (obj) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
			 (when pftrm1
			   (setq done
				 (app-n '|transeq|
					(list trm1s
					      (dbsubst trm1 f2 sub2)
					      trm2s
					      pftrm1
					      (dbsubst h1eqpf f2 sub2))
					))))))))
	       (when (and (not done) (symbolp h2) (abbrevname-p h2))
		 (let* ((h2eqpf (app-n (intern (format nil "~d#Eq" h2)) (term-extr-args trm2s)))
			(h2eq (ctx-extract-type ctx h2eqpf)))
		   (when (and h2eq (pf-p h2eq)
			      (app-p (pf-prop h2eq))
			      (app-p (app-func (pf-prop h2eq)))
			      (eq (app-func (app-func (pf-prop h2eq))) '|eq|)
			      (ctx-terms-eq-type ctx trm2s (app-arg (app-func (pf-prop h2eq))) (obj))
			      (ctx-terms-eq-type ctx trm1s (app-arg (pf-prop h2eq)) (obj)))
		     (setq done (app-n '|symeq| (list trm2s trm1s h2eqpf)))))
		 (unless done
		   (let* ((h2eqpf (app-n (intern (format nil "~d#Eq" h2)) (term-extr-args trm2)))
			  (h2eq (ctx-extract-type ctx0 h2eqpf)))
		     (when (and h2eq (pf-p h2eq)
				(app-p (pf-prop h2eq))
				(app-p (app-func (pf-prop h2eq)))
				(eq (app-func (app-func (pf-prop h2eq))) '|eq|)
				(ctx-terms-eq-type ctx0 trm2 (app-arg (app-func (pf-prop h2eq))) (obj))
				(ctx-terms-eq-type ctx0 trm1 (app-arg (pf-prop h2eq)) (obj)))
		       (let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (obj) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
			 (when pftrm1
			   (setq done
				 (app-n '|symtrans1eq|
					(list trm1s
					      (dbsubst trm1 f2 sub2)
					      trm2s
					      pftrm1
					      (dbsubst h2eqpf f2 sub2))
					))))))))
	       ; check for beta/eta
	       (unless done
		 (cond ((and (fst-p trm1) (beta2-declared-p) (ibeta2-redex-p ctx0 (fst-arg trm1))
			     (ctx-terms-eq-type ctx0
						(normalize
						 (fst (app (app-arg (fst-arg (gen-pair-fst (app-arg (app-func (fst-arg trm1))))))
							   (app-arg (fst-arg trm1)))))
						trm2
						(obj)))
			(let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (obj) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
			  (when pftrm1
			    (let ((trm12 (dbsubst trm1 f2 sub2)))
			      (setq done
				    (app-n '|transeq|
					   (list trm1s trm12 trm2s pftrm1
						 (app-n '|beta2|
							(list
							 (app-arg (app-func (app-func (app-func (fst-arg trm12)))))
							 (app-arg (app-func (app-func (fst-arg trm12))))
							 (app-arg (fst-arg (gen-pair-fst (app-arg (app-func (fst-arg trm12))))))
							 (app-arg (fst-arg trm12)))))))))))
		       ((and (fst-p trm2) (beta2-declared-p) (ibeta2-redex-p ctx0 (fst-arg trm2))
			     (ctx-terms-eq-type ctx0
						(normalize
						 (fst (app (app-arg (fst-arg (gen-pair-fst (app-arg (app-func (fst-arg trm2))))))
							   (app-arg (fst-arg trm2)))))
						trm1
						(obj)))
			(let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (obj) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
			  (when pftrm1
			    (let ((trm12 (dbsubst trm1 f2 sub2)))
			      (setq done
				    (app-n '|symtrans1eq|
					   (list trm1s trm12 trm2s pftrm1
						 (app-n '|beta2|
							(list
							 (app-arg (app-func (app-func (app-func (fst-arg trm2s)))))
							 (app-arg (app-func (app-func (fst-arg trm2s))))
							 (app-arg (fst-arg (gen-pair-fst (app-arg (app-func (fst-arg trm2s))))))
							 (app-arg (fst-arg trm2s)))))))))))
		       ((and (fst-p trm1) (eta2-declared-p)
			     (ieta2-redex-p ctx0 (fst-arg trm1))
			     (ctx-terms-eq-type ctx0
						(normalize
						 (fst 
						  (dbshift-n -1
							     (app-arg (app-func (fst-arg (gen-pair-fst (gen-lam-body (app-arg (fst-arg trm1))))))))))
						trm2
						(obj)))
			(let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (obj) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
			  (when pftrm1
;			    (unless (ctx-term-type-p ctx pftrm1 (pf (app (app '|eq| trm1s) (dbsubst trm1 f2 sub2))))
;			      (setq *trm1* trm1 *f1* f1 *sub1* sub1 *f2* f2 *sub2* sub2 *f3* f3 *sub3* sub3 *n* n *ctx0* ctx0 *ctx* ctx)
;			      (break))
			    (let ((trm12 (dbsubst trm1 f2 sub2)))
			      (setq done
				    (app-n '|transeq|
					   (list trm1s trm12 trm2s pftrm1
						 (app-n '|eta2|
							(list
							 (app-arg (app-func (app-func (fst-arg trm12))))
							 (app-arg (app-func (fst-arg trm12)))
							 (normalize
							  (dbshift-n -1
								     (app-arg (app-func (fst-arg (gen-pair-fst (gen-lam-body (app-arg (fst-arg trm12))))))))))
							))))))))
		       ((and (fst-p trm2) (eta2-declared-p)
			     (ieta2-redex-p ctx0 (fst-arg trm2))
			     (ctx-terms-eq-type ctx0
						(normalize
						 (fst 
						  (dbshift-n -1
							     (app-arg (app-func (fst-arg (gen-pair-fst (gen-lam-body (app-arg (fst-arg trm2))))))))))
						trm1
						(obj)))
			(let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (obj) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
			  (when pftrm1
;			    (unless (ctx-term-type-p ctx pftrm1 (pf (app (app '|eq| trm1s) (dbsubst trm1 f2 sub2))))
;			      (setq *trm1* trm1 *f1* f1 *sub1* sub1 *f2* f2 *sub2* sub2 *f3* f3 *sub3* sub3 *n* n *ctx0* ctx0 *ctx* ctx)
;			      (break))
						     
			    (let ((trm12 (dbsubst trm1 f2 sub2)))
			      (setq done
				    (app-n '|symtrans1eq|
					   (list trm1s trm12 trm2s pftrm1
						 (app-n '|eta2|
							(list
							 (app-arg (app-func (app-func (fst-arg trm2s))))
							 (app-arg (app-func (fst-arg trm2s)))
							 (normalize
							  (dbshift-n -1
								     (app-arg (app-func (fst-arg (gen-pair-fst (gen-lam-body (app-arg (fst-arg trm2s))))))))))))))))))))
	       (when (and done (not (ctx-extract-type ctx (normalize done))))
		 (setq *done* done *trm1* trm1 *trm2* trm2 *f1* f1 *sub1* sub1 *f2* f2 *sub2* sub2 *f3* f3 *sub3* sub3 *n* n *ctx0* ctx0 *ctx* ctx)
		 (break))
	       (do ((el eqns (cdr el)))
		   ((or done (null el))
		    (or (normalize done)
			(congruence-make-equation-pf-extr ctx0 ctx trm1 trm2 f1 sub1 f2 sub2 f3 sub3 n eqns equivs)))
		   (let ((pftrm (caar el))
			 (lft (cadar el))
			 (rght (caddar el)))
		     (cond ((and (ctx-terms-eq-type ctx0 trm1 lft (obj))
				 (ctx-terms-eq-type ctx0 trm2 rght (obj)))
			    (if (ctx-terms-eq-type ctx trm1s (dbsubst trm1 f2 sub2) (obj))
				(setq done (dbsubst pftrm f2 sub2))
			      (let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (obj) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
				(if pftrm1
				    (setq done
					  (app-n '|transeq|
						 (list trm1s
						       (dbsubst trm1 f2 sub2)
						       trm2s
						       pftrm1
						       (dbsubst pftrm f2 sub2)) ; 1, 2 or 3 should work here
						 ))
				  nil))))
			   ((and (ctx-terms-eq-type ctx0 trm1 rght (obj))
				 (ctx-terms-eq-type ctx0 trm2 lft (obj)))
			    (if (ctx-terms-eq-type ctx trm1s (dbsubst trm1 f2 sub2) (obj))
				(setq done (app-n '|symeq| (list trm2s trm1s (dbsubst pftrm f2 sub2))))
			      (let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (obj) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
				(if pftrm1
				    (setq done
					  (app-n '|symtrans1eq|
						 (list trm1s
						       (dbsubst trm1 f2 sub2)
						       trm2s
						       pftrm1
						       (dbsubst pftrm f2 sub2)) ; 1, 2 or 3 should work here
						 ))
				  nil))))
			   (t nil)))))))))
	((prop-p tp)
	 (let ((trm1s (dbsubst trm1 f1 sub1))
	       (trm2s (dbsubst trm2 f2 sub2))
	       (done nil))
	   (if (ctx-terms-eq-type ctx trm1s trm2s (prop))
	       (app '|reflequiv| trm2s)
	   (if (ctx-terms-eq-type ctx0 trm1 trm2 (prop))
	       (congruence-make-equation-pf-1-extr ctx0 ctx trm1 f1 sub1 f2 sub2 f3 sub3 n)
	     ; check for defn here
	     (let ((h1 (term-extr-head trm1s))
		   (h2 (term-extr-head trm2s)))
	       (when (and (symbolp h1) (abbrevname-p h1))
		 (let* ((h1eqpf (app-n (intern (format nil "~d#Eq" h1)) (term-extr-args trm1s)))
			(h1eq (ctx-extract-type ctx h1eqpf)))
		   (when (and h1eq (pf-p h1eq)
			      (app-p (pf-prop h1eq))
			      (app-p (app-func (pf-prop h1eq)))
			      (eq (app-func (app-func (pf-prop h1eq))) '|equiv|)
			      (ctx-terms-eq-type ctx trm1s (app-arg (app-func (pf-prop h1eq))) (prop))
			      (ctx-terms-eq-type ctx trm2s (app-arg (pf-prop h1eq)) (prop)))
		     (setq done h1eqpf)))
		 (unless done
		   (let* ((h1eqpf (app-n (intern (format nil "~d#Eq" h1)) (term-extr-args trm1)))
			  (h1eq (ctx-extract-type ctx0 h1eqpf)))
		     (when (and h1eq (pf-p h1eq)
				(app-p (pf-prop h1eq))
				(app-p (app-func (pf-prop h1eq)))
				(eq (app-func (app-func (pf-prop h1eq))) '|equiv|)
				(ctx-terms-eq-type ctx0 trm1 (app-arg (app-func (pf-prop h1eq))) (prop))
				(ctx-terms-eq-type ctx0 trm2 (app-arg (pf-prop h1eq)) (prop)))
		       (let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (prop) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
			 (when pftrm1
			   (setq done
				 (app-n '|transequiv|
					(list trm1s
					      (dbsubst trm1 f2 sub2)
					      trm2s
					      pftrm1
					      (dbsubst h1eqpf f2 sub2))
					))))))))
	       (when (and (not done) (symbolp h2) (abbrevname-p h2))
		 (let* ((h2eqpf (app-n (intern (format nil "~d#Eq" h2)) (term-extr-args trm2s)))
			(h2eq (ctx-extract-type ctx h2eqpf)))
		   (when (and h2eq (pf-p h2eq)
			      (app-p (pf-prop h2eq))
			      (app-p (app-func (pf-prop h2eq)))
			      (eq (app-func (app-func (pf-prop h2eq))) '|equiv|)
			      (ctx-terms-eq-type ctx trm2s (app-arg (app-func (pf-prop h2eq))) (prop))
			      (ctx-terms-eq-type ctx trm1s (app-arg (pf-prop h2eq)) (prop)))
		     (setq done (app-n '|symequiv| (list trm2s trm1s h2eqpf)))))
		 (unless done
		   (let* ((h2eqpf (app-n (intern (format nil "~d#Eq" h2)) (term-extr-args trm2)))
			  (h2eq (ctx-extract-type ctx0 h2eqpf)))
		     (when (and h2eq (pf-p h2eq)
				(app-p (pf-prop h2eq))
				(app-p (app-func (pf-prop h2eq)))
				(eq (app-func (app-func (pf-prop h2eq))) '|equiv|)
				(ctx-terms-eq-type ctx0 trm2 (app-arg (app-func (pf-prop h2eq))) (prop))
				(ctx-terms-eq-type ctx0 trm1 (app-arg (pf-prop h2eq)) (prop)))
		       (let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (prop) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
			 (when pftrm1
			   (setq done
				 (app-n '|symtrans1equiv|
					(list trm1s
					      (dbsubst trm1 f2 sub2)
					      trm2s
					      pftrm1
					      (dbsubst h2eqpf f2 sub2))
					))))))))
	       ; check for setbeta
	       (unless done
		 (cond ((and (setbeta-declared-p)
			     (setbeta-redex-p ctx0 trm1)
			     (ctx-terms-eq-type ctx0
						(setbeta-reduce trm1)
						trm2
						(prop)))
			(let ((pftrm1 (congruence-make-equation-pf-1-normal
				       ctx0 ctx (prop) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
			  (when pftrm1
			    (let ((trm12 (dbsubst trm1 f2 sub2)))
			      (setq done
				    (app-n '|transequiv|
					   (list trm1s trm12 trm2s pftrm1
						 (app-l '|setbeta|
							(app-arg (app-func (app-arg (app-func trm12)))) ; bounding set
							(app-arg (app-arg (app-func trm12))) ; phi (body)
							(fst-arg (app-arg trm12)) ; (typed) elt
							))))))))
		       ((and (setbeta-declared-p)
			     (setbeta-redex-p ctx0 trm2)
			     (ctx-terms-eq-type ctx0
						trm1
						(setbeta-reduce trm2)
						(prop)))
			(let ((pftrm1 (congruence-make-equation-pf-1-normal
				       ctx0 ctx (prop) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
			  (when pftrm1
			    (let ((trm12 (dbsubst trm1 f2 sub2)))
			      (setq done
				    (app-n '|symtrans1equiv|
					   (list trm1s trm12 trm2s pftrm1
						 (app-l '|setbeta|
							(app-arg (app-func (app-arg (app-func trm2s)))) ; bounding set
							(app-arg (app-arg (app-func trm2s))) ; phi (body)
							(fst-arg (app-arg trm2s)) ; (typed) elt
							))))))))))
	       (do ((el equivs (cdr el)))
		   ((or done (null el))
		    (or (normalize done)
			(congruence-make-equation-pf-extr ctx0 ctx trm1 trm2 f1 sub1 f2 sub2 f3 sub3 n eqns equivs)))
		   (let ((pftrm (caar el))
			 (lft (cadar el))
			 (rght (caddar el)))
		     (cond ((and (ctx-terms-eq-type ctx0 trm1 lft (prop))
				 (ctx-terms-eq-type ctx0 trm2 rght (prop)))
			    (if (ctx-terms-eq-type ctx trm1s (dbsubst trm1 f2 sub2) (prop))
				(setq done (dbsubst pftrm f2 sub2))
			      (let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (prop) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
				(if pftrm1
				    (setq done
					  (app-n '|transequiv|
						 (list trm1s
						       (dbsubst trm1 f2 sub2)
						       trm2s
						       pftrm1
						       (dbsubst pftrm f2 sub2))
						 ))
				  nil))))
			   ((and (ctx-terms-eq-type ctx0 trm1 rght (prop))
				 (ctx-terms-eq-type ctx0 trm2 lft (prop)))
			    (if (ctx-terms-eq-type ctx trm1s (dbsubst trm1 f2 sub2) (prop))
				(setq done (app-n '|symequiv| (list trm2s trm1s (dbsubst pftrm f2 sub2))))
			      (let ((pftrm1 (congruence-make-equation-pf-1-normal ctx0 ctx (prop) trm1 f1 sub1 f2 sub2 f3 sub3 n)))
				(if pftrm1
				    (setq done
					  (app-n '|symtrans1equiv|
						 (list trm1s
						       (dbsubst trm1 f2 sub2)
						       trm2s
						       pftrm1
						       (dbsubst pftrm f2 sub2)) ; 1, 2 or 3 should work here
						 ))
				  nil
				  ))))
			   (t nil)))))))))
	(t nil)))

(defun congruence-make-equation-pf-extr (ctx0 ctx trm1 trm2 f1 sub1 f2 sub2 f3 sub3 n eqns equivs)
  (cond ((and (app-p trm1) (app-p trm2))
	 (multiple-value-bind
	  (ctrm ftp)
	  (congruence-make-equation-pf-extr ctx0 ctx (app-func trm1) (app-func trm2) f1 sub1 f2 sub2 f3 sub3 n eqns equivs)
	  (if (and ctrm ftp (dpi-p ftp))
	      (if (dtype-returns-pf-p (dpi-dom ftp))
		  (values (normalize
			   (app (app ctrm
				     (dbsubst (app-arg trm1) f1 sub1))
				(dbsubst (app-arg trm2) f2 sub2)))
			  (normalize-type (dbsubst-type-0 (dpi-cod ftp) (app-arg trm1))))
		(let ((ctrm2 (congruence-make-equation-pf-normal ctx0 ctx (dpi-dom ftp) (app-arg trm1) (app-arg trm2) f1 sub1 f2 sub2 f3 sub3 n eqns equivs)))
		  (if ctrm2
		      (values (normalize
			       (app (app (app ctrm
					      (dbsubst (app-arg trm1) f1 sub1))
					 (dbsubst (app-arg trm2) f2 sub2))
				    ctrm2))
			      (normalize-type (dbsubst-type-0 (dpi-cod ftp) (app-arg trm1))))
		    nil))))))
	((and (fst-p trm1) (fst-p trm2))
	 (multiple-value-bind
	  (ctrm ftp)
	  (congruence-make-equation-pf-extr ctx0 ctx (fst-arg trm1) (fst-arg trm2) f1 sub1 f2 sub2 f3 sub3 n eqns equivs)
	  (if ctrm
	      (values ctrm (obj))
	    nil)))
	((and (numberp trm1) (equal trm1 trm2)) ; split on n
	 (if (< trm1 n)
	     (values (dbsubst trm1 f3 sub3)
		     (ctx-extract-type ctx0 trm1))
	   (let* ((tp (ctx-extract-type ctx0 trm1))
		  (dbeqpf (make-db-eq-pf ctx0 trm1 tp)))
	     (if dbeqpf
		 (values (dbsubst dbeqpf f1 sub1) (dbsubst-type tp f1 sub1))
	       nil))))
	((and (symbolp trm1) (equal trm1 trm2))
	 (let ((cc (auto-gen-name trm1 "Cong" nil)))
	   (if (and (get cc 'dbtype) (equal (get cc 'dbtype)
					    (congruence-pf-type (get trm1 'dbtype) trm1)))
	       (values cc (get trm1 'dbtype))
	     nil)))
	(t nil)))

(defun make-db-eq-pf (ctx trm tp)
  (cond ((obj-p tp) (app '|eqI| trm))
	((prop-p tp) (app '|reflequiv| trm))
	((dclass-p tp) (app '|eqI| (fst trm)))
	((dpi-p tp)
	 (let ((dom (dpi-dom tp))
	       (cod (dpi-cod tp)))
	   (cond ((and (obj-p dom) (prop-p cod))
;		  (push (list ctx trm tp) *c-problems*)
		  nil
		  )
		 ((and (obj-p dom) (dclass-p cod))
;		  (push (list ctx trm tp) *c-problems*)
		  nil
		  )
		 ((and (obj-p dom) (obj-p cod))
;		  (push (list ctx trm tp) *c-problems*)
		  nil
		  )
		 ((and (dclass-p dom) (prop-p cod))
		  (lam (lam (lam (app-n '|eqCE|
					(list
					 (dbshift-n 3 (dclass-pred dom))
					 2 1
					 (lam (app-l '|equiv| (app (dbshift-n 4 trm) 3) (app (dbshift-n 4 trm) 0)))
					 0
					 (app '|reflequiv| (app (dbshift-n 3 trm) 2))
					 ))))))
		 ((and (dclass-p dom) (dclass-p cod))
		  (lam (lam (lam (app-n '|eqCE|
					(list
					 (dbshift-n 3 (dclass-pred dom))
					 2 1
					 (lam (app-l '|eq| (fst (app (dbshift-n 4 trm) 3)) (fst (app (dbshift-n 4 trm) 0))))
					 0
					 (app '|eqI| (fst (app (dbshift-n 3 trm) 2)))
					 ))))))
		 ((and (dclass-p dom) (obj-p cod))
		  (lam (lam (lam (app-n '|eqCE|
					(list
					 (dbshift-n 3 (dclass-pred dom))
					 2 1
					 (lam (app-l '|eq| (app (dbshift-n 4 trm) 3) (app (dbshift-n 4 trm) 0)))
					 0
					 (app '|eqI| (app (dbshift-n 3 trm) 2))
					 ))))))
		 ((and (dclass-p dom) (dpi-p cod) (dclass-p (dpi-dom cod)) (prop-p (dpi-cod cod)))
		  (lam (lam (lam (lam (lam (lam
					    (app-l
					     '|eqCE|
					     (dbshift-n 5 (dclass-pred (dpi-dom cod)))
					     2 1
					     (lam (app-l '|equiv|
							 (app-l (dbshift-n 7 trm) 6 3)
							 (app-l (dbshift-n 7 trm) 5 0)))
					     0
					     (app-l
					      '|eqCE|
					      (dbshift-n 6 (dclass-pred dom))
					      5 4
					      (lam (app-l '|equiv|
							  (app-l (dbshift-n 7 trm) 6 3)
							  (app-l (dbshift-n 7 trm) 0 3)))
					      3
					      (app-l '|reflequiv| (app-l (dbshift-n 6 trm) 5 2)))))))))))
		 (t
;		  (push (list ctx trm tp) *c-problems*)
		  nil))))
	(t
;	 (push (list ctx trm tp) *c-problems*)
	 nil)))

(defun congruence-make-equation-pf-1-normal (ctx0 ctx tp trm1 f1 sub1 f2 sub2 f3 sub3 n)
  (cond ((dpi-p tp)
	 (if (dtype-returns-pf-p (dpi-dom tp))
	     (let* ((a1 (dbsubst-type (dpi-dom tp) f1 sub1))
		    (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2)))
		    (pftrm
		     (congruence-make-equation-pf-1-normal
		      (ctx-cons (dpi-dom tp) ctx0)
		      (ctx-cons b1 (ctx-cons a1 ctx))
		      (dpi-cod tp)
		      (gen-lam-body trm1)
		      #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1))
		      #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))
		      #'identity (cons 0 ; 0 is a dummy value
				       (cons #'(lambda (i) (+ 2 (funcall f3 i))) sub3))
		      (1+ n)
		      )))
	       (if pftrm
		   (lam (lam pftrm))
		 nil))
	   (let* ((ctp (congruence-pf-type-real ctx (dbshift-type-n 1 (dpi-dom tp)) 0 #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1)) #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))))
		  (a1 (dbsubst-type (dpi-dom tp) f1 sub1))
		  (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2)))
		  (pftrm
		   (congruence-make-equation-pf-1-normal
		    (ctx-cons (dpi-dom tp) ctx0)
		    (ctx-cons ctp (ctx-cons b1 (ctx-cons a1 ctx)))
		    (dpi-cod tp)
		    (gen-lam-body trm1)
		    #'identity (cons 2 (cons #'(lambda (i) (+ 3 (funcall f1 i))) sub1))
		    #'identity (cons 1 (cons #'(lambda (i) (+ 3 (funcall f2 i))) sub2))
		    #'identity (cons 0 (cons #'(lambda (i) (+ 3 (funcall f3 i))) sub3))
		    (1+ n)
		    )))
	     (if pftrm
		 (lam (lam (lam pftrm)))
	       nil))))
	((dclass-p tp)
	 (congruence-make-equation-pf-1-normal ctx0 ctx (obj) (gen-pair-fst trm1) f1 sub1 f2 sub2 f3 sub3 n))
	((obj-p tp)
	 (let ((trm1s (dbsubst trm1 f1 sub1))
	       (trm2s (dbsubst trm1 f2 sub2)))
	   (if (ctx-terms-eq-type ctx trm1s trm2s (obj))
	       (app '|eqI| trm2s)
	     (congruence-make-equation-pf-1-extr ctx0 ctx trm1 f1 sub1 f2 sub2 f3 sub3 n))))
	((prop-p tp)
	 (let ((trm1s (dbsubst trm1 f1 sub1))
	       (trm2s (dbsubst trm1 f2 sub2))
	       (done nil))
	   (if (ctx-terms-eq-type ctx trm1s trm2s (prop))
	       (app '|reflequiv| trm2s)
	     (congruence-make-equation-pf-1-extr ctx0 ctx trm1 f1 sub1 f2 sub2 f3 sub3 n))))
	(t nil)))

(defun congruence-make-equation-pf-1-extr (ctx0 ctx trm1 f1 sub1 f2 sub2 f3 sub3 n)
  (cond ((app-p trm1)
	 (multiple-value-bind
	  (ctrm ftp)
	  (congruence-make-equation-pf-1-extr ctx0 ctx (app-func trm1) f1 sub1 f2 sub2 f3 sub3 n)
	  (if (and ctrm ftp (dpi-p ftp))
	      (if (dtype-returns-pf-p (dpi-dom ftp))
		  (values (app (app ctrm
				    (dbsubst (app-arg trm1) f1 sub1))
			       (dbsubst (app-arg trm1) f2 sub2))
			  (normalize-type (dbsubst-type-0 (dpi-cod ftp) (app-arg trm1))))
		(let ((ctrm2 (congruence-make-equation-pf-1-normal ctx0 ctx (dpi-dom ftp) (app-arg trm1) f1 sub1 f2 sub2 f3 sub3 n)))
		  (if ctrm2
		      (values (app (app (app ctrm
					     (dbsubst (app-arg trm1) f1 sub1))
					(dbsubst (app-arg trm1) f2 sub2))
				   ctrm2)
			      (normalize-type (dbsubst-type-0 (dpi-cod ftp) (app-arg trm1))))
		    nil))))))
	((fst-p trm1)
	 (multiple-value-bind
	  (ctrm ftp)
	  (congruence-make-equation-pf-1-extr ctx0 ctx (fst-arg trm1) f1 sub1 f2 sub2 f3 sub3 n)
	  (if ctrm
	      (values ctrm (obj))
	    nil)))
	((numberp trm1)
	 (if (< trm1 n)
	     (values (dbsubst trm1 f3 sub3)
		     (ctx-extract-type ctx0 trm1))
	   (let* ((tp (ctx-extract-type ctx0 trm1))
		  (dbeqpf (make-db-eq-pf ctx0 trm1 tp)))
	     (if dbeqpf
		 (values (dbsubst dbeqpf f1 sub1) (dbsubst-type tp f1 sub1))
	       nil))))
	((symbolp trm1)
	 (let ((cc (auto-gen-name trm1 "Cong" nil)))
	   (if (and (get cc 'dbtype) (equal (get cc 'dbtype)
					    (congruence-pf-type (get trm1 'dbtype) trm1)))
	       (values cc (get trm1 'dbtype))
	     nil)))
	(t nil)))

(defun esh1 (eqns)
  (mapcar #'(lambda (x)
	      (list (dbshift-n 1 (car x))
		    (dbshift-n 1 (cadr x))
		    (dbshift-n 1 (caddr x))))
	  eqns))

(defun reduce-term (ctx trm tp)
  (catch 'reduce-fail
    (reduce-term-1 ctx trm tp)))

(defun reduce-term-1 (ctx trm tp)
  (if (dtype-returns-pf-p tp) ; should not have been called in this case
      nil
    (reduce-term-normal ctx ctx tp trm
			#'identity 'ID #'identity 'ID #'identity 'ID
			0)))

; ; n gives boundary between shared original ctx and local context separated by f's and sub's
; (defun reduce-term-normal (ctx0 ctx tp trm1 f1 sub1 f2 sub2 f3 sub3 n)
;   (cond ((dpi-p tp)
; 	 (if (dtype-returns-pf-p (dpi-dom tp))
; 	     (let* ((a1 (dbsubst-type (dpi-dom tp) f1 sub1))
; 		    (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2))))
; 	       (multiple-value-bind
; 		(trm2 pftrm)
; 		(reduce-term-normal
; 		 (ctx-cons (dpi-dom tp) ctx0)
; 		 (ctx-cons b1 (ctx-cons a1 ctx))
; 		 (dpi-cod tp)
; 		 (gen-lam-body trm1)
; 		 #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1))
; 		 #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))
; 		 #'identity (cons 0 ; 0 is a dummy value
; 				  (cons #'(lambda (i) (+ 2 (funcall f3 i))) sub3))
; 		 (1+ n) (esh1 eqns) (esh1 equivs)
; 		 ))
; 	       (values (lam trm2)
; 		       (lam (lam pftrm))))
; 	   (let* ((ctp (congruence-pf-type-real ctx (dbshift-type-n 1 (dpi-dom tp)) 0 #'identity (cons 1 (cons #'(lambda (i) (+ 2 (funcall f1 i))) sub1)) #'identity (cons 0 (cons #'(lambda (i) (+ 2 (funcall f2 i))) sub2))))
; 		  (a1 (dbsubst-type (dpi-dom tp) f1 sub1))
; 		  (b1 (dbshift-type-n 1 (dbsubst-type (dpi-dom tp) f2 sub2))))
; 	     (multiple-value-bind
; 	      (trm2 pftrm)
; 	      (reduce-term-normal
; 	       (ctx-cons (dpi-dom tp) ctx0)
; 	       (ctx-cons ctp (ctx-cons b1 (ctx-cons a1 ctx)))
; 	       (dpi-cod tp)
; 	       (gen-lam-body trm1)
; 	       #'identity (cons 2 (cons #'(lambda (i) (+ 3 (funcall f1 i))) sub1))
; 	       #'identity (cons 1 (cons #'(lambda (i) (+ 3 (funcall f2 i))) sub2))
; 	       #'identity (cons 0 (cons #'(lambda (i) (+ 3 (funcall f3 i))) sub3))
; 	       (1+ n) (esh1 eqns) (esh1 equivs)
; 	       )
; 	      (values (lam trm2)
; 		      (lam (lam (lam pftrm))))))))
; 	((dclass-p tp)
; 	 (multiple-value-bind
; 	  (trm2 pftrm)
; 	  (reduce-term-normal ctx0 ctx (obj) (gen-pair-fst trm1) f1 sub1 f2 sub2 f3 sub3 n eqns equivs)
; 	  (let* ((phi (dclass-pred tp))
; 		 (prop1 (normalize (app phi (gen-pair-fst trm1))))
; 		 (prop2 (normalize (app phi trm2))))
; 	    (if (heq prop1 prop2)
; 		(values (pair trm2 (gen-pair-snd trm1))
; 			pftrm)
; 	      (let ((z (congruence-make-equation-pf ctx prop1 prop2 (prop))))
; 		(if z
; 		    (values (pair trm2 (app-n '|equivEimp1| (list prop1 prop2 z (gen-pair-snd trm1))))
; 			    pftrm)
; 		  (throw 'reduce-fail)))))))
; 	((obj-p tp)
; 	 (let ((trm1s (dbsubst trm1 f1 sub1))
; 	       (trm2s (dbsubst trm2 f2 sub2)))
; 	   (if (ctx-terms-eq-type ctx trm1s trm2s (obj))
; 	       (app '|eqI| trm2s)
; 	     (let ((done nil)
; 		   (h1 (term-extr-head trm1s))
; 		   (h2 (term-extr-head trm2s)))
; 	     ; check for defn here
; 	       (when (and (symbolp h1) (abbrevname-p h1))
; 		 (let* ((h1eqpf (app-n (intern (format nil "~d#Eq" h1)) (term-extr-args trm1s)))
; 			(h1eq (ctx-extract-type ctx h1eqpf)))
; 		   (when (and h1eq (pf-p h1eq)
; 			      (app-p (pf-prop h1eq))
; 			      (app-p (app-func (pf-prop h1eq)))
; 			      (eq (app-func (app-func (pf-prop h1eq))) '|eq|)
; 			      (ctx-terms-eq-type ctx trm1s (app-arg (app-func (pf-prop h1eq))) (obj))
; 			      (ctx-terms-eq-type ctx trm2s (app-arg (pf-prop h1eq)) (obj)))
; 		     (setq done h1eqpf))))
; 	       (when (and (not done) (symbolp h2) (abbrevname-p h2))
; 		 (let* ((h2eqpf (app-n (intern (format nil "~d#Eq" h2)) (term-extr-args trm2s)))
; 			(h2eq (ctx-extract-type ctx h2eqpf)))
; 		   (when (and h2eq (pf-p h2eq)
; 			      (app-p (pf-prop h2eq))
; 			      (app-p (app-func (pf-prop h2eq)))
; 			      (eq (app-func (app-func (pf-prop h2eq))) '|eq|)
; 			      (ctx-terms-eq-type ctx trm2s (app-arg (app-func (pf-prop h2eq))) (obj))
; 			      (ctx-terms-eq-type ctx trm1s (app-arg (pf-prop h2eq)) (obj)))
; 		     (setq done (app-n '|symeq| (list trm2s trm1s h2eqpf))))))
; 	       (do ((el eqns (cdr el)))
; 		   ((or done (null el))
; 		    (or done
; 			(reduce-term-extr ctx0 ctx trm1 trm2 f1 sub1 f2 sub2 f3 sub3 n eqns equivs)))
; 		   (let ((pftrm (caar el))
; 			 (lft (cadar el))
; 			 (rght (caddar el)))
; 		     (cond ((and (ctx-terms-eq-type ctx trm1s lft (obj))
; 				 (ctx-terms-eq-type ctx trm2s rght (obj)))
; 			    (setq done pftrm)
; 			    )
; 			   ((and (ctx-terms-eq-type ctx trm1s rght (obj))
; 				 (ctx-terms-eq-type ctx trm2s lft (obj)))
; 			    (setq done (app-n '|symeq| (list lft rght pftrm)))
; 			    )
; 			   (t nil))))))))
; 	((prop-p tp)
; 	 (let ((trm1s (dbsubst trm1 f1 sub1))
; 	       (trm2s (dbsubst trm2 f2 sub2))
; 	       (done nil))
; 	   (if (ctx-terms-eq-type ctx trm1s trm2s (prop))
; 	       (app '|reflequiv| trm2s)
; 	     ; check for defn here
; 	     (let ((h1 (term-extr-head trm1s))
; 		   (h2 (term-extr-head trm2s)))
; 	       (when (and (symbolp h1) (abbrevname-p h1))
; 		 (let* ((h1eqpf (app-n (intern (format nil "~d#Eq" h1)) (term-extr-args trm1s)))
; 			(h1eq (ctx-extract-type ctx h1eqpf)))
; 		   (when (and h1eq (pf-p h1eq)
; 			      (app-p (pf-prop h1eq))
; 			      (app-p (app-func (pf-prop h1eq)))
; 			      (eq (app-func (app-func (pf-prop h1eq))) '|equiv|)
; 			      (ctx-terms-eq-type ctx trm1s (app-arg (app-func (pf-prop h1eq))) (prop))
; 			      (ctx-terms-eq-type ctx trm2s (app-arg (pf-prop h1eq)) (prop)))
; 		     (setq done h1eqpf))))
; 	       (when (and (not done) (symbolp h2) (abbrevname-p h2))
; 		 (let* ((h2eqpf (app-n (intern (format nil "~d#Eq" h2)) (term-extr-args trm2s)))
; 			(h2eq (ctx-extract-type ctx h2eqpf)))
; 		   (when (and h2eq (pf-p h2eq)
; 			      (app-p (pf-prop h2eq))
; 			      (app-p (app-func (pf-prop h2eq)))
; 			      (eq (app-func (app-func (pf-prop h2eq))) '|equiv|)
; 			      (ctx-terms-eq-type ctx trm2s (app-arg (app-func (pf-prop h2eq))) (prop))
; 			      (ctx-terms-eq-type ctx trm1s (app-arg (pf-prop h2eq)) (prop)))
; 		     (setq done (app-n '|symequiv| (list trm2s trm1s h2eqpf))))))
; 	       (do ((el equivs (cdr el)))
; 		   ((or done (null el))
; 		    (or done
; 			(reduce-term-extr ctx0 ctx trm1 trm2 f1 sub1 f2 sub2 f3 sub3 n eqns equivs)))
; 		   (let ((pftrm (caar el))
; 			 (lft (cadar el))
; 			 (rght (caddar el)))
; 		     (cond ((and (ctx-terms-eq-type ctx trm1s lft (obj))
; 				 (ctx-terms-eq-type ctx trm2s rght (obj)))
; 			    (setq done pftrm)
; 			    )
; 			   ((and (ctx-terms-eq-type ctx trm1s rght (obj))
; 				 (ctx-terms-eq-type ctx trm2s lft (obj)))
; 			    (setq done (app-n '|symequiv| (list lft rght pftrm)))
; 			    )
; 			   (t nil))))))))
; 	(t nil)))
; 
; (defun reduce-term-extr (ctx0 ctx trm1 trm2 f1 sub1 f2 sub2 f3 sub3 n eqns equivs)
;   (cond ((and (app-p trm1) (app-p trm2))
; 	 (multiple-value-bind
; 	  (ctrm ftp)
; 	  (reduce-term-extr ctx0 ctx (app-func trm1) (app-func trm2) f1 sub1 f2 sub2 f3 sub3 n eqns equivs)
; 	  (if (and ctrm ftp (dpi-p ftp))
; 	      (if (dtype-returns-pf-p (dpi-dom ftp))
; 		  (values (app (app ctrm
; 				    (dbsubst (app-arg trm1) f1 sub1))
; 			       (dbsubst (app-arg trm2) f2 sub2))
; 			  (normalize-type (dbsubst-type-0 (dpi-cod ftp) (app-arg trm1))))
; 		(let ((ctrm2 (reduce-term-normal ctx0 ctx (dpi-dom ftp) (app-arg trm1) (app-arg trm2) f1 sub1 f2 sub2 f3 sub3 n eqns equivs)))
; 		  (if ctrm2
; 		      (values (app (app (app ctrm
; 					     (dbsubst (app-arg trm1) f1 sub1))
; 					(dbsubst (app-arg trm2) f2 sub2))
; 				   ctrm2)
; 			      (normalize-type (dbsubst-type-0 (dpi-cod ftp) (app-arg trm1))))
; 		    nil))))))
; 	((and (fst-p trm1) (fst-p trm2))
; 	 (multiple-value-bind
; 	  (ctrm ftp)
; 	  (reduce-term-extr ctx0 ctx (fst-arg trm1) (fst-arg trm2) f1 sub1 f2 sub2 f3 sub3 n eqns equivs)
; 	  (if ctrm
; 	      (values ctrm (obj))
; 	    nil)))
; 	((and (numberp trm1) (equal trm1 trm2)) ; split on n
; 	 (if (< trm1 n)
; 	     (values (dbsubst trm1 f3 sub3)
; 		     (ctx-extract-type ctx0 trm1))
; 	   (let* ((tp (ctx-extract-type ctx0 trm1))
; 		  (dbeqpf nil)) ; (make-db-eq-pf ?)))
; 	     (if dbeqpf
; 		 (values dbeqpf tp)
; 	       nil))))
; 	((and (symbolp trm1) (equal trm1 trm2))
; 	 (let ((cc (auto-gen-name trm1 "Cong" nil)))
; 	   (if (and (get cc 'dbtype) (equal (get cc 'dbtype)
; 					    (congruence-pf-type (get trm1 'dbtype) trm1)))
; 	       (values cc (get trm1 'dbtype))
; 	     nil)))
; 	(t nil)))
; 

(defun equal-pf-type (tp trm1 trm2)
  (cond ((dpi-p tp)
	 (dpi (dpi-dom tp) (equal-pf-type (dpi-cod tp) (gen-lam-body trm1) (gen-lam-body trm2))))
	((dclass-p tp)
	 (pf (app (app '|eq| (fst trm1)) (fst trm2))))
	((obj-p tp)
	 (pf (app (app '|eq| trm1) trm2)))
	((prop-p tp)
	 (pf (app (app '|equiv| trm1) trm2)))
	(t (fail "equal-pf-type call with pf type"))))

(defun equal-pf-refl (tp trm)
  (cond ((dpi-p tp)
	 (lam (equal-pf-refl (dpi-cod tp) (gen-lam-body trm))))
	((dclass-p tp)
	 (app '|eqI| (fst trm)))
	((obj-p tp)
	 (app '|eqI| trm))
	((prop-p tp)
	 (app '|reflequiv| trm))
	(t (fail "equal-pf-type call with pf type"))))

(defun make-equal-pf (ctx trm1 trm2 tp &optional eqns equivs)
  (if (dtype-returns-pf-p tp)
      nil
    (make-equal-pf-1 ctx trm1 trm2 tp eqns equivs)))

(defun make-equal-pf-1 (ctx trm1 trm2 tp &optional eqns equivs)
  (if (ctx-terms-eq-type ctx trm1 trm2 tp)
      (equal-pf-refl tp trm1)
    (make-equal-pf-2 ctx trm1 trm2 tp eqns equivs)))

(defun make-equal-pf-2 (ctx trm1 trm2 tp &optional eqns equivs)
  (cond ((dpi-p tp)
	 (let ((pftrm (make-equal-pf-2 (ctx-cons (dpi-dom tp) ctx) (gen-lam-body trm1) (gen-lam-body trm2) (dpi-cod tp) (esh1 eqns) (esh1 equivs))))
	   (if pftrm
	       (lam pftrm)
	     nil)))
	((dclass-p tp)
	 (make-equal-pf-2 ctx (gen-pair-fst trm1) (gen-pair-fst trm2) (obj) eqns equivs))
	((obj-p tp)
	 (cond ((and (fst-p trm1) (beta2-declared-p) (ibeta2-redex-p ctx0 (fst-arg trm1))
		     (ctx-terms-eq-type ctx
					(normalize
					 (fst (app (app-arg (fst-arg (gen-pair-fst (app-arg (app-func (fst-arg trm1))))))
						   (app-arg (fst-arg trm1)))))
					trm2
					(obj)))
		(app-n '|beta2|
		       (list
			(app-arg (app-func (app-func (app-func (fst-arg trm1)))))
			(app-arg (app-func (app-func (fst-arg trm1))))
			(app-arg (fst-arg (gen-pair-fst (app-arg (app-func (fst-arg trm1))))))
			(app-arg (fst-arg trm1)))))
	       ((and (fst-p trm2) (beta2-declared-p) (ibeta2-redex-p ctx0 (fst-arg trm2))
		     (ctx-terms-eq-type ctx
					(normalize
					 (fst (app (app-arg (fst-arg (gen-pair-fst (app-arg (app-func (fst-arg trm2))))))
						   (app-arg (fst-arg trm2)))))
					trm1
					(obj)))
		(app-n '|beta2|
		       (list
			(app-arg (app-func (app-func (app-func (fst-arg trm2)))))
			(app-arg (app-func (app-func (fst-arg trm2))))
			(app-arg (fst-arg (gen-pair-fst (app-arg (app-func (fst-arg trm2))))))
			(app-arg (fst-arg trm2)))))
	       ((and (fst-p trm1) (eta2-declared-p)
		     (ieta2-redex-p ctx0 (fst-arg trm1))
		     (ctx-terms-eq-type ctx
					(normalize
					 (fst 
					  (dbshift-n -1
						     (app-arg (app-func (fst-arg (gen-pair-fst (gen-lam-body (app-arg (fst-arg trm1))))))))))
					trm2
					(obj)))
		(app-n '|eta2|
		       (list
			(app-arg (app-func (app-func (fst-arg trm1))))
			(app-arg (app-func (fst-arg trm1)))
			g)))
	       ((and (fst-p trm2) (eta2-declared-p)
		     (ieta2-redex-p ctx0 (fst-arg trm2))
		     (ctx-terms-eq-type ctx
					(normalize
					 (fst 
					  (dbshift-n -1
						     (app-arg (app-func (fst-arg (gen-pair-fst (gen-lam-body (app-arg (fst-arg trm2))))))))))
					trm1
					(obj)))
		(app-n '|eta2|
		       (list
			(app-arg (app-func (app-func (fst-arg trm2))))
			(app-arg (app-func (fst-arg trm2)))
			g)))
	       (t
		'?))) ; hmmm, unfinished
	((prop-p tp)
	 '?) ; hmmm, unfinished
	(t nil)))
	 
