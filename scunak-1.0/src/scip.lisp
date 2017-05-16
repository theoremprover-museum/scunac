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

; January 2006
; Chad E Brown

(defvar *scip-taskstack* nil)
(defvar *scip-tasks* nil)
(defvar *scip-theta* nil)
(defvar *scip-gevar* nil)
(defvar *scip-gtp* nil)
(defvar *scip-usable* nil)
(defvar *scip-fst-usable* nil)
(defvar *scip-snd-usable* nil)
(defvar *scip-defn-usable* nil)
(defvar *scip-eager-elims* t)
(defvar *scip-assnum* -1)
(defvar *scip-factnum* -1)

(defvar *scip-timestamp* -1)
(defvar *scip-sigma* nil)

(defvar *scip-lemmas* nil)

(defvar *scip-special-usable* nil)

(defvar *scip-pam-proof-file* "myproofs.pam")
(defvar *scip-lisp-proof-file* "myproofs.lisp")

(defun scip-initfn ()
  (let ((prefilenames (command-line-arg-several "-p"))
	(filenames (command-line-arg-several "-f"))
	(claimname (command-line-arg "-c"))
	(color (command-line-switch "-C"))
	(verb (command-line-switch "-v"))
	(verb2 (command-line-switch "-V")))
    (unless claimname
      (fail (format nil "scip must be given a claim name using -c")))
    (when verb
      (setq *verbose* 20))
    (when verb2
      (setq *verbose* 99))
    (unless color
      (setq *style* 'ascii))
    (setq *allow-constants* nil)
    (scunak-header "Welcome to SCIP, the Scunak Interactive Prover.")
    (dolist (prefilename prefilenames)
      (unless (probe-file prefilename)
	(setq prefilename (format nil "~d.lisp" prefilename))
	(unless (probe-file prefilename)
	  (fail (format nil "No file named ~d." prefilename))))
      (load prefilename))
    (dolist (filename filenames)
      (unless (probe-file filename)
	(fail (format nil "No file named ~d." filename)))
      (readinput1 filename))
    (let ((c (intern claimname)))
      (scip c))))

#+:allegro
(defun save-scip-image ()
  (set-fail-to-seriously-fail)
  (setq excl:*restart-app-function* 'scip-initfn)
  (excl:dumplisp :name (format nil "~d/allegro-scunak-scip.dxl" *dxldir*)))

#+:clisp
(defun save-scip-image ()
  (set-fail-to-seriously-fail)
  (setq system::*driver* #'scip-initfn)
  (ext:saveinitmem (format nil "~d/clisp-scunak-scip.mem" *dxldir*) :quiet t :init-function 'scip-initfn))

#+:cmu
(defun save-scip-image ()
  (set-fail-to-seriously-fail)
  (extensions:savelisp (format nil "~d/cmucl-scunak-scip" *dxldir*) :init-function 'scip-initfn
		       :print-herald nil))
  
(defun scip (c)
  (if (claimname-p c)
      (progn
	(setq *scip-lemmas* nil)
	(setq *scip-gevar* (intern-gensym))
	(setq *scip-gtp* (get c 'dbtype))
	(setf (get *scip-gevar* 'evar) t)
	(setf (get *scip-gevar* 'dbtype) *scip-gtp*) ; ok to assign the type since gtp has no evars
	(setq *scip-taskstack* nil)
	(setq *scip-tasks* (list (list *scip-gevar* *emptyctx* nil *scip-gtp* nil 'ID)))
	(setq *scip-theta* (acons *scip-gevar* *scip-gevar* nil))
	(setq *scip-assnum* -1)
	(setq *scip-factnum* -1)
	(setq *scip-usable* nil)
	(setq *scip-fst-usable* nil)
	(setq *scip-snd-usable* nil)
	(setq *scip-timestamp* (get c 'timestamp))
	(setq *scip-sigma* nil)
	(dolist (co *global-sigma*)
	  (when (< (get co 'timestamp) *scip-timestamp*)
	    (push co *scip-sigma*)
	    (when (member (get co 'returns) '(PF DCLASS))
	      (if (get co 'auto-gen)
		  (push co *scip-defn-usable*)
		(if (or (get co 'fo-unif-type) (get co 'fo-type))
		    (push co *scip-fst-usable*)
		  (push co *scip-snd-usable*))))))
	(let ((a (assoc c *scip-special-usable*)))
	  (if a
	      (setq *scip-usable* (cdr a))
	    (setq *scip-usable* *scip-fst-usable*)))
	(if *scunak-socket*
	    (scip-1-sock c)
	  (scip-1 c))
	)
    (format t "~d is not an open claim.~%" c)))

(defun scip-1 (&optional claim)
  (let* ((evar nil)
	 (ctx nil)
	 (names nil)
	 (tp nil)
	 (namedectx nil)
	 (namesubst 'ID)
	 (task nil)
	 (giveup nil)
	 )
    (loop while (and *scip-tasks* (not giveup)) do
	  (setq task (car *scip-tasks*))
	  (setq evar (car task))
	  (setq ctx (cadr task))
	  (setq names (nth 2 task))
	  (setq tp (nth 3 task))
	  (setq namedectx (nth 4 task))
	  (setq namesubst (nth 5 task))
	  (unless (ctx-type-valid-p ctx tp)
	    (fail "bad task ctx tp" ctx tp))
	  (if (dpi-p tp)
	      (progn
		(let* ((z (if (dtype-returns-pf-p (dpi-dom tp))
			      (format nil "ass~d" (incf *scip-assnum*))
			    (progn
			      (format t "Give name for ~d>" (output1-type-string (dpi-dom tp) names))
			      (read-line))))
		       (zz (if (equal z "")
			       (let ((g (intern-gensym "a")))
				 (format t "Please enter a name.  If you hit return again, I will use the name ~d.~%" g)
				 (format t "Give name for ~d>" (output1-type-string (dpi-dom tp) names))
				 (let ((h (read-line)))
				   (if (equal h "")
				       (progn
					 (setq z (format nil "~d" g))
					 g)
				     (progn
				       (setq z h)
				       (intern h)))))
			     (intern z))))
		  (setf (get zz 'bvar) t)
		  (setf (get zz 'dbtype) (dbsubst-type (dpi-dom tp) #'identity namesubst))
		  (let ((ctx2 (ctx-cons (dpi-dom tp) ctx)))
		    (pop *scip-tasks*)
		    (push (list evar ctx2 (cons z names) (dpi-cod tp)
				(cons (list zz (get zz 'dbtype)) namedectx)
				(cons zz (cons #'identity namesubst)))
			  *scip-tasks*))))
	    (multiple-value-bind
	     (succ1 tasklist1 theta1)
	     (if *scip-eager-elims*
		 (task-close-under-simple-elims task (cdr *scip-tasks*) *scip-theta*)
	       nil)
	     (if succ1
		 (progn
;		   (push (list *scip-tasks* *scip-theta*) *scip-taskstack*) ; otherwise undo stops working
		   (setq *scip-tasks* tasklist1)
		   (setq *scip-theta* theta1)
		   )
	       (let ((cmd (iprove-read-cmd)))
		 (cond ((string= cmd "pstatus")
			(let ((i 0))
			  (dolist (task *scip-tasks*)
			    (format t "~d) ~d ~d~%" i (nth 2 task) (output1-type-string (nth 3 task) (nth 2 task)))
			    (incf i))))
		       ((string= cmd "pterm") ; print current proof term
			(format t "Current Pf Term:~%~d~%" (output1-normal-string (normalize (cdr (assoc *scip-gevar* *scip-theta*))))))
		       ((string= cmd "chkterm") ; check current proof term
			(if (ctx-term-type-p *emptyctx* (normalize (cdr (assoc *scip-gevar* *scip-theta*))) *scip-gtp*)
			    (format t "Current Pf Term OK~%")
			  (format t "Current Pf Term NOT OK - ill-typed~%")))
		       ((or (string= cmd "clear-usable") (string= cmd "usable0"))
			(setq *scip-usable* nil)
			)
		       ((and (> (length cmd) 4) (string-equal cmd "use " :start1 0 :end1 4)) ; modified this to behave like main top level use
;			(let ((name (intern (subseq cmd 4))))
;			  (if (and (get name 'dbtype)
;				   (or (dtype-returns-pf-p (get name 'dbtype))
;				       (dtype-returns-dclass-p (get name 'dbtype))))
;			      (progn
;				(push name *scip-usable*)
;				(format t "Added to usable~%"))
;			    (progn
;			      (format t "Not added to usable~%")
;			      nil))))
			(let ((xl (cdr (string-to-string-list cmd))))
			  (setq xl (mapcar #'(lambda (x)
					       (if (stringp x) (intern x) x)) xl))
			  (if (member '|all| xl)
			      (setq *scip-usable* *global-sigma*)
			    (if (member '|none| xl)
				(setq *scip-usable* nil)
			      (progn
				(setq *scip-usable* nil)
				(dolist (x xl)
				  (cond ((eq x '|fo|)
					 (setq *scip-usable*
					       (union (remove-if-not #'(lambda (co)
									 (and (not (get co 'auto-gen)) (or (get co 'fo-unif-type) (get co 'fo-type))))
								     *scip-sigma*)
						      *scip-usable*)))
					((eq x '|defns|)
					 (setq *scip-usable*
					       (union (remove-if-not #'(lambda (co)
									 (get co 'auto-gen))
								     *scip-sigma*)
						      *scip-usable*)))
					((eq x '|so|)
					 (setq *scip-usable*
					       (union (remove-if #'(lambda (co)
								     (or (get co 'auto-gen) (get co 'fo-unif-type) (get co 'fo-type)))
								 *scip-sigma*)
						      *scip-usable*)))
					((and (get x 'dbtype) (or (dtype-returns-dclass-p (get x 'dbtype))
								  (dtype-returns-pf-p (get x 'dbtype))))
					 (push x *scip-usable*)
					 )
					(t (format t "Ignoring ~d~%" x)))))))
			  (if *scip-usable*
			      (format t "Reset usable~%")
			    (format t "WARNING: usable empty!~%"))))
		       ((and (> (length cmd) 9) (string-equal cmd "activate " :start1 0 :end1 9))
			(let ((name (intern (subseq cmd 9)))
			      (added nil))
			  (when (and (get name 'dbtype)
				     (or (dtype-returns-pf-p (get name 'dbtype))
					 (dtype-returns-dclass-p (get name 'dbtype))))
			    (push name *scip-usable*)
			    (setq added t))
			  (dolist (c *global-sigma*)
			    (when (and
				   (or (dtype-returns-pf-p (get c 'dbtype))
				       (dtype-returns-dclass-p (get c 'dbtype)))
				   (member name (dtype-sig-elts (get c 'dbtype))))
			      (push c *scip-usable*)
			      (setq added t)))
			  (if added
			      (format t "Added to usable~%")
			    (format t "Nothing added to usable~%"))))
		       ((string= cmd "usable1")
			(setq *scip-usable* *scip-fst-usable*)
			)
		       ((string= cmd "usable2")
			(setq *scip-usable* *scip-snd-usable*)
			)
		       ((string= cmd "usable12")
			(setq *scip-usable* (append *scip-fst-usable* *scip-snd-usable*))
			)
		       ((string= cmd "unif+")
			(format t "~d~%" (incf *preunify-msv-goal*))
			(format t "~d~%" (incf *preunify-msv-hence*))
			(format t "~d~%" (incf *preunify-msv-supp*)))
		       ((string= cmd "unif-")
			(format t "~d~%" (decf *preunify-msv-goal*))
			(format t "~d~%" (decf *preunify-msv-hence*))
			(format t "~d~%" (decf *preunify-msv-supp*)))
		       ((string= cmd "pplan")
			(when ctx
			  (format t "Support (Objects, Assumptions and Derived Facts in Context):~%")
			  (let ((tmpl nil))
			    (do ((names2 names (cdr names2))
				 (ectx2 ctx (cdr ectx2)))
				((or (null names2) (null ectx2)))
				(push (format nil "~d:~d" (car names2) (output1-type-string (car ectx2) (cdr names2))) tmpl))
			    (dolist (tmp tmpl)
			      (format t "~d~%" tmp))))
			(format t "Goal (What you need to show): ~d~%"
				(output1-type-string tp names)))
		       ((string= cmd "pplan*")
			(when ctx
			  (format t "Support (Objects, Assumptions and Derived Facts in Context):~%")
			  (let ((tmpl nil))
			    (setq *output1-skip-snd* t)
			    (do ((names2 names (cdr names2))
				 (ectx2 ctx (cdr ectx2)))
				((or (null names2) (null ectx2)))
				(push (format nil "~d:~d" (car names2) (output1-type-string (car ectx2) (cdr names2))) tmpl))
			    (dolist (tmp tmpl)
			      (format t "~d~%" tmp))))
			(format t "Goal (What you need to show): ~d~%"
				(output1-type-string tp names))
			(setq *output1-skip-snd* nil)
			)
		       ((or (string= cmd "undo") (string= cmd "u"))
			(if *scip-taskstack*
			    (let ((z (pop *scip-taskstack*)))
			      (setq *scip-tasks* (car z))
			      (setq *scip-theta* (cadr z)))
			  (format t "No previous list of plans~%")))
		       ((string= cmd "saveproof")
			(format t "Filename>")
			(let ((filename (read-line)))
			  (save-scip-proof filename)))
		       ((and (> (length cmd) 10) (string-equal cmd "saveproof " :start1 0 :end1 10))
			(let ((filename (subseq cmd 10)))
			  (save-scip-proof filename)))
		       ((string= cmd "restoreproof")
			(format t "Filename>")
			(let ((filename (read-line)))
			  (load filename)
			  (dolist (bv (nth 4 (car *scip-tasks*)))
			    (setf (get (car bv) 'bvar) t)
			    (setf (get (car bv) 'dbtype) (cadr bv)))
			  ))
		       ((and (> (length cmd) 13) (string-equal cmd "restoreproof " :start1 0 :end1 13))
			(let ((filename (subseq cmd 13)))
			  (load filename)
			  (dolist (bv (nth 4 (car *scip-tasks*)))
			    (setf (get (car bv) 'bvar) t)
			    (setf (get (car bv) 'dbtype) (cadr bv)))))
		       ((string= cmd "q")
			(setq giveup t))
		       ((or (string= cmd "choose-task") (string= cmd "ctk"))
			(format t "Enter a number between 0 and ~d~%" (- (length *scip-tasks*) 1))
			(let ((z (read)))
			  (if (and (numberp z) (nth z *scip-tasks*))
			      (let ((y (nth z *scip-tasks*)))
				(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				(setq *scip-tasks* (cons y (remove y *scip-tasks*))))
			    (format t "Task Unchanged: ~d is not a number between 0 and ~d~%" z (- (length *scip-tasks*) 1)))))
		       ((string= cmd "d") ; done
			(multiple-value-bind
			 (succ theta)
			 (task-done task *scip-theta* nil)
			 (if succ
			     (progn
			       (setq *scip-theta* theta)
			       (pop *scip-tasks*)
			       (format t "Done with subgoal!~%")
			       )
			   (format t "Subgoal not finished~%"))))
		       ((string= cmd "d=") ; done up to equality
			(let ((*scip-usable* (list '|eqE| '|eqE2| '|eqCE| '|eqCE2|))
			      (*preunify-msv-goal* (+ *preunify-msv-goal* 4))
			      (*preunify-msv-hence* (+ *preunify-msv-hence* 4))
			      (*preunify-msv-supp* (+ *preunify-msv-supp* 4))
			      )
			  (declare (special *scip-usable*
					    *preunify-msv-goal*
					    *preunify-msv-hence*
					    *preunify-msv-supp*))
			  (multiple-value-bind
			   (succ theta)
			   (task-done task *scip-theta* nil)
			   (if succ
			       (progn
				 (setq *scip-theta* theta)
				 (pop *scip-tasks*)
				 (format t "Done with subgoal!~%")
				 )
			     (format t "Subgoal not finished up to equality~%")))))
		       ((or (string= cmd "help") (string= cmd "?"))
			(print-scip-help))
		       ((and (> (length cmd) 5) (string-equal cmd "help " :start1 0 :end1 5))
			(let ((name (intern (subseq cmd 5))))
			  (if name
			      (print-help-name name)
			    (print-scip-help))))
		       ((string-equal cmd "xmcases")
			(when (pf-p tp)
			  (format t "Proposition>")
			  (multiple-value-bind
			   (p newtp)
			   (read-extract1 namedectx)
			   (if (and p (prop-p newtp))
			       (let* ((evar3 (intern-gensym))
				      (evar4 (intern-gensym))
				      (case1 (app-n-1-to-0 (length namedectx) evar3))
				      (case2 (app-n-1-to-0 (length namedectx) evar4))
				      (ap
				       (app-n '|xmcases| (list p (pf-prop tp) case1 case2)))
				      (ftp3 (dpi (pf p) (dbshift-type-n 1 tp)))
				      (ftp4 (dpi (pf (app '|not| p)) (dbshift-type-n 1 tp))))
				 (setf (get evar3 'evar) t)
				 (setf (get evar3 'dbtype)
				       (dpi-ctx ctx ftp3))
				 (setf (get evar4 'evar) t)
				 (setf (get evar4 'dbtype)
				       (dpi-ctx ctx ftp4))
				 (dotimes (i (length ctx))
				   (setq ap (lam ap)))
				 (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				 (setq *scip-theta* (compose-theta-1 evar ap *scip-theta*))
				 (setq *scip-tasks*
				       (cons
					(list evar3 ctx names ftp3
					      namedectx namesubst)
					(cons
					 (list evar4 ctx names ftp4
					       namedectx namesubst)
					 (cdr *scip-tasks*)))))
			     (format t "That was not a prop.~%")))))
		       ((string-equal cmd "cases")
			(when (pf-p tp)
			  (let ((or-in-ctx nil))
			    (do ((ctx9 ctx (cdr ctx9))
				 (k 0 (1+ k)))
				((or or-in-ctx (null ctx9)))
				(when (and (pf-p (car ctx9))
					   (eq (term-extr-head (pf-prop (car ctx9))) '|or|))
				  (setq or-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
			    (if or-in-ctx
				(let* ((k (car or-in-ctx))
				       (disjtp (cdr or-in-ctx))
				       (disj (pf-prop disjtp))
				       (disjl (app-arg (app-func disj)))
				       (disjr (app-arg disj))
				       (evar3 (intern-gensym))
				       (evar4 (intern-gensym))
				       (evtrm3 (app-n-1-to-0 (length namedectx) evar3))
				       (evtrm4 (app-n-1-to-0 (length namedectx) evar4))
				       (ap (app
					    (app
					     (app
					      (app
					       (app
						(app '|orE| disjl) disjr)
					       k)
					      (pf-prop tp))
					     evtrm3)
					    evtrm4))
				       (ftp3 (dpi (pf disjl) (dbshift-type-n 1 tp)))
				       (ftp4 (dpi (pf disjr) (dbshift-type-n 1 tp))))
				  (setf (get evar3 'evar) t)
				  (setf (get evar3 'dbtype)
					(dpi-ctx ctx ftp3))
				  (setf (get evar4 'evar) t)
				  (setf (get evar4 'dbtype)
					(dpi-ctx ctx ftp4))
				  (dotimes (i (length ctx))
				    (setq ap (lam ap)))
				  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				  (setq *scip-theta* (compose-theta-1 evar ap *scip-theta*))
				  (setq *scip-tasks*
					(cons
					 (list evar3 ctx names ftp3
					       namedectx namesubst)
					 (cons
					  (list evar4 ctx names ftp4
						namedectx namesubst)
					  (cdr *scip-tasks*)))))
			      (format t "Cannot apply cases.  No disjunction in context.~%")))))
		       ((string-equal cmd "adjcases")
			(when (pf-p tp)
			  (let ((or-in-ctx nil))
			    (do ((ctx9 ctx (cdr ctx9))
				 (k 0 (1+ k)))
				((or or-in-ctx (null ctx9)))
				(when (and (pf-p (car ctx9))
					   (app-p (pf-prop (car ctx9)))
					   (app-p (app-func (pf-prop (car ctx9))))
					   (eq (app-func (app-func (pf-prop (car ctx9)))) '|in|)
					   (app-p (app-arg (app-func (pf-prop (car ctx9)))))
					   (app-p (app-func (app-arg (app-func (pf-prop (car ctx9))))))
					   (eq (app-func (app-func (app-arg (app-func (pf-prop (car ctx9))))))
					       '|setadjoin|))
				  (setq or-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
			    (if or-in-ctx
				(let* ((k (car or-in-ctx))
				       (disjtp (cdr or-in-ctx))
				       (insa (pf-prop disjtp))
				       (elt (app-arg insa))
				       (sa (app-arg (app-func insa)))
				       (set1 (app-arg (app-func sa)))
				       (set2 (app-arg sa))
				       (evar3 (intern-gensym))
				       (evar4 (intern-gensym))
				       (evtrm3 (app-n-1-to-0 (length namedectx) evar3))
				       (evtrm4 (app-n-1-to-0 (length namedectx) evar4))
				       (ap (app
					    (app
					     (app
					      (app
					       (app
						(app
						 (app '|setadjoinE| set1) set2)
						elt)
					       k)
					      (pf-prop tp))
					     evtrm3)
					    evtrm4))
				       (ftp3 (dpi (pf (app-n '|eq| (list elt set1))) (dbshift-type-n 1 tp)))
				       (ftp4 (dpi (pf (app-n '|in| (list set2 elt))) (dbshift-type-n 1 tp))))
				  (setf (get evar3 'evar) t)
				  (setf (get evar3 'dbtype)
					(dpi-ctx ctx ftp3))
				  (setf (get evar4 'evar) t)
				  (setf (get evar4 'dbtype)
					(dpi-ctx ctx ftp4))
				  (dotimes (i (length ctx))
				    (setq ap (lam ap)))
				  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				  (setq *scip-theta* (compose-theta-1 evar ap *scip-theta*))
				  (setq *scip-tasks*
					(cons
					 (list evar3 ctx names ftp3
					       namedectx namesubst)
					 (cons
					  (list evar4 ctx names ftp4
						namedectx namesubst)
					  (cdr *scip-tasks*))))
				  (format t "OK~%")
				  )
			      (format t "Cannot apply setadjoin cases.  No (y::(x;A)) in context.~%")))))
		       ((and (> (length cmd) 7) (string-equal cmd "exists " :start1 0 :end1 7))
			(when (pf-p tp)
			  (let ((name (intern (subseq cmd 7))))
			    (if name
				(let ((ex-in-ctx nil))
				  (do ((ctx9 ctx (cdr ctx9))
				       (k 0 (1+ k)))
				      ((or ex-in-ctx (null ctx9)))
				      (when (and (pf-p (car ctx9))
						 (eq (term-extr-head (pf-prop (car ctx9))) '|dex|))
					(setq ex-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
				  (if ex-in-ctx
				      (let* ((k (car ex-in-ctx))
					     (pfex (cdr ex-in-ctx))
					     (ex (pf-prop pfex))
					     (bdset (app-arg (app-func ex)))
					     (phi (app-arg ex)))
					(setq *k* k *pfex* pfex *ex* ex *bdset* bdset *phi* phi) ; delete me
					(setf (get name 'bvar) t)
					(setf (get name 'dbtype) (dclass (app '|in| (dbsubst bdset #'identity namesubst))))
					(let* ((evar4 (intern-gensym))
					       (ctx4 (ctx-cons (dclass (app '|in| bdset)) ctx))
					       (namedectx4 (cons (list name (get name 'dbtype))
								 namedectx))
					       (namesubst4 (cons name (cons #'identity namesubst)))
					       (evtrm4 (app-n-1-to-0 (length namedectx4) evar4))
					       (ap (app
						    (app
						     (app
						      (app
						       (app '|dexE| bdset)
						       phi)
						      k)
						     (pf-prop tp))
						    (lam evtrm4)))
					       (ftp (dpi (pf (normalize (app (dbshift-n 1 phi) 0)))
							 (dbshift-type-n 2 tp))))
					  (setq *ap* ap) ; delete me
					  (setf (get evar4 'evar) t)
					  (setf (get evar4 'dbtype)
						(dpi-ctx ctx4 ftp))
					  (dotimes (i (length ctx))
					    (setq ap (lam ap)))
					  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					  (setq *scip-theta* (compose-theta-1 evar ap *scip-theta*))
					  (setq *scip-tasks*
						(cons
						 (list evar4 ctx4 (cons name names)
						       ftp
						       namedectx4 namesubst4)
						 (cdr *scip-tasks*)))
					  ))
				    (progn ; otherwise let user give info and make a claim
				      (format t "Bounding Set>")
				      (multiple-value-bind
				       (bdset newtp)
				       (read-extract1 namedectx)
				       (if (and bdset (or (obj-p newtp) (dclass-p newtp)))
					   (progn
					     (when (dclass-p newtp)
					       (setq bdset (fst bdset))
					       (setq newtp (obj)))
					     (let* ((namedbdtp (dclass (app '|in| (dbsubst bdset #'identity namesubst))))
						    (namedectx2 (cons (list name namedbdtp) namedectx))
						    (ctx2 (ctx-cons (dclass (app '|in| bdset)) ctx)))
					       (setf (get name 'bvar) t)
					       (setf (get name 'dbtype) namedbdtp)
					       (format t "Proposition>")
					       (multiple-value-bind
						(phibody newtp2)
						(read-extract1 namedectx2)
						(if (and phibody (prop-p newtp2))
						    (if (nintrm-p 0 phibody)
							(let* ((phi (lam phibody))
							       (ex (app (app '|dex| bdset) phi))
							       (pfex (pf ex)))
							  (multiple-value-bind
							   (tasks2 theta2)
							   (task-claim pfex task (cdr *scip-tasks*) *scip-theta*)
							   (let ((taskwexhyp (car tasks2))
								 (delayed (cdr tasks2)))
							     (multiple-value-bind
							      (evar3 ctx3 names3 tp3 namedectx3 namesubst3)
							      (task-components taskwexhyp)
							      (let* ((evar4 (intern-gensym))
								     (bdset1 (dbshift-n 1 bdset))
								     (ctx4 (ctx-cons (dclass (app '|in| bdset1)) ctx3))
								     (namedectx4 (cons (list name (dclass (app '|in| bdset1))) namedectx3))
								     (namesubst4 (cons name (cons #'identity namesubst3)))
								     (evtrm4 (app-n-1-to-0 (length namedectx4) evar4))
								     (ap (app
									  (app
									   (app
									    (app
									     (app '|dexE| bdset1)
									     (dbshift-n 1 phi))
									    0) (dbshift-n 1 (pf-prop tp)))
									  (lam evtrm4)))
								     (ftp (dpi (pf (normalize (app (dbshift-n 2 phi) 0)))
									       (dbshift-type-n 3 tp))))
								(setf (get evar4 'evar) t)
								(setf (get evar4 'dbtype)
								      (dpi-ctx ctx4 ftp))
								(dotimes (i (length ctx3))
								  (setq ap (lam ap)))
								(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
								(setq *scip-theta* (compose-theta-1 evar3 ap theta2))
								(setq *scip-tasks*
								      (cons
								       (list evar4 ctx4 (cons name names3)
									     ftp
									     namedectx4 namesubst4)
								       delayed))
								)))))
						      (format t "Proposition must depend on existence variable~%"))
						  (format t "Ill-formed proposition~%")))))
					 (format t "Ill-formed bounding set~%"))))))
			      (format t "Problem with eigenvariable name.~%")))))
		       ((and (> (length cmd) 15) (string-equal cmd "setunionexists " :start1 0 :end1 15)) ; fix (currently a copy of exists with minor modifications)
			(when (pf-p tp)
			  (let ((name (intern (subseq cmd 15))))
			    (if name
				(let ((ex-in-ctx nil))
				  (do ((ctx9 ctx (cdr ctx9))
				       (k 0 (1+ k)))
				      ((or ex-in-ctx (null ctx9)))
				      (when (and (pf-p (car ctx9))
						 (app-p (pf-prop (car ctx9)))
						 (app-p (app-func (pf-prop (car ctx9))))
						 (eq (app-func (app-func (pf-prop (car ctx9)))) '|in|)
						 (app-p (app-arg (app-func (pf-prop (car ctx9)))))
						 (eq (app-func (app-arg (app-func (pf-prop (car ctx9)))))
						     '|setunion|))
					(setq ex-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
				  (if ex-in-ctx
				      (let* ((k (car ex-in-ctx))
					     (pfex (cdr ex-in-ctx))
					     (ex (pf-prop pfex))
					     (cset (app-arg (app-arg (app-func ex))))
					     (elt (app-arg ex)))
					(setq *k* k *pfex* pfex *ex* ex *cset* cset *elt* elt) ; delete me
					(let* ((evar4 (intern-gensym))
					       (a1 (pf (app (app '|in| (dbshift-n 2 cset)) 1)))
					       (a2 (pf (app (app '|in| 0) (dbshift-n 1 elt))))
					       (ctx4 (ctx-cons (obj) ctx))
					       (namedectx4
						(cons (list name (obj))
						      namedectx))
					       (namesubst4 (cons name (cons #'identity namesubst)))
					       (evtrm4 (app-n-1-to-0 (length namedectx4) evar4))
					       (ap (app
						    (app
						     (app
						      (app
						       (app '|setunionE| cset)
						       elt)
						      k)
						     (pf-prop tp))
						    (lam evtrm4)))
					       (ftp (dpi a2 (dpi a1
								 (dbshift-type-n 3 tp)))))
					  (setq *ap* ap) ; delete me
					  (setf (get name 'bvar) t)
					  (setf (get name 'dbtype) (obj))
					  (setf (get evar4 'evar) t)
					  (setf (get evar4 'dbtype)
						(dpi-ctx ctx4 ftp))
					  (dotimes (i (length ctx))
					    (setq ap (lam ap)))
					  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					  (setq *scip-theta* (compose-theta-1 evar ap *scip-theta*))
					  (setq *scip-tasks*
						(cons
						 (list evar4 ctx4 (cons name names)
						       ftp
						       namedectx4 namesubst4)
						 (cdr *scip-tasks*)))
					  ))
				    nil))))))
		       ((string-equal cmd "elim") ; do simple eliminations (eg, conjunctions)
			(multiple-value-bind
			 (succ1 tasklist1 theta1)
			 (task-close-under-simple-elims task (cdr *scip-tasks*) *scip-theta*)
			 (if succ1
			     (progn
			       (format t "OK.~%")
			       (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
			       (setq *scip-tasks* tasklist1)
			       (setq *scip-theta* theta1))
			   (format t "No simple elimination steps possible.~%"))))
					;		    ((and (> (length cmd) 7) (string-equal cmd "unfold " :start1 0 :end1 7))
					;		     (let ((name (intern (subseq cmd 7))))
					;		       (if (abbrevname-p name)
					;			   ()
					;			 ?)))
					;		    ((string-equal cmd "fold")
					;		     (when (pf-p tp)
					;		       (let* ((prop (pf-prop tp))
					;			      (h (term-app-head prop)))
					;			 (if (and (symbolp h) (abbrevname-p h))
					;			     (multiple-value-bind
					;			      (succ1 tasklist1 theta1)
					;			      (task-fold-defns (pf (delta-head-reduce prop)) task (cdr *scip-tasks*) *scip-theta*)
					;			      (if succ1
					;				  (progn
					; 				    (format t "Correct.~%")
					; 				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					; 				    (setq *scip-tasks* tasklist1)
					; 				    (setq *scip-theta* theta1))
					;				(format t "Could not justify fold of defn.~%")))
					;			   
					;			   (format t "Could not parse proposition.~%"))))
					;
					;			   
					;			   ?))))
		       ((string= cmd "b")
			(let ((back1 (quick-fill-gap ctx tp *scip-usable* nil 1)))
			  (if back1
			      (let ((z (find-if-not #'(lambda (x)
							(cadr x))
						    back1)))
				(if z
				    (let ((tmp (car z)))
				      (setq *scip-theta* (compose-theta-1 evar tmp *scip-theta*))
				      (format t "Done with subgoal!~%")
				      (pop *scip-tasks*)
				      )
				  (let ((i -1))
				    (setq back1 (simplify-subgoal-list back1))
				    (dolist (z back1)
				      (format t "~d) " (incf i))
				      (let ((tmp (car z)))
					(dotimes (j (length ctx))
					  (setq tmp (gen-lam-body tmp)))
					(format t "~d~%Reduce to~%"
						(output1-normal-string tmp names))
					(dolist (sgs (cadr z))
					  (setq tmp (cdr sgs))
					  (dotimes (j (length ctx))
					    (when (dpi-p tmp)
					      (setq tmp (dpi-cod tmp))))
					  (format t "~d~%" (output1-type-string tmp names)))))
				    (format t "Enter a number between 0 and ~d~%" i)
				    (let ((z (read)))
				      (if (and (numberp z) (nth z back1))
					  (let ((y (nth z back1)))
					    (let ((tmp (car y)))
					      (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					;					     (format t "theta = ~S~%" *scip-theta*) ; delete me
					      (setq *scip-theta* (compose-theta-1 evar tmp *scip-theta*))
					;					     (format t "evar = ~S~%tmp = ~S~%" evar tmp) ; delete me
					;					     (format t "theta = ~S~%" *scip-theta*) ; delete me
					      (setq *scip-tasks* (append
								  (mapcar #'(lambda (new)
									      (let ((dtp (cdr new)))
										(setf (get (car new) 'dbtype) (cdr new)) ; global type, so OK
										(dotimes (j (length ctx))
										  (when (dpi-p dtp)
										    (setq dtp (dpi-cod dtp))))
										(list (car new) ctx names dtp
										      namedectx namesubst
										      )))
									  (cadr y))
								  (cdr *scip-tasks*)))))
					(format t "Task Unchanged: ~d is not a number between 0 and ~d~%" z i))))))
			    (format t "No backward options with 1 gap~%"))))
		       ((string= cmd "b2")
			(let ((back1 (quick-fill-gap ctx tp *scip-usable* nil 2)))
			  (if back1
			      (let ((z (find-if-not #'(lambda (x)
							(cadr x))
						    back1)))
				(if z
				    (let ((tmp (car z)))
				      (setq *scip-theta* (compose-theta-1 evar tmp *scip-theta*))
				      (format t "Done with subgoal!~%")
				      (pop *scip-tasks*)
				      )
				  (let ((i -1))
				    (setq back1 (simplify-subgoal-list back1))
				    (dolist (z back1)
				      (format t "~d) " (incf i))
				      (let ((tmp (car z)))
					(dotimes (j (length ctx))
					  (setq tmp (gen-lam-body tmp)))
					(format t "~d~%Reduce to~%"
						(output1-normal-string tmp names))
					(dolist (sgs (cadr z))
					  (setq tmp (cdr sgs))
					  (dotimes (j (length ctx))
					    (when (dpi-p tmp)
					      (setq tmp (dpi-cod tmp))))
					  (format t "~d~%" (output1-type-string tmp names)))))
				    (format t "Enter a number between 0 and ~d~%" i)
				    (let ((z (read)))
				      (if (and (numberp z) (nth z back1))
					  (let ((y (nth z back1)))
					    (let ((tmp (car y)))
					   (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					;					     (format t "theta = ~S~%" *scip-theta*) ; delete me
					   (setq *scip-theta* (compose-theta-1 evar tmp *scip-theta*))
					;					     (format t "evar = ~S~%tmp = ~S~%" evar tmp) ; delete me
					;					     (format t "theta = ~S~%" *scip-theta*) ; delete me
					   (setq *scip-tasks* (append
							       (mapcar #'(lambda (new)
									   (let ((dtp (cdr new)))
									     (setf (get (car new) 'dbtype) (cdr new)) ; global type, so OK
									     (dotimes (j (length ctx))
									       (when (dpi-p dtp)
										 (setq dtp (dpi-cod dtp))))
									     (list (car new) ctx names dtp
										   namedectx namesubst
										   )))
								       (cadr y))
							       (cdr *scip-tasks*)))))
				     (format t "Task Unchanged: ~d is not a number between 0 and ~d~%" z i))))))
			 (format t "No backward options with 2 gaps~%"))))
		    ((string= cmd "f") 
		     (let ((fw 
			    (simplify-term-type-pairs
			     (remove-if-not
			      #'(lambda (x)
				  (pf-p (cdr x)))
			      (mapcar #'(lambda (y)
					  (cons y (ctx-extract-type ctx y)))
				      (quick-ctx-forward *scip-usable* ctx 1))))))
		       (if fw
			   (let ((i -1))
			     (dolist (z fw)
			       (format t "~d) ~d~%~d~%" (incf i)
				       (output1-normal-string (car z) names)
				       (output1-type-string (cdr z) names)))
			     (format t "Enter a number between 0 and ~d~%" i)
			     (let ((z (read)))
			       (if (and (numberp z) (nth z fw))
				   (let* ((y (nth z fw))
					  (name (format nil "fact~d" (incf *scip-factnum*)))
					  (namez (intern name))
					  (ctx2 (ctx-cons (cdr y) ctx))
					  (newevar (intern-gensym))
					  (tp2 (dbshift-type-n 1 tp))
					  (newevartp (dpi-ctx ctx2 tp2)))
				     (setf (get namez 'bvar) t)
				     (setf (get namez 'dbtype) (dbsubst-type (cdr y) #'identity namesubst))
				     (setf (get newevar 'evar) t)
				     (setf (get newevar 'dbtype) newevartp) ; global
				     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				     (pop *scip-tasks*)
				     (setq *scip-theta* (compose-theta-1 evar (term-for-extending-ctx ctx newevar (normalize (car y))) *scip-theta*))
				     (push (list newevar ctx2 (cons name names) tp2
						 (cons (list namez (get namez 'dbtype)) namedectx)
						 (cons namez (cons #'identity namesubst))
						 )
					   *scip-tasks*))
				 (format t "Task Unchanged: ~d is not a number between 0 and ~d~%" z i))))
			 (format t "No forward options~%"))))
		    ((string= cmd "f2")
		     (let ((fw 
			    (simplify-term-type-pairs
			     (remove-if-not
			      #'(lambda (x)
				  (pf-p (cdr x)))
			      (mapcar #'(lambda (y)
					  (cons y (ctx-extract-type ctx y)))
				      (quick-ctx-forward *scip-usable* ctx 2))))))
		       (if fw
			   (let ((i -1))
			     (dolist (z fw)
			       (format t "~d) ~d~%~d~%" (incf i)
				       (output1-normal-string (car z) names)
				       (output1-type-string (cdr z) names)))
			     (format t "Enter a number between 0 and ~d~%" i)
			     (let ((z (read)))
			       (if (and (numberp z) (nth z fw))
				   (let* ((y (nth z fw))
					  (name (format nil "fact~d" (incf *scip-factnum*)))
					  (namez (intern name))
					  (ctx2 (ctx-cons (cdr y) ctx))
					  (newevar (intern-gensym))
					  (tp2 (dbshift-type-n 1 tp))
					  (newevartp (dpi-ctx ctx2 tp2)))
				     (setf (get namez 'bvar) t)
				     (setf (get namez 'dbtype) (dbsubst-type (cdr y) #'identity namesubst))
				     (setf (get newevar 'evar) t)
				     (setf (get newevar 'dbtype) newevartp) ; global
				     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				     (pop *scip-tasks*)
				     (setq *scip-theta* (compose-theta-1 evar (term-for-extending-ctx ctx newevar (normalize (car y))) *scip-theta*))
				     (push (list newevar ctx2 (cons name names) tp2
						 (cons (list namez (get namez 'dbtype)) namedectx)
						 (cons namez (cons #'identity namesubst))
						 )
					   *scip-tasks*))
				 (format t "Task Unchanged: ~d is not a number between 0 and ~d~%" z i))))
			 (format t "No forward(2) options~%"))))
		    ((string= cmd "typeof")
		     (format t "Enter Extraction Term>")
		     (multiple-value-bind
		      (e newtp)
		      (read-extract1 namedectx)
		      (if e
			  (format t "Type: ~d~%" (output1-type-string newtp names))
			(format t "Could not determine an extraction term from input.~%"))))
 		    ((string= cmd "hornit")
		     (setq *fohorn-binary-res* nil)
		     (setq *fohorn-factor* nil)
		     (setq *fohorn-unit-res* t)
		     (let* ((inittime (get-internal-run-time))
			    (e (fohorn-res-fill (mapcar #'car namedectx) tp (append *scip-fst-usable* *scip-defn-usable*)))
			    (endtime (get-internal-run-time)))
		       (format t "hornit time: ~d~%" (- endtime inittime))
		       (if e
			   (progn
			     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
			     (setq *scip-theta* (compose-theta-1 evar e *scip-theta*))
			     (pop *scip-tasks*)
			     (format t "hornit succeeded.~%")
			     )
			 (format t "hornit failed.~%"))))
 		    ((string= cmd "vampire")
		     (let* ((inittime (get-universal-time))
			    (e (vampire-res-fill (mapcar #'car namedectx)
						 (dbsubst-type tp #'identity namesubst)
						 (append *scip-fst-usable* *scip-snd-usable* *scip-defn-usable*)))
			    (endtime (get-universal-time)))
		       (format t "vampire real time: ~d~%" (- endtime inittime))
		       (if e
			   (progn
;			     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
;			     (setq *scip-theta* (compose-theta-1 evar e *scip-theta*))
;			     (pop *scip-tasks*)
			     (format t "vampire succeeded (but no proof term at present).~%")
			     )
			 (format t "vampire failed.~%"))))
 		    ((string= cmd "otter")
		     (let* ((inittime (get-universal-time))
			    (e (otter-res-fill (mapcar #'car namedectx)
					       (dbsubst-type tp #'identity namesubst)
					       (append *scip-fst-usable* *scip-defn-usable*)))
			    (endtime (get-universal-time)))
		       (format t "otter real time: ~d~%" (- endtime inittime))
		       (if e
			   (progn
;			     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
;			     (setq *scip-theta* (compose-theta-1 evar e *scip-theta*))
;			     (pop *scip-tasks*)
			     (format t "otter succeeded (but no proof term at present).~%")
			     )
			 (format t "otter failed.~%"))))
 		    ((string= cmd "mls")
		     (let ((prop (dbsubst (pf-prop tp) #'identity namesubst)))
		       (if (prop-comp-set-fragment-p prop)
			   (let ((br (mls*-tableau (remove-if #'null
							      (mapcar #'(lambda (x)
									  (if (and (pf-p (cadr x))
										   (prop-comp-set-fragment-p (pf-prop (cadr x))))
									      (pf-prop (cadr x))
									    nil))
								      *sci-namedectx*))
						   (list prop))))
			     (if br
				 (progn
				   (format t "The mls set theory part of this is satisfiable.  Consider:~%")
				   (dolist (p (car br))
				     (format t "~d~%" (output1-extraction-string p nil nil)))
				   )
			       (format t "The gap can be filled by mls set theory reasoning...~%")))
			 (format t "The current goal is not an mls proposition.~%"))))
 		    ((string= cmd "apply")
 		     (format t "Enter Extraction Proof Term>")
 		     (multiple-value-bind
 		      (e newtp)
 		      (read-extract1 namedectx)
 		      (if e
 			  (if (dtype-returns-pf-p newtp)
			      (if (deptype1-p newtp ctx)
				  (scip-add-fact e newtp)
;				  (let* ((name (format nil "fact~d" (incf *scip-factnum*)))
;					 (namez (intern name))
;					 (ctx2 (ctx-cons newtp ctx))
;					 (newevar (intern-gensym))
;					 (tp2 (dbshift-type-n 1 tp))
;					 (newevartp (dpi-ctx ctx2 tp2)))
;				    (setf (get namez 'bvar) t)
;				    (setf (get namez 'dbtype) (dbsubst-type newtp #'identity namesubst))
;				    (setf (get newevar 'evar) t)
;				    (setf (get newevar 'dbtype) newevartp) ; global
;				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
;				    (pop *scip-tasks*)
;				    (setq *scip-theta* (compose-theta-1 evar (term-for-extending-ctx ctx newevar e) *scip-theta*))
;				    (push (list newevar ctx2 (cons name names) tp2
;						(cons (list namez (get namez 'dbtype)) namedectx)
;						(cons namez (cons #'identity namesubst))
;						)
;					  *scip-tasks*))
				(format t "Task Unchanged: ~d is of type~%~d~%which is 2nd order~%"
					(output1-extraction-string e names t)
					(output1-type-string newtp names t)
					))
 			    (format t "Task Unchanged: ~d is of type~%~d~%which is not a pf type~%"
 				    (output1-extraction-string e names t)
 				    (output1-type-string newtp names t)
 				    ))
 			(format t "Could not determine an extraction term from input.~%"))))
 		    ((string= cmd "willshow")
 		     (format t "Enter Proposition>")
 		     (let* ((e (read-extract1-prop namedectx)))
 		       (if e
 			   (let ((newtp (pf e)))
 			     (multiple-value-bind
 			      (succ1 tasklist1 theta1)
 			      (task-willshow newtp task (cdr *scip-tasks*) *scip-theta*)
 			      (if succ1
 				  (progn
 				    (format t "Correct.~%")
 				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
 				    (setq *scip-tasks* tasklist1)
 				    (setq *scip-theta* theta1))
 				(format t "Could not justify goal from given subgoal.~%"))))
 			 (format t "Could not parse proposition.~%"))))
		    ((and (> (length cmd) 6) (string-equal cmd "hence " :start1 0 :end1 6))
		     (let* ((str (subseq cmd 6))
			    (e (read-extract1-0 namedectx str)))
 		       (if e
 			   (let ((newtp (pf e)))
 			     (multiple-value-bind
 			      (succ1 tasklist1 theta1)
 			      (task-hence newtp task (cdr *scip-tasks*) *scip-theta*)
 			      (if succ1
 				  (progn
 				    (format t "Correct.~%")
 				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
 				    (setq *scip-tasks* tasklist1)
 				    (setq *scip-theta* theta1))
				(format t "Could not justify hence.~%"))))
 			 (format t "Could not parse proposition.~%"))))
		    ((and (> (length cmd) 5) (string-equal cmd "fact " :start1 0 :end1 5))
		     (let* ((str (subseq cmd 5))
			    (e (read-extract1-0 namedectx str)))
 		       (if e
 			   (let ((newtp (pf e)))
 			     (multiple-value-bind
 			      (succ1 tasklist1 theta1)
 			      (task-fact newtp task (cdr *scip-tasks*) *scip-theta*)
 			      (if succ1
 				  (progn
 				    (format t "Correct.~%")
 				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
 				    (setq *scip-tasks* tasklist1)
 				    (setq *scip-theta* theta1))
 				(format t "Could not justify fact.~%"))))
 			 (format t "Could not parse proposition.~%"))))
 		    ((string= cmd "hence")
 		     (format t "Enter Proposition>")
 		     (let* ((e (read-extract1-prop namedectx)))
 		       (if e
 			   (let ((newtp (pf e)))
 			     (multiple-value-bind
 			      (succ1 tasklist1 theta1)
 			      (task-hence newtp task (cdr *scip-tasks*) *scip-theta*)
 			      (if succ1
 				  (progn
 				    (format t "Correct.~%")
 				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
 				    (setq *scip-tasks* tasklist1)
 				    (setq *scip-theta* theta1))
				(format t "Could not justify hence.~%"))))
 			 (format t "Could not parse proposition.~%"))))
 		    ((or (string= cmd "fact") ; same as hence but without hence set to t :-)
			 (string= cmd "clearly"))
 		     (format t "Enter Proposition>")
 		     (let* ((e (read-extract1-prop namedectx)))
 		       (if e
 			   (let ((newtp (pf e)))
 			     (multiple-value-bind
 			      (succ1 tasklist1 theta1)
 			      (task-fact newtp task (cdr *scip-tasks*) *scip-theta*)
 			      (if succ1
 				  (progn
 				    (format t "Correct.~%")
 				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
 				    (setq *scip-tasks* tasklist1)
 				    (setq *scip-theta* theta1))
 				(format t "Could not justify fact.~%"))))
 			 (format t "Could not parse proposition.~%"))))
 		    ((string= cmd "willshow=")
		     (let ((*scip-usable* (list '|eqE| '|eqE2| '|eqCE| '|eqCE2|))
			   (*preunify-msv-goal* (+ *preunify-msv-goal* 4))
			   (*preunify-msv-hence* (+ *preunify-msv-hence* 4))
			   (*preunify-msv-supp* (+ *preunify-msv-supp* 4))
			   )
		       (declare (special *scip-usable*
					 *preunify-msv-goal*
					 *preunify-msv-hence*
					 *preunify-msv-supp*))
		       (format t "Enter Proposition>")
		       (let* ((e (read-extract1-prop namedectx)))
			 (if e
			     (let ((newtp (pf e)))
			       (multiple-value-bind
				(succ1 tasklist1 theta1)
				(task-willshow newtp task (cdr *scip-tasks*) *scip-theta*)
				(if succ1
				    (progn
				      (format t "Correct.~%")
				      (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				      (setq *scip-tasks* tasklist1)
				      (setq *scip-theta* theta1))
				  (format t "Could not justify goal from given subgoal.~%"))))
			   (format t "Could not parse proposition.~%")))))
 		    ((string= cmd "hence=")
		     (let ((*scip-usable* (list '|eqE| '|eqE2| '|eqCE| '|eqCE2|))
			   (*preunify-msv-goal* (+ *preunify-msv-goal* 4))
			   (*preunify-msv-hence* (+ *preunify-msv-hence* 4))
			   (*preunify-msv-supp* (+ *preunify-msv-supp* 4))
			   )
		       (declare (special *scip-usable*
					 *preunify-msv-goal*
					 *preunify-msv-hence*
					 *preunify-msv-supp*))
		       (format t "Enter Proposition>")
		       (let* ((e (read-extract1-prop namedectx)))
			 (if e
			     (let ((newtp (pf e)))
			       (multiple-value-bind
				(succ1 tasklist1 theta1)
				(task-hence newtp task (cdr *scip-tasks*) *scip-theta*)
				(if succ1
				    (progn
				      (format t "Correct.~%")
				      (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				      (setq *scip-tasks* tasklist1)
				      (setq *scip-theta* theta1))
				  (format t "Could not justify hence.~%"))))
			   (format t "Could not parse proposition.~%")))))
 		    ((string= cmd "fact=") ; same as hence= but without hence set to t :-)
		     (let ((*scip-usable* (list '|eqE| '|eqE2| '|eqCE| '|eqCE2|))
			   (*preunify-msv-goal* (+ *preunify-msv-goal* 4))
			   (*preunify-msv-hence* (+ *preunify-msv-hence* 4))
			   (*preunify-msv-supp* (+ *preunify-msv-supp* 4))
			   )
		       (declare (special *scip-usable*
					 *preunify-msv-goal*
					 *preunify-msv-hence*
					 *preunify-msv-supp*))
		       (format t "Enter Proposition>")
		       (let* ((e (read-extract1-prop namedectx)))
			 (if e
			     (let ((newtp (pf e)))
			       (multiple-value-bind
				(succ1 tasklist1 theta1)
				(task-fact newtp task (cdr *scip-tasks*) *scip-theta*)
				(if succ1
				    (progn
				      (format t "Correct.~%")
				      (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				      (setq *scip-tasks* tasklist1)
				      (setq *scip-theta* theta1))
				  (format t "Could not justify fact.~%"))))
			   (format t "Could not parse proposition.~%")))))
 		    ((string= cmd "lemma")
 		     (let ((ctxi (input1-ctx-info-from-named-ectx namedectx))
			   name expldeps dtp)
		       (format t "Enter Name>")
		       (setq name (intern (read-line)))
		       (format t "Enter Local Dependencies>")
		       (setq expldeps (extract-locvars (read-line)))
		       (multiple-value-bind
			(argctx failinfo)
			(varlist-to-ctx expldeps ctxi)
			(if failinfo
			    (format t "~d~%" failinfo)
			  (progn
			    (format t "Enter Type>")
			    (setq dtp (read-dtype1-nodb namedectx (read-line)))
			    (if dtp
				(if (dtype-returns-pf-p dtp)
				    (let ((mctx (build-minimal-ctx (dtype-free-bvars dtp)
								   ctxi)))
				      (if (subctx mctx argctx)
					  (let ((fdtp (prefix-dpi-db argctx dtp))
						(now *timestamp*))
					    (setq *timestamp* (- *scip-timestamp* 1.5)) ; time travel
					    (newclaim name (normalize-type fdtp) nil)
					    (setq *timestamp* now)
					    (push name *scip-lemmas*)
					    (when (deptype1-p dtp)
					      (scip-add-fact
					       (app-n name
						      (mapcar #'(lambda (x)
								  (named-term-to-db namedectx x))
							      expldeps))
					       (named-type-to-db namedectx
								 dtp))))
					(format t "Hidden Dependency for new lemma ~d~%" name)))
				  (format t "Lemma does not return pf type.~%"))
			      (format t "Could not parse dtype1.~%")))))))
 		    ((string= cmd "claimtype") ; more general case with hyps
 		     (format t "Enter Type>")
 		     (let* ((e (read-dtype1 namedectx)))
 		       (if e
			   (if (dtype-returns-pf-p e)
			       (progn
				 (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				 (pop *scip-tasks*)
				 (multiple-value-setq
				  (*scip-tasks* *scip-theta*)
				  (task-claim e task *scip-tasks* *scip-theta*))
				 )
			     (format t "claimtype does not return pf type.~%"))
 			 (format t "Could not parse dtype1.~%"))))
 		    ((string= cmd "claim") ; splits proof in two - island step
 		     (format t "Enter Proposition>")
 		     (let* ((e (read-extract1-prop namedectx)))
 		       (if e
 			   (progn
 			     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
 			     (pop *scip-tasks*)
 			     (multiple-value-setq
 			      (*scip-tasks* *scip-theta*)
 			      (task-claim (pf e) task *scip-tasks* *scip-theta*))
 			     )
 			 (format t "Could not parse proposition.~%"))))
 					; specialized rules
 		    ((string= cmd "contradiction")
 		     (let ((C (pf-prop tp))
 			   (pffalse (pf '|false|)))
 		       (if (eq C '|false|)
 			   (format t "You are already proving false, task unchanged.~%")
			 (if (and (app-p C)
				  (eq (app-func C) '|not|))
			     (let* ((D (app-arg C))
				    (pffalse (pf '|false|))
				    (newevar (intern-gensym))
				    (trm1 (app-n-1-to-0 (length ctx) newevar))
				    (trm (app (app '|notI| D) trm1))
				    (tp2 (dpi (pf D) pffalse)))
			       (setf (get newevar 'evar) t)
			       (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
			       (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
			       (dotimes (n (length ctx)) (setq trm (lam trm)))
			       (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
			       (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							(cdr *scip-tasks*)))
			       (format t "OK~%")
			       )
			   (let* ((newevar (intern-gensym))
 				(trm1 (app-n-1-to-0 (length ctx) newevar))
 				(trm (app (app '|contradiction| C) trm1))
 				(tp2 (dpi (pf (app '|not| C)) pffalse)))
 			   (setf (get newevar 'evar) t)
 			   (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
 			   (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
 			   (dotimes (n (length ctx)) (setq trm (lam trm)))
			   (format t "OK~%")
 			   (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
 			   (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
 						    (cdr *scip-tasks*))))))))
 		    ((string= cmd "intro")
 		     (let ((C (pf-prop tp)))
		       (cond ((and (app-p C) (eq (app-func C) '|not|))
			      (let* ((D (app-arg C))
				     (pffalse (pf '|false|))
				     (newevar (intern-gensym))
				     (trm1 (app-n-1-to-0 (length ctx) newevar))
				     (trm (app (app '|notI| D) trm1))
				     (tp2 (dpi (pf D) pffalse)))
				(setf (get newevar 'evar) t)
				(setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				(dotimes (n (length ctx)) (setq trm (lam trm)))
				(setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				(setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							 (cdr *scip-tasks*)))
				(format t "OK~%")
				))
			     ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|imp|))
			      (let* ((A (app-arg (app-func C)))
				     (B (app-arg C))
				     (newevar (intern-gensym))
				     (trm1 (app-n-1-to-0 (length ctx) newevar))
				     (trm (app (app (app '|impI| A) B) trm1))
				     (tp2 (dpi (pf A) (pf (dbshift-n 1 B)))))
				(setf (get newevar 'evar) t)
				(setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				(dotimes (n (length ctx)) (setq trm (lam trm)))
				(setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				(setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							 (cdr *scip-tasks*)))
				(format t "OK~%")
				))
			     ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|dimp|))
			      (let* ((A (app-arg (app-func C)))
				     (B (app-arg C))
				     (newevar (intern-gensym))
				     (trm1 (app-n-1-to-0 (length ctx) newevar))
				     (trm (app (app (app '|dimpI| A) B) trm1))
				     (tp2 (dpi (pf A) (pf (normalize (app (dbshift-n 1 B) 0))))))
				(setf (get newevar 'evar) t)
				(setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				(dotimes (n (length ctx)) (setq trm (lam trm)))
				(setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				(setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							 (cdr *scip-tasks*)))
				(format t "OK~%")
				))
			     ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|dall|))
			      (let* ((A (app-arg (app-func C)))
				     (B (app-arg C))
				     (newevar (intern-gensym))
				     (trm1 (app-n-1-to-0 (length ctx) newevar))
				     (trm (app (app (app '|dallI| A) B) trm1))
				     (tp2 (dpi (dclass (app '|in| A)) (pf (normalize (app (dbshift-n 1 B) 0))))))
				(setf (get newevar 'evar) t)
				(setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				(dotimes (n (length ctx)) (setq trm (lam trm)))
				(setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				(setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							 (cdr *scip-tasks*)))
				(format t "OK~%")
				))
			     ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|and|))
			      (let* ((A (app-arg (app-func C)))
				     (B (app-arg C))
				     (newevar1 (intern-gensym))
				     (newevar2 (intern-gensym))
				     (trm1 (app-n-1-to-0 (length ctx) newevar1))
				     (trm2 (app-n-1-to-0 (length ctx) newevar2))
				     (trm (app (app (app (app '|andI| A) B) trm1) trm2))
				     (tp1 (pf A))
				     (tp2 (pf B))
				     )
				(setf (get newevar1 'evar) t)
				(setf (get newevar1 'dbtype) (dpi-ctx ctx tp1))
				(setf (get newevar2 'evar) t)
				(setf (get newevar2 'dbtype) (dpi-ctx ctx tp2))
				(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				(dotimes (n (length ctx)) (setq trm (lam trm)))
				(setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				(setq *scip-tasks* (cons (list newevar1 ctx names tp1 namedectx namesubst)
							 (cons (list newevar2 ctx names tp2 namedectx namesubst)
							       (cdr *scip-tasks*))))
				(format t "OK~%")
				))
			     ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|dand|))
			      (let* ((A (app-arg (app-func C)))
				     (B (app-arg C))
				     (newevar1 (intern-gensym))
				     (newevar2 (intern-gensym))
				     (trm1 (app-n-1-to-0 (length ctx) newevar1))
				     (trm2 (app-n-1-to-0 (length ctx) newevar2))
				     (trm (app (app (app (app '|dandI| A) B) trm1) (app trm2 trm1)))
				     (tp1 (pf A))
				     (tp2 (dpi (pf A) (pf (normalize (app (dbshift-n 1 B) 0)))))
				     )
				(setf (get newevar1 'evar) t)
				(setf (get newevar1 'dbtype) (dpi-ctx ctx tp1))
				(setf (get newevar2 'evar) t)
				(setf (get newevar2 'dbtype) (dpi-ctx ctx tp2))
				(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				(dotimes (n (length ctx)) (setq trm (lam trm)))
				(setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				(setq *scip-tasks* (cons (list newevar1 ctx names tp1 namedectx namesubst)
							 (cons (list newevar2 ctx names tp2 namedectx namesubst)
							       (cdr *scip-tasks*))))
				(format t "OK~%")
				))
			     ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|subset|))
			      (let* ((A (app-arg (app-func C)))
				     (B (app-arg C))
				     (newevar (intern-gensym))
				     (trm1 (app-n-1-to-0 (length ctx) newevar))
				     (trm (app (app (app '|subsetI1| A) B) trm1))
				     (tp2 (dpi (dclass (app '|in| A)) (pf (app (app '|in| (dbshift-n 1 B)) (fst 0))))))
				(setf (get newevar 'evar) t)
				(setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				(dotimes (n (length ctx)) (setq trm (lam trm)))
				(setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				(setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							 (cdr *scip-tasks*)))
				(format t "OK~%")
				))
			     ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|eq|))
			      (let* ((A (app-arg (app-func C)))
				     (B (app-arg C))
				     (A* (if (fst-p A) (fst-arg A)))
				     (B* (if (fst-p B) (fst-arg B)))
				     (A*tp (if (and A* B*) (ctx-extract-type ctx A*)))
				     (B*tp (if (and A* B*) (ctx-extract-type ctx B*))))
				(if (and A*tp B*tp
					 (dclass-p A*tp)
					 (dclass-p B*tp)
					 (app-p (dclass-pred A*tp))
					 (app-p (dclass-pred B*tp))
					 (eq (app-func (dclass-pred A*tp)) '|in|)
					 (eq (app-func (dclass-pred B*tp)) '|in|)
					 (app-p (app-arg (dclass-pred A*tp)))
					 (app-p (app-arg (dclass-pred B*tp)))
					 (app-p (app-func (app-arg (dclass-pred A*tp))))
					 (app-p (app-func (app-arg (dclass-pred B*tp))))
					 (eq (app-func (app-func (app-arg (dclass-pred A*tp)))) '|funcSet|)
					 (eq (app-func (app-func (app-arg (dclass-pred B*tp)))) '|funcSet|))
				    (let ((domset (app-arg (app-func (app-arg (dclass-pred A*tp)))))
					  (codset (app-arg (app-arg (dclass-pred A*tp)))))
				      (if (and (ctx-terms-eq-type ctx
								  domset
								  (app-arg (app-func (app-arg (dclass-pred B*tp))))
								  (obj))
					       (ctx-terms-eq-type ctx
								  codset
								  (app-arg (app-arg (dclass-pred B*tp)))
								  (obj)))
					  (let* ((newevar (intern-gensym))
						 (trm1 (app-n-1-to-0 (length ctx) newevar))
						 (trm (app-n '|funcext2|
							     (list domset codset A* B* trm1)))
						 (tp2 (dpi (dclass (app '|in| domset)) (pf (app-n '|eq|
												  (list (fst (app-n '|ap2|
														    (list
														     (dbshift-n 1 domset)
														     (dbshift-n 1 codset)
														     (dbshift-n 1 A*)
														     0)))
													(fst (app-n '|ap2|
														    (list
														     (dbshift-n 1 domset)
														     (dbshift-n 1 codset)
														     (dbshift-n 1 B*)
														     0)))))))))
					    (setf (get newevar 'evar) t)
					    (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
					    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					    (dotimes (n (length ctx)) (setq trm (lam trm)))
					    (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
					    (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
								     (cdr *scip-tasks*)))
					    (format t "OK~%")
					    )
					(format t "intro not applicable to this goal~%")))
				  (let* ((newevar1 (intern-gensym))
					 (newevar2 (intern-gensym))
					 (trm1 (app-n-1-to-0 (length ctx) newevar1))
					 (trm2 (app-n-1-to-0 (length ctx) newevar2))
					 (trm (app (app (app (app '|setextsub| A) B) trm1) trm2))
					 (tp1 (pf (app (app '|subset| A) B)))
					 (tp2 (pf (app (app '|subset| B) A)))
					 )
				    (setf (get newevar1 'evar) t)
				    (setf (get newevar1 'dbtype) (dpi-ctx ctx tp1))
				    (setf (get newevar2 'evar) t)
				    (setf (get newevar2 'dbtype) (dpi-ctx ctx tp2))
				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				    (dotimes (n (length ctx)) (setq trm (lam trm)))
				    (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				    (setq *scip-tasks* (cons (list newevar1 ctx names tp1 namedectx namesubst)
							     (cons (list newevar2 ctx names tp2 namedectx namesubst)
								   (cdr *scip-tasks*))))
				    (format t "OK~%")
				    ))))
			     ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|equiv|))
			      (let* ((C (pf-prop tp))
				     (name (term-extr-head C)))
				(if (abbrevname-p name)
				    (let* ((args (term-extr-args C))
					   (e1 (app-n (intern (format nil "~d#F" name)) args))
					   (e1tp (ctx-extract-type ctx e1)))
				      (if (and e1tp (dpi-p e1tp)
					       (pf-p (dpi-dom e1tp)))
					  (multiple-value-bind
					   (tasklist2 theta2)
					   (task-claim (dpi-dom e1tp) task (cdr *scip-tasks*) *scip-theta*)
					   (multiple-value-bind
					    (evar1 ctx1 names1 tp1 namedectx1 namesubst1)
					    (task-components (car tasklist2))
					    (let ((e (app (dbshift-n 1 e1) 0)))
					      (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					      (setq *scip-tasks* (cdr tasklist2))
					      (setq *scip-theta*
						    (compose-theta-1
						     evar1
						     (lam-ctx ctx1 e)
						     theta2))
					      (format t "OK~%"))))
					(format t "Problem intro'ing abbrev at head of goal.~%There is no excuse for this failure.~%")))
				  (format t "Problem intro'ing abbrev at head of goal.~%There is no excuse for this failure.~%"))))
			     (t
			      (format t "You are not proving something to intro, task unchanged.~%")))))
		    ((and *auto-gen-congruence* (> *congruences-stage* 1)
			  (> (length cmd) 11) (string-equal cmd "unfoldgoal " :start1 0 :end1 11))
		     (let ((name (intern (subseq cmd 11))))
		       (if (get name 'abbrev)
			   (if (member name (sig-elts (pf-prop tp)))
			       (let ((d (delta-reduce-abbrevs ctx (pf-prop tp) (prop) (list name))))
;				 (setq *ctx* ctx *d* d *tp* tp)
				 (if (and d (not (heq d (pf-prop tp))))
				     (let ((pftrm (congruence-make-equation-pf
						   ctx d (pf-prop tp) (prop))))
				       (when (> *verbose* 30)
					 (format t "After Unfolding:~%~d~2%" (output1-extraction-string d names t))
					 (format t "Before Unfolding:~%~d~2%" (output1-extraction-string (pf-prop tp) names t))
					 (setq *output1-skip-snd* t)
					 (format t "After Unfolding:~%~d~2%" (output1-extraction-string d names t))
					 (format t "Before Unfolding:~%~d~2%" (output1-extraction-string (pf-prop tp) names t))
					 (setq *output1-skip-snd* nil))
				       (if pftrm
					   (multiple-value-bind
					    (tasklist2 theta2)
					    (task-claim (pf d) task (cdr *scip-tasks*) *scip-theta*)
					    (let ((task1 (car tasklist2)))
					      (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					      (setq *scip-tasks* (cdr tasklist2))
					      (setq *scip-theta*
						    (compose-theta-1
						     (car task1)
						     (lam-ctx ctx
							      (app-n '|equivEimp1| (list d (pf-prop tp) pftrm)))
						     theta2))))
					 (format t "Problem automatically unfolding abbrev in goal (1).~%")))
				   (format t "Problem automatically unfolding abbrev in goal (2).~%")))
			     (format t "~d does not occur in goal.~%" name))
			 (format t "~d is not an abbreviation.~%" name))))
		    ((and *auto-gen-congruence* (> *congruences-stage* 1)
			  (> (length cmd) 7) (string-equal cmd "unfold " :start1 0 :end1 7))
		     (let ((name (intern (subseq cmd 7))))
		       (if (get name 'abbrev)
			   (let ((a-in-ctx nil))
			     (do ((ctx9 ctx (cdr ctx9))
				  (k 0 (1+ k)))
				 ((or a-in-ctx (null ctx9)))
				 (when (and (pf-p (car ctx9))
					    (member name (sig-elts (pf-prop (car ctx9)))))
				   (setq a-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
			     (if a-in-ctx
				 (let* ((oldprop (pf-prop (cdr a-in-ctx)))
					(k (car a-in-ctx))
					(d (delta-reduce-abbrevs ctx (pf-prop (cdr a-in-ctx)) (prop) (list name))))
				   (if (and d (not (heq d oldprop)))
				       (let ((pftrm (congruence-make-equation-pf
						     ctx d oldprop (prop))))
					 (if pftrm
					     (multiple-value-bind
					      (tasklist2 theta2)
					      (task-claim (pf d) task (cdr *scip-tasks*) *scip-theta*)
					      (let ((task1 (cadr tasklist2)))
						(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
						(setq *scip-tasks* (cons (car tasklist2) (cddr tasklist2)))
						(setq *scip-theta*
						      (compose-theta-1
						       (car task1)
						       (lam-ctx ctx
								(app-n '|equivEimp2| (list d oldprop pftrm k)))
						       theta2))))
					   (format t "Problem automatically unfolding abbrev in support (1).~%")))
				     (format t "Problem automatically unfolding abbrev in support (2).~%")))
			       (format t "~d was not found in the support.~%" name)))
			 (format t "~d is not an abbreviation.~%" name))))
		    ((or (string-equal cmd "unfoldgoalhead") (string-equal cmd "fh"))
 		     (let* ((C (pf-prop tp))
			    (name (term-extr-head C)))
		       (if (abbrevname-p name)
			   (let* ((args (term-extr-args C))
				  (e1 (app-n (intern (format nil "~d#F" name)) args))
				  (e1tp (ctx-extract-type ctx e1)))
			     (if (and e1tp (dpi-p e1tp)
				      (pf-p (dpi-dom e1tp)))
				 (multiple-value-bind
				  (tasklist2 theta2)
				  (task-claim (dpi-dom e1tp) task (cdr *scip-tasks*) *scip-theta*)
				  (multiple-value-bind
				   (evar1 ctx1 names1 tp1 namedectx1 namesubst1)
				   (task-components (car tasklist2))
				   (let ((e (app (dbshift-n 1 e1) 0)))
				     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				     (setq *scip-tasks* (cdr tasklist2))
				     (setq *scip-theta*
					   (compose-theta-1
					    evar1
					    (lam-ctx ctx1 e)
					    theta2))
				     (format t "OK~%"))))
			       (format t "Problem folding abbrev at head of goal.~%There is no excuse for this failure.~%")))
			 (format t "Head of goal is not an abbrev~%"))))
		    ((or (string-equal cmd "unfoldhead") (string-equal cmd "ufh"))
		     (let ((name nil)
			   (i nil))
		       (do ((j 0 (1+ j))
			    (ctx2 ctx (cdr ctx2)))
			   ((or i (null ctx2)))
			   (when (pf-p (car ctx2))
			     (setq name (term-extr-head (pf-prop (car ctx2))))
			     (when (and (symbolp name) (abbrevname-p name))
			       (setq i j))))
		       (if i
			   (let* ((pfprop (ctx-extract-type ctx i))
				  (prop (pf-prop pfprop))
				  (args (term-extr-args prop))
				  (h (intern (format nil "~d#U" name)))
				  (e (app (app-n h args) i))
				  (newtp
				   (ctx-extract-type ctx e)))
			     (if newtp
				 (progn
				   (scip-add-fact e newtp)
				   (format t "OK~%"))
			       (format t "Error expanding abbreviation ~d.~%There is no excuse for this.~%" name)))
			 (format t "Could not identify context element with abbrev at head~%"))))
		    ((and (> (length cmd) 11) (string-equal cmd "unfoldhead " :start1 0 :end1 11))
		     (let ((name (intern (subseq cmd 11)))
			   (i nil))
		       (if (abbrevname-p name)
			   (do ((j 0 (1+ j))
				(ctx2 ctx (cdr ctx2)))
			       ((or i (null ctx2)))
			       (when (and (pf-p (car ctx2))
					  (eq (term-extr-head (pf-prop (car ctx2))) name))
				 (setq i j)))
			 (setq i (position name names :test #'string=)))
		       (if i
			   (let* ((pfprop (ctx-extract-type ctx i))
				  (prop (pf-prop pfprop))
				  (args (term-extr-args prop))
				  (h (intern (format nil "~d#U" (term-extr-head prop))))
				  (e (app (app-n h args) i))
				  (newtp
				   (ctx-extract-type ctx e)))
			     (if newtp
				 (progn
				   (scip-add-fact e newtp)
				   (format t "OK~%"))
			       (format t "Error expanding abbreviation ~d.~%There is no excuse for this.~%" name)))
			 (format t "Could not identify context element with abbrev at head~%"))))
		    ((and *auto-gen-congruence* (> *congruences-stage* 1)
			  (string-equal cmd "args=")) ; reduce showing an equation to showing args are equal (using #Cong)
		     (let ((C (pf-prop tp)))
		       (if (and (app-p C) (app-p (app-func C))
				(or (eq (app-func (app-func C)) '|eq|)
				    (eq (app-func (app-func C)) '|equiv|)))
			   (let* ((lhs (app-arg (app-func C)))
				  (rhs (app-arg C))
				  (lhsh (term-extr-head lhs))
				  (rhsh (term-extr-head rhs)))
			     (if (equal lhsh rhsh)
				 (if (symbolp lhsh)
				     (let ((cc (auto-gen-name lhsh "Cong" nil)))
				       (if (and (get cc 'dbtype) (equal (get cc 'dbtype)
									(congruence-pf-type (get lhsh 'dbtype) lhsh)))
					   (let ((pftrm cc)
						 (largs (term-extr-args lhs))
						 (rargs (term-extr-args rhs))
						 (altp nil)
						 (artp nil)
						 (cctp (get cc 'dbtype))
						 (tasks2 (cdr *scip-tasks*)))
					     (do ((tph (get lhsh 'dbtype) (dpi-cod tph)))
						 ((not (dpi-p tph)))
						 (setq altp (dpi-dom cctp))
						 (setq cctp (normalize-type (dbsubst-type-0 (dpi-cod cctp) (car largs))))
						 (setq artp (dpi-dom cctp))
						 (setq cctp (normalize-type (dbsubst-type-0 (dpi-cod cctp) (car rargs))))
						 (let ((apftrm (if (heq altp artp)
								   (congruence-make-equation-pf ctx (car largs) (car rargs)
												altp)
								 nil)))
						   (if apftrm
						       (progn
							 (setq cctp (normalize-type (dbsubst-type-0 (dpi-cod cctp) apftrm)))
							 (setq pftrm (app (app (app pftrm (car largs)) (car rargs))
									  apftrm))
							 )
						     (let ((newevar (intern-gensym)))
						       (setf (get newevar 'evar) t)
						       (setf (get newevar 'dbtype) (dpi-ctx ctx (dpi-dom cctp)))
						       (push (list newevar ctx names (dpi-dom cctp) namedectx namesubst) tasks2)
						       (let ((newevar-ap (app-n-1-to-0 (length ctx) newevar)))
							 (setq cctp (normalize-type (dbsubst-type-0 (dpi-cod cctp) newevar-ap)))
							 (setq pftrm (app (app (app pftrm (car largs)) (car rargs))
									  newevar-ap)))))
						   (pop largs)
						   (pop rargs)
						   ))
					     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					     (setq pftrm (lam-ctx ctx pftrm))
					     (setq *scip-theta* (compose-theta-1 evar pftrm *scip-theta*))
					     (setq *scip-tasks* tasks2)
					     (format t "OK~%"))					     
					 (format t "Congruence Problem with ~d~%" lhsh)))
				   (format t "Cannot apply congruence with local head~%"))
			       (format t "Sides of equation do not have matching heads: ~d =/= ~d~%" lhsh rhsh)))
			 (format t "Goal is not an equation~%"))))
		    ((and *auto-gen-congruence* (> *congruences-stage* 1)
			  (string-equal cmd "reducegoal")) ; do some "reductions" to the goal
		     (let ((C (pf-prop tp)))
		       (cond ((and (app-p C) (app-p (app-func C))
				   (eq (app-func (app-func C)) '|eq|))
			      (let* ((lhs (app-arg (app-func C)))
				     (rhs (app-arg C)))
				(multiple-value-bind
				 (rlhs lpftrm)
				 (reduce-obj ctx lhs)
				 (multiple-value-bind
				  (rrhs rpftrm)
				  (reduce-obj ctx rhs)
				  (if lpftrm
				      (if rpftrm
					  (let* ((newgoal (app-n '|eq| (list rlhs rrhs)))
						 (newevar (intern-gensym))
						 (newevar-ap (app-n-1-to-0 (length ctx) newevar)))
					    (setf (get newevar 'evar) t)
					    (setf (get newevar 'dbtype) (dpi-ctx ctx (pf newgoal)))
					    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					    (setq *scip-theta* (compose-theta-1
								evar
								(lam-ctx ctx
									 (app-n '|boxeq|
										(list
										 lhs rlhs
										 rhs rrhs
										 lpftrm rpftrm
										 newevar-ap)))
								*scip-theta*))
					    (setq *scip-tasks* (cons
								(list newevar ctx names (pf newgoal) namedectx namesubst)
								(cdr *scip-tasks*)))
					    (format t "OK~%"))
					(let* ((newgoal (app-n '|eq| (list rlhs rhs)))
						 (newevar (intern-gensym))
						 (newevar-ap (app-n-1-to-0 (length ctx) newevar)))
					    (setf (get newevar 'evar) t)
					    (setf (get newevar 'dbtype) (dpi-ctx ctx (pf newgoal)))
					    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					    (setq *scip-theta* (compose-theta-1
								evar
								(lam-ctx ctx
									 (app-n '|boxeq|
										(list
										 lhs rlhs
										 rhs rhs
										 lpftrm (app '|eqI| rhs)
										 newevar-ap)))
								*scip-theta*))
					    (setq *scip-tasks* (cons
								(list newevar ctx names (pf newgoal) namedectx namesubst)
								(cdr *scip-tasks*)))
					    (format t "OK~%")))
				    (if rpftrm
					(let* ((newgoal (app-n '|eq| (list lhs rrhs)))
					       (newevar (intern-gensym))
					       (newevar-ap (app-n-1-to-0 (length ctx) newevar)))
					  (setf (get newevar 'evar) t)
					  (setf (get newevar 'dbtype) (dpi-ctx ctx (pf newgoal)))
					  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					  (setq *scip-theta* (compose-theta-1
							      evar
							      (lam-ctx ctx
								       (app-n '|boxeq|
									      (list
									       lhs lhs
									       rhs rrhs
									       (app '|eqI| lhs) rpftrm
									       newevar-ap)))
							      *scip-theta*))
					  (setq *scip-tasks* (cons
							      (list newevar ctx names (pf newgoal) namedectx namesubst)
							      (cdr *scip-tasks*)))
					  (format t "OK~%"))
				      (format t "Cannot reduce goal~%")))))))
			     (t (format t "Cannot reduce goal~%")))))
;		      (if redprop
;			  (multiple-value-bind
;			   (tasklist2 theta2)
;			   (task-claim (pf redprop) task (cdr *scip-tasks*) *scip-theta*)
;			   (let ((task1 (car tasklist2)))
;			     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
;			     (setq *scip-tasks* (cdr tasklist2))
;			     (setq *scip-theta*
;				   (compose-theta-1
;				    (car task1)
;				    (lam-ctx ctx
;					     (app-n '|equivEimp2| (list (pf-prop tp) redprop pftrm)))
;				    theta2))))
;			(format t "No reductions apply to goal"))))
 		    (t nil)))))))
    (let ((trm (normalize (cdr (assoc *scip-gevar* *scip-theta*)))))
      (setq *trm* trm) ; delete me
      (cond ((free-evars trm)
 	     (format t "Term has remaining free evars~%"))
 	    ((not (ctx-term-type-p *emptyctx* trm *scip-gtp*))
 	     (format t "Term does not have the right tp~%"))
	    (claim
	     (let ((q nil)
		   (r nil))
	       (format t "Output PAM Proof Term to File [y/n, Default y]>")
	       (setq q (read-line))
	       (unless (or (string= (string-downcase q) "n") (string= (string-downcase q) "no"))
		 (format t "Filename [Default File ~d]>" *scip-pam-proof-file*)
		 (setq r (read-line))
		 (unless (equal r "")
		   (when r (setq *scip-pam-proof-file* r)))
		 (let ((f (open *scip-pam-proof-file* :direction :output
				:if-does-not-exist :create
				:if-exists :append)))
		   (output1-sig (reverse *scip-lemmas*) f)
		   (format f "~d:=~d.~%" claim (output1-normal-string trm))
		   (close f)))
	       (format t "Output Lisp Proof Term to File [y/n, Default y]>")
	       (setq q (read-line))
	       (unless (or (string= (string-downcase q) "n") (string= (string-downcase q) "no"))
		 (format t "Filename [Default File ~d]>" *scip-lisp-proof-file*)
		 (setq r (read-line))
		 (unless (equal r "")
		   (when r (setq *scip-lisp-proof-file* r)))
		 (let ((f (open *scip-lisp-proof-file* :direction :output
				:if-does-not-exist :create
				:if-exists :append)))
		   (output-sig (reverse *scip-lemmas*) f)
		   (format f "(claim2abbrev '~S~%~d~%)~%" claim (output-term-string trm))
		   (close f)))
	       (claim2abbrev claim trm)
	       ))
 	    (t
 	     (format t "Successful Term:~%~d~%~d~%"
 		     (output-term-string trm)
 		     (output1-normal-string trm))))
      (format t "Scip Out!~%")
      )))

(defun read-dtype1-nodb (namedectx r)
  (let* ((words (tokenize-str r))
	 (n (length words))
	 (ch (earley-parse-string 'DTYPE1 r input1-grammar))
	 (res (chart-to-parse-trees words 0 n 'DTYPE1 input1-grammar ch)))
    (if res
	(let ((pre-tp (car res)))
	  (multiple-value-bind
	   (tp info fail)
	   (deptype-fill-in-blanks pre-tp *input1-state* namedectx)
	   (if (or info fail)
	       nil
	     (if (deptype1-p tp) ; check before switching to dbruijn indices
		 (normalize-type tp)
	       nil))))
      nil)))

(defun input1-ctx-info-from-named-ectx (namedectx)
  (if namedectx
      (let* ((ctxi (input1-ctx-info-from-named-ectx (cdr namedectx)))
	     (frees (dtype-free-bvars (cadar namedectx)))
	     (mctx (build-minimal-ctx frees ctxi)))
	(cons (list (caar namedectx)
		    (cons (list (caar namedectx) (cadar namedectx)) mctx))
	      ctxi))
    nil))

(defun extract-locvars (str)
  (let ((locvars nil)
	(name ""))
    (dotimes (i (length str))
      (let ((c (aref str i)))
	(if (member c '(#\space))
	    (unless (equal name "")
	      (push (intern name) locvars)
	      (setq name ""))
	  (setq name (format nil "~d~d" name c)))))
    (unless (equal name "")
      (push (intern name) locvars))
    (reverse locvars)))

(defun scip-1-sock (&optional claim)
  (let* ((evar nil)
	 (ctx nil)
	 (names nil)
	 (tp nil)
	 (namedectx nil)
	 (namesubst 'ID)
	 (task nil)
	 (giveup nil)
	 )
    (loop while (and *scip-tasks* (not giveup)) do
	  (setq task (car *scip-tasks*))
	  (setq evar (car task))
	  (setq ctx (cadr task))
	  (setq names (nth 2 task))
	  (setq tp (nth 3 task))
	  (setq namedectx (nth 4 task))
	  (setq namesubst (nth 5 task))
	  (do ((nctx9 (reverse namedectx) (cdr nctx9))
	       (prev9 nil (cons (list (caar nctx9) (cadar nctx9)) prev9)))
	      ((null nctx9))
	      (push (list (caar nctx9) (cons (list (caar nctx9) (cadar nctx9)) prev9)) *input1-ctx-info*))
	  (unless (ctx-type-valid-p ctx tp)
	    (fail "bad task ctx tp" ctx tp))
	  (if (dpi-p tp)
	      (progn
		(let* ((z (if (dtype-returns-pf-p (dpi-dom tp))
			      (format nil "ass~d" (incf *scip-assnum*))
			    (progn
			      (format t "Give name for ~d>" (output1-type-string (dpi-dom tp) names))
			      (force-output *standard-output*)
			      (scu-out 'PROMPT-NAME)
			      (read-scunak-socket-line))))
		       (zz (if (equal z "")
			       (let ((g (intern-gensym "a")))
				 (format t "Please enter a name.  If you hit return again, I will use the name ~d.~%" g)
				 (format t "Give name for ~d>" (output1-type-string (dpi-dom tp) names))
				 (force-output *standard-output*)
				 (scu-out 'PROMPT-NAME)
				 (let ((h (read-scunak-socket-line)))
				   (if (equal h "")
				       (progn
					 (setq z (format nil "~d" g))
					 g)
				     (progn
				       (setq z h)
				       (intern h)))))
			     (intern z))))
		  (setf (get zz 'bvar) t)
		  (setf (get zz 'dbtype) (dbsubst-type (dpi-dom tp) #'identity namesubst))
		  (let ((ctx2 (ctx-cons (dpi-dom tp) ctx)))
		    (pop *scip-tasks*)
		    (push (list evar ctx2 (cons z names) (dpi-cod tp)
				(cons (list zz (get zz 'dbtype)) namedectx)
				(cons zz (cons #'identity namesubst)))
			  *scip-tasks*))))
	    (multiple-value-bind
	     (succ1 tasklist1 theta1)
	     (if *scip-eager-elims*
		 (task-close-under-simple-elims task (cdr *scip-tasks*) *scip-theta*)
	       nil)
	     (if succ1
		 (progn
					;		   (push (list *scip-tasks* *scip-theta*) *scip-taskstack*) ; otherwise undo stops working
		   (setq *scip-tasks* tasklist1)
		   (setq *scip-theta* theta1)
		   )
	       (let ((r (progn
			  (force-output *standard-output*)
			  (scu-out 'READY-SCIP)
			  (read *scunak-socket* nil nil))))
		 (unless (and (open-stream-p *scunak-socket*)
			      (open-stream-p *standard-output*))
		   (setq giveup t)
		   (setq r nil)
		   )
		 (when r
		   (unless (consp r)
		     (setq r (list r)))
		   (case (car r)
			 (PSTATUS
			  (let ((i 0))
			    (dolist (task *scip-tasks*)
			      (format t "~d) ~d ~d~%" i (nth 2 task) (output1-type-string (nth 3 task) (nth 2 task)))
			      (scu-out (list i (nth 2 task) (nth 3 task)))
			      (incf i))))
			 (PTERM ; print current proof term
			  (format t "Current Pf Term:~%~d~%" (output1-normal-string (normalize (cdr (assoc *scip-gevar* *scip-theta*)))))
			  (scu-out (normalize (cdr (assoc *scip-gevar* *scip-theta*)))))
			 (CHKTERM ; check current proof term
			  (if (ctx-term-type-p *emptyctx* (normalize (cdr (assoc *scip-gevar* *scip-theta*))) *scip-gtp*)
			      (progn
				(scu-out 'OK)
				(format t "Current Pf Term OK~%"))
			    (progn
			      (scu-out 'ILL-TYPED)
			      (format t "Current Pf Term NOT OK - ill-typed~%"))))
			 (LISP (eval (cadr r)))
			 (USE ; made this just like main top level version of use
			  (let ((xl (cdr r)))
			    (setq xl (mapcar #'(lambda (x)
						 (if (stringp x) (intern x) x)) xl))
			    (if (member '|all| xl)
				(setq *scip-usable* *global-sigma*)
			      (if (member '|none| xl)
				  (setq *scip-usable* nil)
				(progn
				  (setq *scip-usable* nil)
				  (dolist (x xl)
				    (cond ((eq x '|fo|)
					   (setq *scip-usable*
						 (union (remove-if-not #'(lambda (co)
									   (and (not (get co 'auto-gen)) (or (get co 'fo-unif-type) (get co 'fo-type))))
								       *global-sigma*)
							*scip-usable*)))
					  ((eq x '|defns|)
					   (setq *scip-usable*
						 (union (remove-if-not #'(lambda (co)
									   (get co 'auto-gen))
								       *scip-sigma*)
							*scip-usable*)))
					  ((eq x '|so|)
					   (setq *scip-usable*
						 (union (remove-if #'(lambda (co)
								       (or (get co 'auto-gen) (get co 'fo-unif-type) (get co 'fo-type)))
								   *global-sigma*)
							*scip-usable*)))
					  ((and (get x 'dbtype) (or (dtype-returns-dclass-p (get x 'dbtype))
								    (dtype-returns-pf-p (get x 'dbtype))))
					   (push x *scip-usable*)
					   )
					  (t (format t "Ignoring ~d~%" x)))))))
			    (if *scip-usable*
				(format t "Reset usable~%")
			      (format t "WARNING: usable empty!~%"))))
			 (UNIF+
			  (format t "~d~%" (incf *preunify-msv-goal*))
			  (format t "~d~%" (incf *preunify-msv-hence*))
			  (format t "~d~%" (incf *preunify-msv-supp*)))
			 (UNIF-
			  (format t "~d~%" (decf *preunify-msv-goal*))
			  (format t "~d~%" (decf *preunify-msv-hence*))
			  (format t "~d~%" (decf *preunify-msv-supp*)))
			 ((PPLAN PPLAN*)
			  (when ctx
			    (format t "Support (Objects, Assumptions and Derived Facts in Context):~%")
			    (let ((tmpl nil))
			      (do ((names2 names (cdr names2))
				   (ectx2 ctx (cdr ectx2)))
				  ((or (null names2) (null ectx2)))
				  (scu-out (list 'SUPPORT (car names2) (car ectx2) (cdr names2)))
				  (push (format nil "~d:~d" (car names2) (output1-type-string (car ectx2) (cdr names2))) tmpl))
			      (dolist (tmp tmpl)
				(format t "~d~%" tmp))))
			  (scu-out (list 'GOAL tp names))
			  (format t "Goal (What you need to show): ~d~%"
				  (output1-type-string tp names)))
			 ((UNDO U)
			  (if *scip-taskstack*
			      (let ((z (pop *scip-taskstack*)))
				(setq *scip-tasks* (car z))
				(setq *scip-theta* (cadr z)))
			    (progn
			      (scu-out 'NO-MORE-UNDO)
			      (format t "No previous list of plans~%"))))
			 (SAVEPROOF
			  (let ((filename (cadr r)))
			    (save-scip-proof filename)))
			 (RESTOREPROOF
			  (let ((filename (cadr r)))
			    (load filename)
			    (dolist (bv (nth 4 (car *scip-tasks*)))
			      (setf (get (car bv) 'bvar) t)
			      (setf (get (car bv) 'dbtype) (cadr bv)))))
			 (Q (setq giveup t))
			 ((CHOOSE-TASK CTK)
			  (format t "Enter a number between 0 and ~d~%" (- (length *scip-tasks*) 1))
			  (let ((z (progn (scu-out (list 'PROMPT-NUM (- (length *scip-tasks*) 1))) (read *scunak-socket* nil nil))))
			    (if (and (numberp z) (nth z *scip-tasks*))
				(let ((y (nth z *scip-tasks*)))
				  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				  (setq *scip-tasks* (cons y (remove y *scip-tasks*))))
			      (progn
				(scu-out 'TASK-UNCHANGED-BAD-CHOICE)
				(format t "Task Unchanged: ~d is not a number between 0 and ~d~%" z (- (length *scip-tasks*) 1))))))
			 (D
			  (multiple-value-bind
			   (succ theta)
			   (task-done task *scip-theta* nil)
			   (if succ
			       (progn
				 (setq *scip-theta* theta)
				 (pop *scip-tasks*)
				 (scu-out 'DONE-WITH-SUBGOAL)
				 (format t "Done with subgoal!~%")
				 )
			     (progn
			       (scu-out 'SUBGOAL-NOT-FINISHED)
			       (format t "Subgoal not finished~%")))))
			 (HELP
			  (let ((name (if (cadr r) (if (symbolp (cadr r)) (cadr r) (intern (cadr r))) nil)))
			    (if name
				(print-help-name name)
			      (print-scip-help))))
			 (XMCASES
			  (when (and (pf-p tp)
				     (std-declared-p '|not| '|xmcases|))
			    (format t "Proposition>")
			    (multiple-value-bind
			     (p newtp)
			     (read-extract1-sock namedectx)
			     (if (and p (prop-p newtp))
				 (let* ((evar3 (intern-gensym))
					(evar4 (intern-gensym))
					(case1 (app-n-1-to-0 (length namedectx) evar3))
					(case2 (app-n-1-to-0 (length namedectx) evar4))
					(ap
					 (app-n '|xmcases| (list p (pf-prop tp) case1 case2)))
					(ftp3 (dpi (pf p) (dbshift-type-n 1 tp)))
					(ftp4 (dpi (pf (app '|not| p)) (dbshift-type-n 1 tp))))
				   (setf (get evar3 'evar) t)
				   (setf (get evar3 'dbtype)
					 (dpi-ctx ctx ftp3))
				   (setf (get evar4 'evar) t)
				   (setf (get evar4 'dbtype)
					 (dpi-ctx ctx ftp4))
				   (dotimes (i (length ctx))
				     (setq ap (lam ap)))
				   (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				   (setq *scip-theta* (compose-theta-1 evar ap *scip-theta*))
				   (setq *scip-tasks*
					 (cons
					  (list evar3 ctx names ftp3
						namedectx namesubst)
					  (cons
					   (list evar4 ctx names ftp4
						 namedectx namesubst)
					   (cdr *scip-tasks*)))))
			       (format t "That was not a prop.~%")))))
			 (CASES
			  (when (and (pf-p tp)
				     (std-declared-p '|or| '|orE|))
			    (let ((or-in-ctx nil))
			      (do ((ctx9 ctx (cdr ctx9))
				   (k 0 (1+ k)))
				  ((or or-in-ctx (null ctx9)))
				  (when (and (pf-p (car ctx9))
					     (eq (term-extr-head (pf-prop (car ctx9))) '|or|))
				    (setq or-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
			      (if or-in-ctx
				  (let* ((k (car or-in-ctx))
					 (disjtp (cdr or-in-ctx))
					 (disj (pf-prop disjtp))
					 (disjl (app-arg (app-func disj)))
					 (disjr (app-arg disj))
					 (evar3 (intern-gensym))
					 (evar4 (intern-gensym))
					 (evtrm3 (app-n-1-to-0 (length namedectx) evar3))
					 (evtrm4 (app-n-1-to-0 (length namedectx) evar4))
					 (ap (app
					      (app
					       (app
						(app
						 (app
						  (app '|orE| disjl) disjr)
						 k)
						(pf-prop tp))
					       evtrm3)
					      evtrm4))
					 (ftp3 (dpi (pf disjl) (dbshift-type-n 1 tp)))
					 (ftp4 (dpi (pf disjr) (dbshift-type-n 1 tp))))
				    (setf (get evar3 'evar) t)
				    (setf (get evar3 'dbtype)
					  (dpi-ctx ctx ftp3))
				    (setf (get evar4 'evar) t)
				    (setf (get evar4 'dbtype)
					  (dpi-ctx ctx ftp4))
				    (dotimes (i (length ctx))
				      (setq ap (lam ap)))
				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				    (setq *scip-theta* (compose-theta-1 evar ap *scip-theta*))
				    (setq *scip-tasks*
					  (cons
					   (list evar3 ctx names ftp3
						 namedectx namesubst)
					   (cons
					    (list evar4 ctx names ftp4
						  namedectx namesubst)
					    (cdr *scip-tasks*)))))
				(format t "Cannot apply cases.  No disjunction in context.~%")))))
			 (ADJCASES
			  (when (and (pf-p tp)
				     (std-declared-p '|in| '|eq| '|setadjoin| '|setadjoinE|))
			    (let ((or-in-ctx nil))
			      (do ((ctx9 ctx (cdr ctx9))
				   (k 0 (1+ k)))
				  ((or or-in-ctx (null ctx9)))
				  (when (and (pf-p (car ctx9))
					     (app-p (pf-prop (car ctx9)))
					     (app-p (app-func (pf-prop (car ctx9))))
					     (eq (app-func (app-func (pf-prop (car ctx9)))) '|in|)
					     (app-p (app-arg (app-func (pf-prop (car ctx9)))))
					     (app-p (app-func (app-arg (app-func (pf-prop (car ctx9))))))
					     (eq (app-func (app-func (app-arg (app-func (pf-prop (car ctx9))))))
						 '|setadjoin|))
				    (setq or-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
			      (if or-in-ctx
				  (let* ((k (car or-in-ctx))
					 (disjtp (cdr or-in-ctx))
					 (insa (pf-prop disjtp))
					 (elt (app-arg insa))
					 (sa (app-arg (app-func insa)))
					 (set1 (app-arg (app-func sa)))
					 (set2 (app-arg sa))
					 (evar3 (intern-gensym))
					 (evar4 (intern-gensym))
					 (evtrm3 (app-n-1-to-0 (length namedectx) evar3))
					 (evtrm4 (app-n-1-to-0 (length namedectx) evar4))
					 (ap (app
					      (app
					       (app
						(app
						 (app
						  (app
						   (app '|setadjoinE| set1) set2)
						  elt)
						 k)
						(pf-prop tp))
					       evtrm3)
					      evtrm4))
					 (ftp3 (dpi (pf (app-n '|eq| (list elt set1))) (dbshift-type-n 1 tp)))
					 (ftp4 (dpi (pf (app-n '|in| (list set2 elt))) (dbshift-type-n 1 tp))))
				    (setf (get evar3 'evar) t)
				    (setf (get evar3 'dbtype)
					  (dpi-ctx ctx ftp3))
				    (setf (get evar4 'evar) t)
				    (setf (get evar4 'dbtype)
					  (dpi-ctx ctx ftp4))
				    (dotimes (i (length ctx))
				      (setq ap (lam ap)))
				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				    (setq *scip-theta* (compose-theta-1 evar ap *scip-theta*))
				    (setq *scip-tasks*
					  (cons
					   (list evar3 ctx names ftp3
						 namedectx namesubst)
					   (cons
					    (list evar4 ctx names ftp4
						  namedectx namesubst)
					    (cdr *scip-tasks*))))
				    (format t "OK~%")
				    )
				(format t "Cannot apply setadjoin cases.  No (y::(x;A)) in context.~%")))))
			 (EXISTS
			  (when (and (pf-p tp)
				     (std-declared-p '|dex| '|dexE| '|in|))
			    (let ((name (if (symbolp (cadr r)) (cadr r) (intern (cadr r)))))
			      (if name
				  (let ((ex-in-ctx nil))
				    (do ((ctx9 ctx (cdr ctx9))
					 (k 0 (1+ k)))
					((or ex-in-ctx (null ctx9)))
					(when (and (pf-p (car ctx9))
						   (eq (term-extr-head (pf-prop (car ctx9))) '|dex|))
					  (setq ex-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
				    (if ex-in-ctx
					(let* ((k (car ex-in-ctx))
					       (pfex (cdr ex-in-ctx))
					       (ex (pf-prop pfex))
					       (bdset (app-arg (app-func ex)))
					       (phi (app-arg ex)))
					  (setq *k* k *pfex* pfex *ex* ex *bdset* bdset *phi* phi) ; delete me
					  (setf (get name 'bvar) t)
					  (setf (get name 'dbtype) (dclass (app '|in| (dbsubst bdset #'identity namesubst))))
					  (let* ((evar4 (intern-gensym))
						 (ctx4 (ctx-cons (dclass (app '|in| bdset)) ctx))
						 (namedectx4 (cons (list name (get name 'dbtype))
								   namedectx))
						 (namesubst4 (cons name (cons #'identity namesubst)))
						 (evtrm4 (app-n-1-to-0 (length namedectx4) evar4))
						 (ap (app
						      (app
						       (app
							(app
							 (app '|dexE| bdset)
							 phi)
							k)
						       (pf-prop tp))
						      (lam evtrm4)))
						 (ftp (dpi (pf (normalize (app (dbshift-n 1 phi) 0)))
							   (dbshift-type-n 2 tp))))
					    (setq *ap* ap) ; delete me
					    (setf (get evar4 'evar) t)
					    (setf (get evar4 'dbtype)
						  (dpi-ctx ctx4 ftp))
					    (dotimes (i (length ctx))
					      (setq ap (lam ap)))
					    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					    (setq *scip-theta* (compose-theta-1 evar ap *scip-theta*))
					    (setq *scip-tasks*
						  (cons
						   (list evar4 ctx4 (cons name names)
							 ftp
							 namedectx4 namesubst4)
						   (cdr *scip-tasks*)))
					    ))
				      (progn ; otherwise let user give info and make a claim
					(format t "Bounding Set>")
					(multiple-value-bind
					 (bdset newtp)
					 (read-extract1-sock namedectx)
					 (if (and bdset (or (obj-p newtp) (dclass-p newtp)))
					     (progn
					       (when (dclass-p newtp)
						 (setq bdset (fst bdset))
						 (setq newtp (obj)))
					       (let* ((namedbdtp (dclass (app '|in| (dbsubst bdset #'identity namesubst))))
						      (namedectx2 (cons (list name namedbdtp) namedectx))
						      (ctx2 (ctx-cons (dclass (app '|in| bdset)) ctx)))
						 (setf (get name 'bvar) t)
						 (setf (get name 'dbtype) namedbdtp)
						 (format t "Proposition>")
						 (multiple-value-bind
						  (phibody newtp2)
						  (read-extract1-sock namedectx2)
						  (if (and phibody (prop-p newtp2))
						      (if (nintrm-p 0 phibody)
							  (let* ((phi (lam phibody))
								 (ex (app (app '|dex| bdset) phi))
								 (pfex (pf ex)))
							    (multiple-value-bind
							     (tasks2 theta2)
							     (task-claim pfex task (cdr *scip-tasks*) *scip-theta*)
							     (let ((taskwexhyp (car tasks2))
								   (delayed (cdr tasks2)))
							       (multiple-value-bind
								(evar3 ctx3 names3 tp3 namedectx3 namesubst3)
								(task-components taskwexhyp)
								(let* ((evar4 (intern-gensym))
								       (bdset1 (dbshift-n 1 bdset))
								       (ctx4 (ctx-cons (dclass (app '|in| bdset1)) ctx3))
								       (namedectx4 (cons (list name (dclass (app '|in| bdset1))) namedectx3))
								       (namesubst4 (cons name (cons #'identity namesubst3)))
								       (evtrm4 (app-n-1-to-0 (length namedectx4) evar4))
								       (ap (app
									    (app
									     (app
									      (app
									       (app '|dexE| bdset1)
									       (dbshift-n 1 phi))
									      0) (dbshift-n 1 (pf-prop tp)))
									    (lam evtrm4)))
								       (ftp (dpi (pf (normalize (app (dbshift-n 2 phi) 0)))
										 (dbshift-type-n 3 tp))))
								  (setf (get evar4 'evar) t)
								  (setf (get evar4 'dbtype)
									(dpi-ctx ctx4 ftp))
								  (dotimes (i (length ctx3))
								    (setq ap (lam ap)))
								  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
								  (setq *scip-theta* (compose-theta-1 evar3 ap theta2))
								  (setq *scip-tasks*
									(cons
									 (list evar4 ctx4 (cons name names3)
									       ftp
									       namedectx4 namesubst4)
									 delayed))
								  )))))
							(format t "Proposition must depend on existence variable~%"))
						    (format t "Ill-formed proposition~%")))))
					   (format t "Ill-formed bounding set~%"))))))
				(format t "Problem with eigenvariable name.~%")))))
			 (SETUNIONEXISTS
			  (when (and (pf-p tp)
				     (std-declared-p '|setunion| '|setunionE| '|in|))
			    (let ((name (if (symbolp (cadr r)) (cadr r) (intern (cadr r)))))
			      (if name
				  (let ((ex-in-ctx nil))
				    (do ((ctx9 ctx (cdr ctx9))
					 (k 0 (1+ k)))
					((or ex-in-ctx (null ctx9)))
					(when (and (pf-p (car ctx9))
						   (app-p (pf-prop (car ctx9)))
						   (app-p (app-func (pf-prop (car ctx9))))
						   (eq (app-func (app-func (pf-prop (car ctx9)))) '|in|)
						   (app-p (app-arg (app-func (pf-prop (car ctx9)))))
						   (eq (app-func (app-arg (app-func (pf-prop (car ctx9)))))
						       '|setunion|))
					  (setq ex-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
				    (if ex-in-ctx
					(let* ((k (car ex-in-ctx))
					       (pfex (cdr ex-in-ctx))
					       (ex (pf-prop pfex))
					       (cset (app-arg (app-arg (app-func ex))))
					       (elt (app-arg ex)))
					  (let* ((evar4 (intern-gensym))
						 (a1 (pf (app (app '|in| (dbshift-n 2 cset)) 1)))
						 (a2 (pf (app (app '|in| 0) (dbshift-n 1 elt))))
						 (ctx4 (ctx-cons (obj) ctx))
						 (namedectx4
						  (cons (list name (obj))
							namedectx))
						 (namesubst4 (cons name (cons #'identity namesubst)))
						 (evtrm4 (app-n-1-to-0 (length namedectx4) evar4))
						 (ap (app
						      (app
						       (app
							(app
							 (app '|setunionE| cset)
							 elt)
							k)
						       (pf-prop tp))
						      (lam evtrm4)))
						 (ftp (dpi a2 (dpi a1
								   (dbshift-type-n 3 tp)))))
					    (setq *ap* ap) ; delete me
					    (setf (get name 'bvar) t)
					    (setf (get name 'dbtype) (obj))
					    (setf (get evar4 'evar) t)
					    (setf (get evar4 'dbtype)
						  (dpi-ctx ctx4 ftp))
					    (dotimes (i (length ctx))
					      (setq ap (lam ap)))
					    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					    (setq *scip-theta* (compose-theta-1 evar ap *scip-theta*))
					    (setq *scip-tasks*
						  (cons
						   (list evar4 ctx4 (cons name names)
							 ftp
							 namedectx4 namesubst4)
						   (cdr *scip-tasks*)))
					    ))
				      nil))))))
			 (ELIM
			  (multiple-value-bind
			   (succ1 tasklist1 theta1)
			   (task-close-under-simple-elims task (cdr *scip-tasks*) *scip-theta*)
			   (if succ1
			       (progn
				 (scu-out 'OK)
				 (format t "OK.~%")
				 (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				 (setq *scip-tasks* tasklist1)
				 (setq *scip-theta* theta1))
			     (progn
			       (scu-out 'NO-SIMPLE-ELIMS)
			       (format t "No simple elimination steps possible.~%")))))
					;		    ((and (> (length cmd) 7) (string-equal cmd "unfold " :start1 0 :end1 7))
					;		     (let ((name (intern (subseq cmd 7))))
					;		       (if (abbrevname-p name)
					;			   ()
					;			 ?)))
					;		    ((string-equal cmd "fold")
					;		     (when (pf-p tp)
					;		       (let* ((prop (pf-prop tp))
					;			      (h (term-app-head prop)))
					;			 (if (and (symbolp h) (abbrevname-p h))
					;			     (multiple-value-bind
					;			      (succ1 tasklist1 theta1)
					;			      (task-fold-defns (pf (delta-head-reduce prop)) task (cdr *scip-tasks*) *scip-theta*)
					;			      (if succ1
					;				  (progn
					; 				    (format t "Correct.~%")
					; 				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					; 				    (setq *scip-tasks* tasklist1)
					; 				    (setq *scip-theta* theta1))
					;				(format t "Could not justify fold of defn.~%")))
					;			   
					;			   (format t "Could not parse proposition.~%"))))
					;
					;			   
					;			   ?))))
			 (B
			  (let ((back1 (quick-fill-gap ctx tp *scip-usable* nil 1)))
			    (if back1
				(let ((z (find-if-not #'(lambda (x)
							  (cadr x))
						      back1)))
				  (if z
				      (let ((tmp (car z)))
					(setq *scip-theta* (compose-theta-1 evar tmp *scip-theta*))
					(format t "Done with subgoal!~%")
					(pop *scip-tasks*)
					)
				    (let ((i -1))
				      (setq back1 (simplify-subgoal-list back1))
				      (dolist (z back1)
					(format t "~d) " (incf i))
					(let ((tmp (car z)))
					  (dotimes (j (length ctx))
					    (setq tmp (gen-lam-body tmp)))
					  (scu-out (list i ctx tmp names (cadr z)))
					  (format t "~d~%Reduce to~%"
						  (output1-normal-string tmp names))
					  (dolist (sgs (cadr z))
					    (setq tmp (cdr sgs))
					    (dotimes (j (length ctx))
					      (when (dpi-p tmp)
						(setq tmp (dpi-cod tmp))))
					    (format t "~d~%" (output1-type-string tmp names)))))
				      (format t "Enter a number between 0 and ~d~%" i)
				      (let ((z (progn (scu-out (list 'PROMPT-NUM i)) (read *scunak-socket* nil nil))))
					(if (and (numberp z) (nth z back1))
					    (let ((y (nth z back1)))
					      (let ((tmp (car y)))
						(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					;					     (format t "theta = ~S~%" *scip-theta*) ; delete me
						(setq *scip-theta* (compose-theta-1 evar tmp *scip-theta*))
					;					     (format t "evar = ~S~%tmp = ~S~%" evar tmp) ; delete me
					;					     (format t "theta = ~S~%" *scip-theta*) ; delete me
						(setq *scip-tasks* (append
								    (mapcar #'(lambda (new)
										(let ((dtp (cdr new)))
										  (setf (get (car new) 'dbtype) (cdr new)) ; global type, so OK
										  (dotimes (j (length ctx))
										    (when (dpi-p dtp)
										      (setq dtp (dpi-cod dtp))))
										  (list (car new) ctx names dtp
											namedectx namesubst
											)))
									    (cadr y))
								    (cdr *scip-tasks*)))))
					  (progn
					    (scu-out 'TASK-UNCHANGED-BAD-CHOICE)
					    (format t "Task Unchanged: ~d is not a number between 0 and ~d~%" z i)))))))
			      (progn
				(scu-out 'NO-OPTIONS)
				(format t "No backward options with 1 gap~%")))))
			 (B2
			  (let ((back1 (quick-fill-gap ctx tp *scip-usable* nil 2)))
			    (if back1
				(let ((z (find-if-not #'(lambda (x)
							  (cadr x))
						      back1)))
				  (if z
				      (let ((tmp (car z)))
					(setq *scip-theta* (compose-theta-1 evar tmp *scip-theta*))
					(format t "Done with subgoal!~%")
					(pop *scip-tasks*)
					)
				    (let ((i -1))
				      (setq back1 (simplify-subgoal-list back1))
				      (dolist (z back1)
					(format t "~d) " (incf i))
					(let ((tmp (car z)))
					  (dotimes (j (length ctx))
					    (setq tmp (gen-lam-body tmp)))
					  (scu-out (list i ctx tmp names (cadr z)))
					  (format t "~d~%Reduce to~%"
						  (output1-normal-string tmp names))
					  (dolist (sgs (cadr z))
					    (setq tmp (cdr sgs))
					    (dotimes (j (length ctx))
					      (when (dpi-p tmp)
						(setq tmp (dpi-cod tmp))))
					    (format t "~d~%" (output1-type-string tmp names)))))
				      (format t "Enter a number between 0 and ~d~%" i)
				      (let ((z (progn (scu-out (list 'PROMPT-NUM i)) (read *scunak-socket* nil nil))))
					(if (and (numberp z) (nth z back1))
					    (let ((y (nth z back1)))
					      (let ((tmp (car y)))
						(push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					;					     (format t "theta = ~S~%" *scip-theta*) ; delete me
						(setq *scip-theta* (compose-theta-1 evar tmp *scip-theta*))
					;					     (format t "evar = ~S~%tmp = ~S~%" evar tmp) ; delete me
					;					     (format t "theta = ~S~%" *scip-theta*) ; delete me
						(setq *scip-tasks* (append
								    (mapcar #'(lambda (new)
										(let ((dtp (cdr new)))
										  (setf (get (car new) 'dbtype) (cdr new)) ; global type, so OK
										  (dotimes (j (length ctx))
										    (when (dpi-p dtp)
										      (setq dtp (dpi-cod dtp))))
										  (list (car new) ctx names dtp
											namedectx namesubst
											)))
									    (cadr y))
								    (cdr *scip-tasks*)))))
					  (progn
					    (scu-out 'TASK-UNCHANGED-BAD-CHOICE)
					    (format t "Task Unchanged: ~d is not a number between 0 and ~d~%" z i)))))))
			      (progn
				(scu-out 'NO-OPTIONS)
				(format t "No backward options with 2 gaps~%")))))
			 (F
			  (let ((fw 
				 (simplify-term-type-pairs
				  (remove-if-not
				   #'(lambda (x)
				       (pf-p (cdr x)))
				   (mapcar #'(lambda (y)
					       (cons y (ctx-extract-type ctx y)))
					   (quick-ctx-forward *scip-usable* ctx 1))))))
			    (if fw
				(let ((i -1))
				  (dolist (z fw)
				    (format t "~d) ~d~%~d~%" (incf i)
					    (output1-normal-string (car z) names)
					    (output1-type-string (cdr z) names))
				    (scu-out (list i (car z) (cdr z) names)))
				  (format t "Enter a number between 0 and ~d~%" i)
				  (let ((z (progn (scu-out (list 'PROMPT-NUM i)) (read *scunak-socket* nil nil))))
				    (if (and (numberp z) (nth z fw))
					(let* ((y (nth z fw))
					       (name (format nil "fact~d" (incf *scip-factnum*)))
					       (namez (intern name))
					       (ctx2 (ctx-cons (cdr y) ctx))
					       (newevar (intern-gensym))
					       (tp2 (dbshift-type-n 1 tp))
					       (newevartp (dpi-ctx ctx2 tp2)))
					  (setf (get namez 'bvar) t)
					  (setf (get namez 'dbtype) (dbsubst-type (cdr y) #'identity namesubst))
					  (setf (get newevar 'evar) t)
					  (setf (get newevar 'dbtype) newevartp) ; global
					  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					  (pop *scip-tasks*)
					  (setq *scip-theta* (compose-theta-1 evar (term-for-extending-ctx ctx newevar (normalize (car y))) *scip-theta*))
					  (push (list newevar ctx2 (cons name names) tp2
						      (cons (list namez (get namez 'dbtype)) namedectx)
						      (cons namez (cons #'identity namesubst))
						      )
						*scip-tasks*))
				      (progn
					(scu-out 'TASK-UNCHANGED-BAD-CHOICE)
					(format t "Task Unchanged: ~d is not a number between 0 and ~d~%" z i)))))
			      (progn
				(scu-out 'NO-OPTIONS)
				(format t "No forward options~%")))))
			 (F2
			  (let ((fw 
				 (simplify-term-type-pairs
				  (remove-if-not
				   #'(lambda (x)
				       (pf-p (cdr x)))
				   (mapcar #'(lambda (y)
					       (cons y (ctx-extract-type ctx y)))
					   (quick-ctx-forward *scip-usable* ctx 2))))))
			    (if fw
				(let ((i -1))
				  (dolist (z fw)
				    (format t "~d) ~d~%~d~%" (incf i)
					    (output1-normal-string (car z) names)
					    (output1-type-string (cdr z) names))
				    (scu-out (list i (car z) (cdr z) names)))
				  (format t "Enter a number between 0 and ~d~%" i)
				  (let ((z (progn (scu-out (list 'PROMPT-NUM i)) (read *scunak-socket* nil nil))))
				    (if (and (numberp z) (nth z fw))
					(let* ((y (nth z fw))
					       (name (format nil "fact~d" (incf *scip-factnum*)))
					       (namez (intern name))
					       (ctx2 (ctx-cons (cdr y) ctx))
					       (newevar (intern-gensym))
					       (tp2 (dbshift-type-n 1 tp))
					       (newevartp (dpi-ctx ctx2 tp2)))
					  (setf (get namez 'bvar) t)
					  (setf (get namez 'dbtype) (dbsubst-type (cdr y) #'identity namesubst))
					  (setf (get newevar 'evar) t)
					  (setf (get newevar 'dbtype) newevartp) ; global
					  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					  (pop *scip-tasks*)
					  (setq *scip-theta* (compose-theta-1 evar (term-for-extending-ctx ctx newevar (normalize (car y))) *scip-theta*))
					  (push (list newevar ctx2 (cons name names) tp2
						      (cons (list namez (get namez 'dbtype)) namedectx)
						      (cons namez (cons #'identity namesubst))
						      )
						*scip-tasks*))
				      (progn
					(scu-out 'TASK-UNCHANGED-BAD-CHOICE)
					(format t "Task Unchanged: ~d is not a number between 0 and ~d~%" z i)))))
			      (progn
				(scu-out 'NO-OPTIONS)
				(format t "No forward(2) options~%")))))
			 (TYPEOF ; just like the main one
			  (let ((pre-ex (input1l-preextr (cadr r))))
			    (multiple-value-bind
			     (e newtp info fail)
			     (extr-fill-in-blanks-1 pre-ex *input1-state* (input1-blanks-prefix *input1-ctx-info*))
			     (if (or info fail)
				 (progn
				   (when *scunak-socket*
				     (scu-out 'ILL-TYPED))
				   (format t "Could not determine a well-typed extraction term from input.~%")
				   (when fail
				     (format t "~d~%" fail))
				   (dolist (z info)
				     (when (eq (car z) 'EVAR) 
				       (let ((trm (nth 4 z))
					     (dtp (nth 5 z))
					     (etp (nth 6 z)))
					 (if (and trm dtp etp)
					     (progn
					       (when *scunak-socket*
						 (scu-out (list 'TYPE-PROBLEM trm etp dtp)))
					       (format t "Term: ~d~%Has Type: ~d~%Expected Type: ~d~%"
						       (output1-extraction-string trm nil t)
						       (output1-type-string etp nil t)
						       (output1-type-string dtp nil t)))
					   (when (nth 3 z)
					     (format t "~d" (nth 3 z))))))))
			       (if e
				   (progn
				     (when *scunak-socket*
				       (scu-out (list 'TYPE newtp)))
				     (format t "Type: ~d~%" (output1-type-string newtp (mapcar #'car *input1-ctx-info*))))
				 (progn
				   (when *scunak-socket*
				     (scu-out 'ILL-TYPED))
				   (format t "Could not determine an extraction term from input.~%")))))))
			 (MLS
			  (let ((prop (dbsubst (pf-prop tp) #'identity namesubst)))
			    (if (prop-comp-set-fragment-p prop)
				(let ((br (mls*-tableau (remove-if #'null
								   (mapcar #'(lambda (x)
									       (if (and (pf-p (cadr x))
											(prop-comp-set-fragment-p (pf-prop (cadr x))))
										   (pf-prop (cadr x))
										 nil))
									   *sci-namedectx*))
							(list prop))))
				  (if br
				      (progn
					(format t "The mls set theory part of this is satisfiable.  Consider:~%")
					(scu-out 'MLS-SAT)
					(dolist (p (car br))
					  (format t "~d~%" (output1-extraction-string p nil nil)))
					)
				    (progn
				      (scu-out 'MLS-SUCCESS)
				      (format t "The gap can be filled by mls set theory reasoning...~%"))))
			      (progn
				(scu-out 'NOT-MLS-PROP)
				(format t "The current goal is not an mls proposition.~%")))))
			 (APPLY
			  (multiple-value-bind
			   (e newtp)
			   (input1l-extr-n (cadr r) namedectx)
			   (if e
			       (if (dtype-returns-pf-p newtp)
				   (if (deptype1-p newtp ctx)
				       (progn
					 (scu-out 'OK)
					 (scip-add-fact e newtp))
				     (progn
				       (scu-out 'TASK-UNCHANGED-SECOND-ORDER-APPLY)
				       (format t "Task Unchanged: ~d is of type~%~d~%which is 2nd order~%"
					       (output1-extraction-string e names t)
					       (output1-type-string newtp names t)
					       )))
				 (progn
				   (scu-out 'TASK-UNCHANGED-NOT-PF-TYPE)
				   (format t "Task Unchanged: ~d is of type~%~d~%which is not a pf type~%"
					   (output1-extraction-string e names t)
					   (output1-type-string newtp names t)
					   )))
			     (progn
			       (scu-out 'NOT-EXTR-TERM)
			       (format t "Could not determine an extraction term from input.~%")))))
			 (WILLSHOW
			  (let* ((e (input1l-prop-n (cadr r) namedectx)))
			    (if e
				(let ((newtp (pf e)))
				  (multiple-value-bind
				   (succ1 tasklist1 theta1)
				   (task-willshow newtp task (cdr *scip-tasks*) *scip-theta*)
				   (if succ1
				       (progn
					 (scu-out 'CORRECT)
					 (format t "Correct.~%")
					 (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					 (setq *scip-tasks* tasklist1)
					 (setq *scip-theta* theta1))
				     (progn
				       (scu-out 'COULD-NOT-JUSTIFY)
				       (format t "Could not justify goal from given subgoal.~%")))))
			      (progn
				(scu-out 'NOT-PROP)
				(format t "Could not parse proposition.~%")))))
			 (HENCE
			  (let* ((e (input1l-prop-n (cadr r) namedectx)))
			    (if e
				(let ((newtp (pf e)))
				  (multiple-value-bind
				   (succ1 tasklist1 theta1)
				   (task-hence newtp task (cdr *scip-tasks*) *scip-theta*)
				   (if succ1
				       (progn
					 (scu-out 'CORRECT)
					 (format t "Correct.~%")
					 (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					 (setq *scip-tasks* tasklist1)
					 (setq *scip-theta* theta1))
				     (progn
				       (scu-out 'COULD-NOT-JUSTIFY)
				       (format t "Could not justify hence.~%")))))
			      (progn
				(scu-out 'NOT-PROP)
				(format t "Could not parse proposition.~%")))))
			 ((FACT CLEARLY)
			  (let* ((e (input1l-prop-n (cadr r) namedectx)))
			    (if e
				(let ((newtp (pf e)))
				  (multiple-value-bind
				   (succ1 tasklist1 theta1)
				   (task-fact newtp task (cdr *scip-tasks*) *scip-theta*)
				   (if succ1
				       (progn
					 (scu-out 'CORRECT)
					 (format t "Correct.~%")
					 (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					 (setq *scip-tasks* tasklist1)
					 (setq *scip-theta* theta1))
				     (progn
				       (scu-out 'COULD-NOT-JUSTIFY)
				       (format t "Could not justify fact.~%")))))
			      (progn
				(scu-out 'NOT-PROP)
				(format t "Could not parse proposition.~%")))))
			 (LEMMA
			  (let ((ctxi (input1-ctx-info-from-named-ectx namedectx))
				(name (if (symbolp (cadr r)) (cadr r) (if (stringp (cadr r)) (intern (cadr r)) nil)))
				(expldeps (mapcar #'(lambda (x)
						      (if (symbolp x)
							  x
							(if (stringp x)
							    (intern x)
							  nil)))
						  (caddr r)))
				(dtp (input1l-dtype (cadddr r))))
			    (if (and name (not (member nil expldeps)) dtp)
				(multiple-value-bind
				 (argctx failinfo)
				 (varlist-to-ctx expldeps ctxi)
				 (if failinfo
				     (progn
				       (format t "~d~%" failinfo)
				       (force-output *standard-output*)
				       (scu-out (list 'BAD-LEMMA-CTX failinfo)))
				   (progn
				     (if (dtype-returns-pf-p dtp)
					 (let ((mctx (build-minimal-ctx (dtype-free-bvars dtp)
									ctxi)))
					   (if (subctx mctx argctx)
					       (let ((fdtp (prefix-dpi-db argctx dtp))
						     (now *timestamp*))
						 (setq *timestamp* (- *scip-timestamp* 1.5)) ; time travel
						 (newclaim name (normalize-type fdtp) nil)
						 (setq *timestamp* now)
						 (push name *scip-lemmas*)
						 (when (deptype1-p dtp)
						   (scip-add-fact
						    (app-n name
							   (mapcar #'(lambda (x)
								       (named-term-to-db namedectx x))
								   expldeps))
						    (named-type-to-db namedectx
								      dtp))))
					     (progn
					       (format t "Hidden Dependency for new lemma ~d~%" name)
					       (force-output *standard-output*)
					       (scu-out (list 'HIDDEN-DEPENDENCY)))))
				       (progn
					 (format t "Lemma does not return pf type.~%")
					 (force-output *standard-output*)
					 (scu-out (list 'LEMMA-NOT-PF-TYPE))
					 )))))
			      (progn
				(format t "LEMMA arguments not understood~%")
				(force-output *standard-output*)
				(scu-out (list 'LEMMA-ARGS-NOT-UNDERSTOOD))
				))))
			 (CLAIMTYPE
			  (let* ((e (input1l-dtype-n (cadr r) namedectx)))
			    (if e
				(if (dtype-returns-pf-p e)
				    (progn
				      (scu-out 'OK)
				      (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				      (pop *scip-tasks*)
				      (multiple-value-setq
				       (*scip-tasks* *scip-theta*)
				       (task-claim e task *scip-tasks* *scip-theta*))
				      )
				  (progn
				    (scu-out 'NOT-PF-TYPE)
				    (format t "claimtype does not return pf type.~%")))
			      (progn
				(scu-out 'NOT-TYPE)
				(format t "Could not parse dtype1.~%")))))
			 (CLAIM ; splits proof in two - island step
			  (let* ((e (input1l-prop-n (cadr r) namedectx)))
			    (if e
				(progn
				  (scu-out 'OK)
				  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				  (pop *scip-tasks*)
				  (multiple-value-setq
				   (*scip-tasks* *scip-theta*)
				   (task-claim (pf e) task *scip-tasks* *scip-theta*))
				  )
			      (progn
				(scu-out 'NOT-PROP)
				(format t "Could not parse proposition.~%")))))
 					; specialized rules
			 (CONTRADICTION
			  (when (std-declared-p '|false| '|not| '|notI| '|contradiction|)
			    (let ((C (pf-prop tp))
				  (pffalse (pf '|false|)))
			      (if (eq C '|false|)
				  (format t "You are already proving false, task unchanged.~%")
				(if (and (app-p C)
					 (eq (app-func C) '|not|))
				    (let* ((D (app-arg C))
					   (pffalse (pf '|false|))
					   (newevar (intern-gensym))
					   (trm1 (app-n-1-to-0 (length ctx) newevar))
					   (trm (app (app '|notI| D) trm1))
					   (tp2 (dpi (pf D) pffalse)))
				      (setf (get newevar 'evar) t)
				      (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				      (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				      (dotimes (n (length ctx)) (setq trm (lam trm)))
				      (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				      (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							       (cdr *scip-tasks*)))
				      (scu-out 'OK)
				      (format t "OK~%")
				      )
				  (let* ((newevar (intern-gensym))
					 (trm1 (app-n-1-to-0 (length ctx) newevar))
					 (trm (app (app '|contradiction| C) trm1))
					 (tp2 (dpi (pf (app '|not| C)) pffalse)))
				    (setf (get newevar 'evar) t)
				    (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				    (dotimes (n (length ctx)) (setq trm (lam trm)))
				    (scu-out 'OK)
				    (format t "OK~%")
				    (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				    (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							     (cdr *scip-tasks*)))))))))
			 (INTRO
			  (let ((C (pf-prop tp)))
			    (cond ((and (app-p C) (eq (app-func C) '|not|)
					(std-declared-p '|not| '|false| '|notI|))
				   (let* ((D (app-arg C))
					  (pffalse (pf '|false|))
					  (newevar (intern-gensym))
					  (trm1 (app-n-1-to-0 (length ctx) newevar))
					  (trm (app (app '|notI| D) trm1))
					  (tp2 (dpi (pf D) pffalse)))
				     (setf (get newevar 'evar) t)
				     (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				     (dotimes (n (length ctx)) (setq trm (lam trm)))
				     (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				     (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							      (cdr *scip-tasks*)))
				     (scu-out 'OK)
				     (format t "OK~%")
				     ))
				  ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|imp|)
					(std-declared-p '|imp| '|impI|))
				   (let* ((A (app-arg (app-func C)))
					  (B (app-arg C))
					  (newevar (intern-gensym))
					  (trm1 (app-n-1-to-0 (length ctx) newevar))
					  (trm (app (app (app '|impI| A) B) trm1))
					  (tp2 (dpi (pf A) (pf (dbshift-n 1 B)))))
				     (setf (get newevar 'evar) t)
				     (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				     (dotimes (n (length ctx)) (setq trm (lam trm)))
				     (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				     (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							      (cdr *scip-tasks*)))
				     (scu-out 'OK)
				     (format t "OK~%")
				     ))
				  ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|dimp|)
					(std-declared-p '|dimp| '|dimpI|))
				   (let* ((A (app-arg (app-func C)))
					  (B (app-arg C))
					  (newevar (intern-gensym))
					  (trm1 (app-n-1-to-0 (length ctx) newevar))
					  (trm (app (app (app '|dimpI| A) B) trm1))
					  (tp2 (dpi (pf A) (pf (normalize (app (dbshift-n 1 B) 0))))))
				     (setf (get newevar 'evar) t)
				     (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				     (dotimes (n (length ctx)) (setq trm (lam trm)))
				     (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				     (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							      (cdr *scip-tasks*)))
				     (scu-out 'OK)
				     (format t "OK~%")
				     ))
				  ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|dall|)
					(std-declared-p '|dall| '|dallI| '|in|))
				   (let* ((A (app-arg (app-func C)))
					  (B (app-arg C))
					  (newevar (intern-gensym))
					  (trm1 (app-n-1-to-0 (length ctx) newevar))
					  (trm (app (app (app '|dallI| A) B) trm1))
					  (tp2 (dpi (dclass (app '|in| A)) (pf (normalize (app (dbshift-n 1 B) 0))))))
				     (setf (get newevar 'evar) t)
				     (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				     (dotimes (n (length ctx)) (setq trm (lam trm)))
				     (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				     (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							      (cdr *scip-tasks*)))
				     (scu-out 'OK)
				     (format t "OK~%")
				     ))
				  ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|and|)
					(std-declared-p '|and| '|andI|))
				   (let* ((A (app-arg (app-func C)))
					  (B (app-arg C))
					  (newevar1 (intern-gensym))
					  (newevar2 (intern-gensym))
					  (trm1 (app-n-1-to-0 (length ctx) newevar1))
					  (trm2 (app-n-1-to-0 (length ctx) newevar2))
					  (trm (app (app (app (app '|andI| A) B) trm1) trm2))
					  (tp1 (pf A))
					  (tp2 (pf B))
					  )
				     (setf (get newevar1 'evar) t)
				     (setf (get newevar1 'dbtype) (dpi-ctx ctx tp1))
				     (setf (get newevar2 'evar) t)
				     (setf (get newevar2 'dbtype) (dpi-ctx ctx tp2))
				     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				     (dotimes (n (length ctx)) (setq trm (lam trm)))
				     (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				     (setq *scip-tasks* (cons (list newevar1 ctx names tp1 namedectx namesubst)
							      (cons (list newevar2 ctx names tp2 namedectx namesubst)
								    (cdr *scip-tasks*))))
				     (scu-out 'OK)
				     (format t "OK~%")
				     ))
				  ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|dand|)
					(std-declared-p '|dand| '|dandI|))
				   (let* ((A (app-arg (app-func C)))
					  (B (app-arg C))
					  (newevar1 (intern-gensym))
					  (newevar2 (intern-gensym))
					  (trm1 (app-n-1-to-0 (length ctx) newevar1))
					  (trm2 (app-n-1-to-0 (length ctx) newevar2))
					  (trm (app (app (app (app '|dandI| A) B) trm1) (app trm2 trm1)))
					  (tp1 (pf A))
					  (tp2 (dpi (pf A) (pf (normalize (app (dbshift-n 1 B) 0)))))
					  )
				     (setf (get newevar1 'evar) t)
				     (setf (get newevar1 'dbtype) (dpi-ctx ctx tp1))
				     (setf (get newevar2 'evar) t)
				     (setf (get newevar2 'dbtype) (dpi-ctx ctx tp2))
				     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				     (dotimes (n (length ctx)) (setq trm (lam trm)))
				     (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				     (setq *scip-tasks* (cons (list newevar1 ctx names tp1 namedectx namesubst)
							      (cons (list newevar2 ctx names tp2 namedectx namesubst)
								    (cdr *scip-tasks*))))
				     (scu-out 'OK)
				     (format t "OK~%")
				     ))
				  ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|subset|)
					(std-declared-p '|subset| '|subsetI1| '|in|))
				   (let* ((A (app-arg (app-func C)))
					  (B (app-arg C))
					  (newevar (intern-gensym))
					  (trm1 (app-n-1-to-0 (length ctx) newevar))
					  (trm (app (app (app '|subsetI1| A) B) trm1))
					  (tp2 (dpi (dclass (app '|in| A)) (pf (app (app '|in| (dbshift-n 1 B)) (fst 0))))))
				     (setf (get newevar 'evar) t)
				     (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
				     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
				     (dotimes (n (length ctx)) (setq trm (lam trm)))
				     (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
				     (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
							      (cdr *scip-tasks*)))
				     (scu-out 'OK)
				     (format t "OK~%")
				     ))
				  ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|eq|))
				   (let* ((A (app-arg (app-func C)))
					  (B (app-arg C))
					  (A* (if (fst-p A) (fst-arg A)))
					  (B* (if (fst-p B) (fst-arg B)))
					  (A*tp (if (and A* B*) (ctx-extract-type ctx A*)))
					  (B*tp (if (and A* B*) (ctx-extract-type ctx B*))))
				     (if (and A*tp B*tp
					      (std-declared-p '|eq| '|in| '|funcSet| '|funcext2| '|ap2|)
					      (dclass-p A*tp)
					      (dclass-p B*tp)
					      (app-p (dclass-pred A*tp))
					      (app-p (dclass-pred B*tp))
					      (eq (app-func (dclass-pred A*tp)) '|in|)
					      (eq (app-func (dclass-pred B*tp)) '|in|)
					      (app-p (app-arg (dclass-pred A*tp)))
					      (app-p (app-arg (dclass-pred B*tp)))
					      (app-p (app-func (app-arg (dclass-pred A*tp))))
					      (app-p (app-func (app-arg (dclass-pred B*tp))))
					      (eq (app-func (app-func (app-arg (dclass-pred A*tp)))) '|funcSet|)
					      (eq (app-func (app-func (app-arg (dclass-pred B*tp)))) '|funcSet|))
					 (let ((domset (app-arg (app-func (app-arg (dclass-pred A*tp)))))
					       (codset (app-arg (app-arg (dclass-pred A*tp)))))
					   (if (and (ctx-terms-eq-type ctx
								       domset
								       (app-arg (app-func (app-arg (dclass-pred B*tp))))
								       (obj))
						    (ctx-terms-eq-type ctx
								       codset
								       (app-arg (app-arg (dclass-pred B*tp)))
								       (obj)))
					       (let* ((newevar (intern-gensym))
						      (trm1 (app-n-1-to-0 (length ctx) newevar))
						      (trm (app-n '|funcext2|
								  (list domset codset A* B* trm1)))
						      (tp2 (dpi (dclass (app '|in| domset)) (pf (app-n '|eq|
												       (list (fst (app-n '|ap2|
															 (list
															  (dbshift-n 1 domset)
															  (dbshift-n 1 codset)
															  (dbshift-n 1 A*)
															  0)))
													     (fst (app-n '|ap2|
															 (list
															  (dbshift-n 1 domset)
															  (dbshift-n 1 codset)
															  (dbshift-n 1 B*)
															  0)))))))))
						 (setf (get newevar 'evar) t)
						 (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
						 (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
						 (dotimes (n (length ctx)) (setq trm (lam trm)))
						 (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
						 (setq *scip-tasks* (cons (list newevar ctx names tp2 namedectx namesubst)
									  (cdr *scip-tasks*)))
						 (scu-out 'OK)
						 (format t "OK~%")
						 )
					     (progn
					       (scu-out 'NO-INTRO)
					       (format t "intro not applicable to this goal~%"))))
				       (if (std-declared-p '|eq| '|subset| '|setextsub|)
					   (let* ((newevar1 (intern-gensym))
						  (newevar2 (intern-gensym))
						  (trm1 (app-n-1-to-0 (length ctx) newevar1))
						  (trm2 (app-n-1-to-0 (length ctx) newevar2))
						  (trm (app (app (app (app '|setextsub| A) B) trm1) trm2))
						  (tp1 (pf (app (app '|subset| A) B)))
						  (tp2 (pf (app (app '|subset| B) A)))
						  )
					     (setf (get newevar1 'evar) t)
					     (setf (get newevar1 'dbtype) (dpi-ctx ctx tp1))
					     (setf (get newevar2 'evar) t)
					     (setf (get newevar2 'dbtype) (dpi-ctx ctx tp2))
					     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					     (dotimes (n (length ctx)) (setq trm (lam trm)))
					     (setq *scip-theta* (compose-theta-1 evar trm *scip-theta*))
					     (setq *scip-tasks* (cons (list newevar1 ctx names tp1 namedectx namesubst)
								      (cons (list newevar2 ctx names tp2 namedectx namesubst)
									    (cdr *scip-tasks*))))
					     (scu-out 'OK)
					     (format t "OK~%")
					     )
					 (progn
					   (scu-out 'NO-INTRO)
					   (format t "intro not applicable to this goal~%"))))))
			     ((and (app-p C) (app-p (app-func C)) (eq (app-func (app-func C)) '|equiv|))
			      (let* ((C (pf-prop tp))
				     (name (term-extr-head C)))
				(if (abbrevname-p name)
				    (let* ((args (term-extr-args C))
					   (e1 (app-n (intern (format nil "~d#F" name)) args))
					   (e1tp (ctx-extract-type ctx e1)))
				      (if (and e1tp (dpi-p e1tp)
					       (pf-p (dpi-dom e1tp)))
					  (multiple-value-bind
					   (tasklist2 theta2)
					   (task-claim (dpi-dom e1tp) task (cdr *scip-tasks*) *scip-theta*)
					   (multiple-value-bind
					    (evar1 ctx1 names1 tp1 namedectx1 namesubst1)
					    (task-components (car tasklist2))
					    (let ((e (app (dbshift-n 1 e1) 0)))
					      (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					      (setq *scip-tasks* (cdr tasklist2))
					      (setq *scip-theta*
						    (compose-theta-1
						     evar1
						     (lam-ctx ctx1 e)
						     theta2))
					      (scu-out 'OK)
					      (format t "OK~%"))))
					(format t "Problem intro'ing abbrev at head of goal.~%There is no excuse for this failure.~%")))
				  (format t "Problem intro'ing abbrev at head of goal.~%There is no excuse for this failure.~%"))))
				  (t
				   (scu-out 'NO-INTRO)
				   (format t "You are not proving something to intro, task unchanged.~%")))))
			 (UNFOLDGOAL
			  (when (and *auto-gen-congruence* (> *congruences-stage* 1))
			    (let ((name (if (symbolp (cadr r)) (cadr r) (intern (cadr r)))))
			      (if (get name 'abbrev)
				  (if (member name (sig-elts (pf-prop tp)))
				      (let ((d (delta-reduce-abbrevs ctx (pf-prop tp) (prop) (list name))))
					;				 (setq *ctx* ctx *d* d *tp* tp)
					(if (and d (not (heq d (pf-prop tp))))
					    (let ((pftrm (congruence-make-equation-pf
							  ctx d (pf-prop tp) (prop))))
					      (when (> *verbose* 30)
						(format t "After Unfolding:~%~d~2%" (output1-extraction-string d names t))
						(format t "Before Unfolding:~%~d~2%" (output1-extraction-string (pf-prop tp) names t))
						(setq *output1-skip-snd* t)
						(format t "After Unfolding:~%~d~2%" (output1-extraction-string d names t))
						(format t "Before Unfolding:~%~d~2%" (output1-extraction-string (pf-prop tp) names t))
						(setq *output1-skip-snd* nil))
					      (if pftrm
						  (multiple-value-bind
						   (tasklist2 theta2)
						   (task-claim (pf d) task (cdr *scip-tasks*) *scip-theta*)
						   (let ((task1 (car tasklist2)))
						     (scu-out 'OK)
						     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
						     (setq *scip-tasks* (cdr tasklist2))
						     (setq *scip-theta*
							   (compose-theta-1
							    (car task1)
							    (lam-ctx ctx
								     (app-n '|equivEimp1| (list d (pf-prop tp) pftrm)))
							    theta2))))
						(progn
						  (scu-out 'FAILED)
						  (format t "Problem automatically unfolding abbrev in goal (1).~%"))))
					  (progn
					    (scu-out 'FAILED)
					    (format t "Problem automatically unfolding abbrev in goal (2).~%"))))
				    (progn
				      (scu-out 'ABBREV-NOT-IN-GOAL)
				      (format t "~d does not occur in goal.~%")))
				(progn
				  (scu-out 'NOT-ABBREV)
				  (format t "~d is not an abbreviation.~%"))))))
			 (UNFOLD
			  (when (and *auto-gen-congruence* (> *congruences-stage* 1))
			    (let ((name (if (symbolp (cadr r)) (cadr r) (intern (cadr r)))))
			      (if (get name 'abbrev)
				  (let ((a-in-ctx nil))
				    (do ((ctx9 ctx (cdr ctx9))
					 (k 0 (1+ k)))
					((or a-in-ctx (null ctx9)))
					(when (and (pf-p (car ctx9))
						   (member name (sig-elts (pf-prop (car ctx9)))))
					  (setq a-in-ctx (cons k (dbshift-type-n (1+ k) (car ctx9))))))
				    (if a-in-ctx
					(let* ((oldprop (pf-prop (cdr a-in-ctx)))
					       (k (car a-in-ctx))
					       (d (delta-reduce-abbrevs ctx (pf-prop (cdr a-in-ctx)) (prop) (list name))))
					  (if (and d (not (heq d oldprop)))
					      (let ((pftrm (congruence-make-equation-pf
							    ctx d oldprop (prop))))
						(if pftrm
						    (multiple-value-bind
						     (tasklist2 theta2)
						     (task-claim (pf d) task (cdr *scip-tasks*) *scip-theta*)
						     (let ((task1 (cadr tasklist2)))
						       (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
						       (scu-out 'OK)
						       (setq *scip-tasks* (cons (car tasklist2) (cddr tasklist2)))
						       (setq *scip-theta*
							     (compose-theta-1
							      (car task1)
							      (lam-ctx ctx
								       (app-n '|equivEimp2| (list d oldprop pftrm k)))
							      theta2))))
						  (progn
						    (scu-out 'FAILED)
						    (format t "Problem automatically unfolding abbrev in support (1).~%"))))
					    (progn
					      (scu-out 'FAILED)
					      (format t "Problem automatically unfolding abbrev in support (2).~%"))))
				      (progn
					(scu-out 'COULD-NOT-FIND)
					(format t "~d was not found in the support.~%"))))
				(progn
				  (scu-out 'NOT-ABBREV)
				  (format t "~d is not an abbreviation.~%"))))))
			 ((UNFOLDGOALHEAD FH)
			  (let* ((C (pf-prop tp))
				 (name (term-extr-head C)))
			    (if (abbrevname-p name)
				(let* ((args (term-extr-args C))
				       (e1 (app-n (intern (format nil "~d#F" name)) args))
				       (e1tp (ctx-extract-type ctx e1)))
				  (if (and e1tp (dpi-p e1tp)
					   (pf-p (dpi-dom e1tp)))
				      (multiple-value-bind
				       (tasklist2 theta2)
				       (task-claim (dpi-dom e1tp) task (cdr *scip-tasks*) *scip-theta*)
				       (multiple-value-bind
					(evar1 ctx1 names1 tp1 namedectx1 namesubst1)
					(task-components (car tasklist2))
					(let ((e (app (dbshift-n 1 e1) 0)))
					  (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
					  (setq *scip-tasks* (cdr tasklist2))
					  (setq *scip-theta*
						(compose-theta-1
						 evar1
						 (lam-ctx ctx1 e)
						 theta2))
					  (scu-out 'OK)
					  (format t "OK~%"))))
				    (progn
				      (scu-out 'FAILED)
				      (format t "Problem folding abbrev at head of goal.~%There is no excuse for this failure.~%"))))
			      (progn
				(scu-out 'GOAL-NOT-ABBREV-HEAD)
				(format t "Head of goal is not an abbrev~%")))))
			 ((UNFOLDHEAD UFH)
			  (if (cadr r)
			      (let ((name (if (symbolp (cadr r)) (cadr r) (intern (cadr r))))
				    (i nil))
				(if (abbrevname-p name)
				    (do ((j 0 (1+ j))
					 (ctx2 ctx (cdr ctx2)))
					((or i (null ctx2)))
					(when (and (pf-p (car ctx2))
						   (eq (term-extr-head (pf-prop (car ctx2))) name))
					  (setq i j)))
				  (setq i (position name names :test #'string=)))
				(if i
				    (let* ((pfprop (ctx-extract-type ctx i))
					   (prop (pf-prop pfprop))
					   (args (term-extr-args prop))
					   (h (intern (format nil "~d#U" (term-extr-head prop))))
					   (e (app (app-n h args) i))
					   (newtp
					    (ctx-extract-type ctx e)))
				      (if newtp
					  (progn
					    (scip-add-fact e newtp)
					    (scu-out 'OK)
					    (format t "OK~%"))
					(progn
					  (scu-out 'FAILED)
					  (format t "Error expanding abbreviation ~d.~%There is no excuse for this.~%" name))))
				  (progn
				    (scu-out 'NO-ABBREV-HEAD)
				    (format t "Could not identify context element with abbrev at head~%"))))
			    (let ((name nil)
				  (i nil))
			      (do ((j 0 (1+ j))
				   (ctx2 ctx (cdr ctx2)))
				  ((or i (null ctx2)))
				  (when (pf-p (car ctx2))
				    (setq name (term-extr-head (pf-prop (car ctx2))))
				    (when (and (symbolp name) (abbrevname-p name))
				      (setq i j))))
			      (if i
				  (let* ((pfprop (ctx-extract-type ctx i))
					 (prop (pf-prop pfprop))
					 (args (term-extr-args prop))
					 (h (intern (format nil "~d#U" name)))
					 (e (app (app-n h args) i))
					 (newtp
					  (ctx-extract-type ctx e)))
				    (if newtp
					(progn
					  (scip-add-fact e newtp)
					  (scu-out 'OK)
					  (format t "OK~%"))
				      (progn
					(scu-out 'FAILED)
					(format t "Error expanding abbreviation ~d.~%There is no excuse for this.~%" name))))
				(progn
				  (scu-out 'NO-ABBREV-HEAD)
				  (format t "Could not identify context element with abbrev at head~%"))))))
			 (ARGS=
			  (when (and *auto-gen-congruence* (> *congruences-stage* 1))
			    (let ((C (pf-prop tp)))
			      (if (and (app-p C) (app-p (app-func C))
				       (or (eq (app-func (app-func C)) '|eq|)
					   (eq (app-func (app-func C)) '|equiv|)))
				  (let* ((lhs (app-arg (app-func C)))
					 (rhs (app-arg C))
					 (lhsh (term-extr-head lhs))
					 (rhsh (term-extr-head rhs)))
				    (if (equal lhsh rhsh)
					(if (symbolp lhsh)
					    (let ((cc (auto-gen-name lhsh "Cong" nil)))
					      (if (and (get cc 'dbtype) (equal (get cc 'dbtype)
									       (congruence-pf-type (get lhsh 'dbtype) lhsh)))
						  (let ((pftrm cc)
							(largs (term-extr-args lhs))
							(rargs (term-extr-args rhs))
							(altp nil)
							(artp nil)
							(cctp (get cc 'dbtype))
							(tasks2 (cdr *scip-tasks*)))
						    (do ((tph (get lhsh 'dbtype) (dpi-cod tph)))
							((not (dpi-p tph)))
							(setq altp (dpi-dom cctp))
							(setq cctp (normalize-type (dbsubst-type-0 (dpi-cod cctp) (car largs))))
							(setq artp (dpi-dom cctp))
							(setq cctp (normalize-type (dbsubst-type-0 (dpi-cod cctp) (car rargs))))
							(let ((apftrm (if (heq altp artp)
									  (congruence-make-equation-pf ctx (car largs) (car rargs)
												       altp)
									nil)))
							  (if apftrm
							      (progn
								(setq cctp (normalize-type (dbsubst-type-0 (dpi-cod cctp) apftrm)))
								(setq pftrm (app (app (app pftrm (car largs)) (car rargs))
										 apftrm))
								)
							    (let ((newevar (intern-gensym)))
							      (setf (get newevar 'evar) t)
							      (setf (get newevar 'dbtype) (dpi-ctx ctx (dpi-dom cctp)))
							      (push (list newevar ctx names (dpi-dom cctp) namedectx namesubst) tasks2)
							      (let ((newevar-ap (app-n-1-to-0 (length ctx) newevar)))
								(setq cctp (normalize-type (dbsubst-type-0 (dpi-cod cctp) newevar-ap)))
								(setq pftrm (app (app (app pftrm (car largs)) (car rargs))
										 newevar-ap)))))
							  (pop largs)
							  (pop rargs)
							  ))
						    (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
						    (setq pftrm (lam-ctx ctx pftrm))
						    (setq *scip-theta* (compose-theta-1 evar pftrm *scip-theta*))
						    (setq *scip-tasks* tasks2)
						    (scu-out 'OK)
						    (format t "OK~%"))					     
						(progn
						  (scu-out 'FAILED)
						  (format t "Congruence Problem with ~d~%" lhsh))))
					  (progn
					    (scu-out 'FAILED)
					    (format t "Cannot apply congruence with local head~%")))
				      (progn
					(scu-out 'NOT-MATCHING-HEADS)
					(format t "Sides of equation do not have matching heads: ~d =/= ~d~%" lhsh rhsh))))
				(progn
				  (scu-out 'NOT-EQN)
				  (format t "Goal is not an equation~%"))))))
			 (REDUCEGOAL
			  (when (and *auto-gen-congruence* (> *congruences-stage* 1))
			    (let ((C (pf-prop tp)))
			      (cond ((and (app-p C) (app-p (app-func C))
					  (eq (app-func (app-func C)) '|eq|))
				     (let* ((lhs (app-arg (app-func C)))
					    (rhs (app-arg C)))
				       (multiple-value-bind
					(rlhs lpftrm)
					(reduce-obj ctx lhs)
					(multiple-value-bind
					 (rrhs rpftrm)
					 (reduce-obj ctx rhs)
					 (if lpftrm
					     (if rpftrm
						 (let* ((newgoal (app-n '|eq| (list rlhs rrhs)))
							(newevar (intern-gensym))
							(newevar-ap (app-n-1-to-0 (length ctx) newevar)))
						   (setf (get newevar 'evar) t)
						   (setf (get newevar 'dbtype) (dpi-ctx ctx (pf newgoal)))
						   (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
						   (setq *scip-theta* (compose-theta-1
								       evar
								       (lam-ctx ctx
										(app-n '|boxeq|
										       (list
											lhs rlhs
											rhs rrhs
											lpftrm rpftrm
											newevar-ap)))
								       *scip-theta*))
						   (setq *scip-tasks* (cons
								       (list newevar ctx names (pf newgoal) namedectx namesubst)
								       (cdr *scip-tasks*)))
						   (scu-out 'OK)
						   (format t "OK~%"))
					       (let* ((newgoal (app-n '|eq| (list rlhs rhs)))
						      (newevar (intern-gensym))
						      (newevar-ap (app-n-1-to-0 (length ctx) newevar)))
						 (setf (get newevar 'evar) t)
						 (setf (get newevar 'dbtype) (dpi-ctx ctx (pf newgoal)))
						 (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
						 (setq *scip-theta* (compose-theta-1
								     evar
								     (lam-ctx ctx
									      (app-n '|boxeq|
										     (list
										      lhs rlhs
										      rhs rhs
										      lpftrm (app '|eqI| rhs)
										      newevar-ap)))
								     *scip-theta*))
						 (setq *scip-tasks* (cons
								     (list newevar ctx names (pf newgoal) namedectx namesubst)
								     (cdr *scip-tasks*)))
						 (scu-out 'OK)
						 (format t "OK~%")))
					   (if rpftrm
					       (let* ((newgoal (app-n '|eq| (list lhs rrhs)))
						      (newevar (intern-gensym))
						      (newevar-ap (app-n-1-to-0 (length ctx) newevar)))
						 (setf (get newevar 'evar) t)
						 (setf (get newevar 'dbtype) (dpi-ctx ctx (pf newgoal)))
						 (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
						 (setq *scip-theta* (compose-theta-1
								     evar
								     (lam-ctx ctx
									      (app-n '|boxeq|
										     (list
										      lhs lhs
										      rhs rrhs
										      (app '|eqI| lhs) rpftrm
										      newevar-ap)))
								     *scip-theta*))
						 (setq *scip-tasks* (cons
								     (list newevar ctx names (pf newgoal) namedectx namesubst)
								     (cdr *scip-tasks*)))
						 (scu-out 'OK)
						 (format t "OK~%"))
					     (progn
					       (scu-out 'CANNOT-REDUCE-GOAL)
					       (format t "Cannot reduce goal~%"))))))))
				    (t (scu-out 'CANNOT-REDUCE-GOAL) (format t "Cannot reduce goal~%"))))))
			 (t (scu-out 'NOT-SCIP-COMMAND) nil))))))))
    (let ((trm (normalize (cdr (assoc *scip-gevar* *scip-theta*)))))
      (cond ((free-evars trm)
	     (scu-out 'PFTERM-HAS-FREES)
 	     (format t "Term has remaining free evars~%")
	     (force-output *standard-output*)
	     )
 	    ((not (ctx-term-type-p *emptyctx* trm *scip-gtp*))
	     (scu-out 'PFTERM-WRONG-TYPE)
 	     (format t "Term does not have the right tp~%")
	     (force-output *standard-output*)
	     )
	    (claim
	     (scu-out (list 'SCIP-PFTERM trm))
	     (let ((q nil)
		   (r nil))
	       (format t "Output PAM Proof Term to File [y/n, Default y]>")
	       (force-output *standard-output*)
	       (scu-out 'PROMPT-BOOL)
	       (setq q (read *scunak-socket* nil nil))
	       (when q
		 (format t "Filename [Default File ~d]>" *scip-pam-proof-file*)
		 (force-output *standard-output*)
		 (scu-out 'PROMPT-FILENAME)
		 (setq r (read-scunak-socket-line))
		 (unless (equal r "")
		   (when r (setq *scip-pam-proof-file* r)))
		 (let ((f (open *scip-pam-proof-file* :direction :output
				:if-does-not-exist :create
				:if-exists :append)))
		   (output1-sig (reverse *scip-lemmas*) f)
		   (format f "~d:=~d.~%" claim (output1-normal-string trm))
		   (close f)))
	       (format t "Output Lisp Proof Term to File [y/n, Default y]>")
	       (force-output *standard-output*)
	       (scu-out 'PROMPT-BOOL)
	       (setq q (read *scunak-socket* nil nil))
	       (when q
		 (format t "Filename [Default File ~d]>" *scip-lisp-proof-file*)
		 (force-output *standard-output*)
		 (scu-out 'PROMPT-FILENAME)
		 (setq r (read-scunak-socket-line))
		 (unless (equal r "")
		   (when r (setq *scip-lisp-proof-file* r)))
		 (let ((f (open *scip-lisp-proof-file* :direction :output
				:if-does-not-exist :create
				:if-exists :append)))
		   (output-sig (reverse *scip-lemmas*) f)
		   (format f "(claim2abbrev '~S~%~d~%)~%" claim (output-term-string trm))
		   (close f)))
	       (claim2abbrev claim trm)
	       ))
 	    (t
	     (scu-out (list 'SCIP-PFTERM trm))
 	     (format t "Successful Term:~%~d~%~d~%"
 		     (output-term-string trm)
 		     (output1-normal-string trm))))
      (scu-out 'SCIP-OUT)
      (format t "Scip Out!~%")
      (force-output *standard-output*)
      )))

(defun ibeta2-redex-p (ctx trm)
  (and (iap2-p trm)
       (let ((f (gen-pair-fst (app-arg (app-func trm)))))
	 (and (fst-p f)
	      (ilam2-p (fst-arg f))
	      (ctx-terms-eq-type ctx
				 (app-arg (app-func (app-func (app-func trm))))
				 (app-arg (app-func (app-func (fst-arg f))))
				 (obj))
	      (ctx-terms-eq-type ctx
				 (app-arg (app-func (app-func trm)))
				 (app-arg (app-func (fst-arg f)))
				 (obj))
	      ))))

(defun ieta2-redex-p (ctx trm)
  (and (ilam2-p trm)
       (let ((b (gen-pair-fst (gen-lam-body (app-arg trm)))))
	 (and (fst-p b)
	      (iap2-p (fst-arg b))
	      (equal (app-arg (fst-arg b)) 0)
	      (not (nintrm-p 0 (app-func (fst-arg b))))
	      (ctx-terms-eq-type ctx
				 (app-arg (app-func (app-func trm)))
				 (app-arg (app-func (app-func (app-func (fst-arg b)))))
				 (obj))
	      (ctx-terms-eq-type ctx
				 (app-arg (app-func trm))
				 (app-arg (app-func (app-func (fst-arg b))))
				 (obj))
	      ))))

(defun iap2-p (trm)
  (and (app-p trm)
       (app-p (app-func trm))
       (app-p (app-func (app-func trm)))
       (app-p (app-func (app-func (app-func trm))))
       (eq (app-func (app-func (app-func (app-func trm)))) '|ap2|)))

(defun ilam2-p (trm)
  (and (app-p trm)
       (app-p (app-func trm))
       (app-p (app-func (app-func trm)))
       (eq (app-func (app-func (app-func trm))) '|lam2|)))

(defun beta2-declared-p ()
  (and (get '|beta2| 'dbtype)
       (equal (get '|beta2| 'dbtype)
	      '(DPI OBJ DPI OBJ DPI (DPI (DCLASS APP |in| . 1) DCLASS APP |in| . 1)
		    DPI (DCLASS APP |in| . 2) PF APP
		    (APP |eq| FST APP
			 (APP (APP (APP |ap2| . 3) . 2) APP (APP (APP |lam2| . 3) . 2)
			      . 1)
			 . 0)
		    FST APP 1 . 0))))

(defun eta2-declared-p ()
  (and (get '|eta2| 'dbtype)
       (equal (get '|eta2| 'dbtype)
	      '(DPI OBJ DPI OBJ DPI (DCLASS APP |in| APP (APP |funcSet| . 1) . 0) PF
		    APP
		    (APP |eq| FST APP (APP (APP |lam2| . 2) . 1) APP
			 (APP (APP |ap2| . 2) . 1) . 0)
		    FST . 0))))

(defun setbeta-declared-p ()
  (equal (get '|setbeta| 'dbtype)
	 '(DPI OBJ DPI (DPI (DCLASS APP |in| . 0) . PROP) DPI
	       (DCLASS APP |in| . 1) PF APP
	       (APP |equiv| APP (APP |in| APP (APP |dsetconstr| . 2) . 1) FST
		    . 0)
	       APP 1 . 0)))

(defun setbeta-redex-p (ctx trm)
  (and (app-p trm)
       (app-p (app-func trm))
       (eq (app-func (app-func trm)) '|in|)
       (app-p (app-arg (app-func trm)))
       (app-p (app-func (app-arg (app-func trm))))
       (eq (app-func (app-func (app-arg (app-func trm)))) '|dsetconstr|)
       (fst-p (app-arg trm))
       (let ((tp (ctx-extract-type ctx (fst-arg (app-arg trm)))))
	 (and tp (dclass-p tp)
	      (app-p (dclass-pred tp))
	      (eq (app-func (dclass-pred tp)) '|in|)
	      (ctx-terms-eq-type ctx
				 (app-arg (app-func (app-arg (app-func trm))))
				 (app-arg (dclass-pred tp))
				 (obj))))))

; assumes setbeta-redex-p returns t
(defun setbeta-reduce (trm)
  (normalize
   (app (app-arg (app-arg (app-func trm)))
	(fst-arg (app-arg trm)))))

; trm should be of type obj, we check for object-level beta or eta reduction
(defun reduce-obj (ctx trm)
  (cond ((and (fst-p trm) (ibeta2-redex-p ctx (fst-arg trm)) (beta2-declared-p))
	 (let ((f (app-arg (fst-arg (gen-pair-fst (app-arg (app-func (fst-arg trm)))))))
	       (x (app-arg (fst-arg trm))))
	   (values (normalize (fst (app f x)))
		   (app-n '|beta2|
			  (list
			   (app-arg (app-func (app-func (app-func (fst-arg trm)))))
			   (app-arg (app-func (app-func (fst-arg trm))))
			   (app-arg (fst-arg (gen-pair-fst (app-arg (app-func (fst-arg trm))))))
			   (app-arg (fst-arg trm)))))))
	((and (fst-p trm) (ieta2-redex-p ctx (fst-arg trm)) (eta2-declared-p))
	 (let ((g 
		(dbshift-n -1
			   (app-arg (app-func (fst-arg (gen-pair-fst (gen-lam-body (app-arg (fst-arg trm))))))))))
	   (values (fst g)
		   (app-n '|eta2|
			  (list
			   (app-arg (app-func (app-func (fst-arg trm))))
			   (app-arg (app-func (fst-arg trm)))
			   g)))))
	(t nil)))

(defun std-declared-p (&rest r)
  (let ((b t))
    (dolist (x r b)
      (unless (std-declared-1-p x)
	(setq b nil)))))

(defun std-declared-1-p (c)
  (case c
	(|xmcases|
	 (equal (get '|xmcases| 'dbtype)
		'(DPI PROP DPI PROP DPI (DPI (PF . 1) PF . 1) DPI
		      (DPI (PF APP |not| . 2) PF . 2) PF . 2)))
	(|setextsub|
	 (equal (get '|setextsub| 'dbtype)
		'(DPI OBJ DPI OBJ DPI (PF APP (APP |subset| . 1) . 0) DPI
		      (PF APP (APP |subset| . 1) . 2) PF APP (APP |eq| . 3) . 2)))
	(|ap2|
	 (equal (get '|ap2| 'dbtype)
		'(DPI OBJ DPI OBJ DPI (DCLASS APP |in| APP (APP |funcSet| . 1) . 0) DPI
		      (DCLASS APP |in| . 2) DCLASS APP |in| . 2)))
	(|funcext2|
	 (equal (get '|funcext2| 'dbtype)
		'(DPI OBJ DPI OBJ DPI (DCLASS APP |in| APP (APP |funcSet| . 1) . 0) DPI
		      (DCLASS APP |in| APP (APP |funcSet| . 2) . 1) DPI
		      (DPI (DCLASS APP |in| . 3) PF APP
			   (APP |eq| FST APP (APP (APP (APP |ap2| . 4) . 3) . 2) . 0)
			   FST APP (APP (APP (APP |ap2| . 4) . 3) . 1) . 0)
		      PF APP (APP |eq| FST . 2) FST . 1)))
	(|funcSet|
	 (equal (get '|funcSet| 'dbtype)
		'(DPI OBJ DPI OBJ . OBJ)))
	(|subsetI1|
	 (equal (get '|subsetI1| 'dbtype)
		'(DPI OBJ DPI OBJ DPI
		      (DPI (DCLASS APP |in| . 1) PF APP (APP |in| . 1) FST . 0) PF APP
		      (APP |subset| . 2) . 1)))
	(|subset|
	 (equal (get '|subset| 'dbtype)
		'(DPI OBJ DPI OBJ . PROP)))
	(|dand|
	 (equal (get '|dand| 'dbtype)
		'(DPI PROP DPI (DPI (PF . 0) . PROP) . PROP)))
	(|dandI|
	 (equal (get '|dandI| 'dbtype)
		'(DPI PROP DPI (DPI (PF . 0) . PROP) DPI (PF . 1) DPI (PF APP 1 . 0) PF
		      APP (APP |dand| . 3) . 2)))
	(|andI|
	 (equal (get '|andI| 'dbtype)
		'(DPI PROP DPI PROP DPI (PF . 1) DPI (PF . 1) PF APP (APP |and| . 3)
		      . 2)))
	(|and|
	 (equal (get '|and| 'dbtype)
		'(DPI PROP DPI PROP . PROP)))
	(|dallI|
	 (equal (get '|dallI| 'dbtype)
		'(DPI OBJ DPI (DPI (DCLASS APP |in| . 0) . PROP) DPI
		      (DPI (DCLASS APP |in| . 1) PF APP 1 . 0) PF APP (APP |dall| . 2)
		      . 1)))
	(|dall|
	 (equal (get '|dall| 'dbtype)
		'(DPI OBJ DPI (DPI (DCLASS APP |in| . 0) . PROP) . PROP)))
	(|dimp|
	 (equal (get '|dimp| 'dbtype)
		'(DPI PROP DPI (DPI (PF . 0) . PROP) . PROP)))
	(|dimpI|
	 (equal (get '|dimpI| 'dbtype)
		'(DPI PROP DPI (DPI (PF . 0) . PROP) DPI (DPI (PF . 1) PF APP 1 . 0) PF
		      APP (APP |dimp| . 2) . 1)))
	(|impI|
	 (equal (get '|impI| 'dbtype)
		'(DPI PROP DPI PROP DPI (DPI (PF . 1) PF . 1) PF APP (APP |imp| . 2)
		      . 1)))
	(|imp|
	 (equal (get '|imp| 'dbtype)
		'(DPI PROP DPI PROP . PROP)))
	(|or|
	 (equal (get '|or| 'dbtype)
		'(DPI PROP DPI PROP . PROP)))
	(|orE|
	 (equal (get '|orE| 'dbtype)
		'(DPI PROP DPI PROP DPI (PF APP (APP |or| . 1) . 0) DPI PROP DPI
		      (DPI (PF . 3) PF . 1) DPI (DPI (PF . 3) PF . 2) PF . 2)))
	(|eq|
	 (equal (get '|eq| 'dbtype)
		'(DPI OBJ DPI OBJ . PROP)))
	(|eqI|
	 (equal (get '|eqI| 'dbtype)
		'(DPI OBJ PF APP (APP |eq| . 0) . 0)))
	(|setadjoin|
	 (equal (get '|setadjoin| 'dbtype)
		'(DPI OBJ DPI OBJ . OBJ)))
	(|setadjoinE|
	 (equal (get '|setadjoinE| 'dbtype)
		'(DPI OBJ DPI OBJ DPI OBJ DPI
		      (PF APP (APP |in| APP (APP |setadjoin| . 2) . 1) . 0) DPI PROP
		      DPI (DPI (PF APP (APP |eq| . 2) . 4) PF . 1) DPI
		      (DPI (PF APP (APP |in| . 4) . 3) PF . 2) PF . 2)))
	(|dex|
	 (equal (get '|dex| 'dbtype)
		'(DPI OBJ DPI (DPI (DCLASS APP |in| . 0) . PROP) . PROP)))
	(|dexE|
	 (equal (get '|dexE| 'dbtype)
		'(DPI OBJ DPI (DPI (DCLASS APP |in| . 0) . PROP) DPI
		      (PF APP (APP |dex| . 1) . 0) DPI PROP DPI
		      (DPI (DCLASS APP |in| . 3) DPI (PF APP 3 . 0) PF . 2) PF . 1)))
	(|in|
	 (equal (get '|in| 'dbtype)
		'(DPI OBJ DPI OBJ . PROP)))
	(|not|
	 (equal (get '|not| 'dbtype)
		'(DPI PROP . PROP)))
	(|false|
	 (equal (get '|false| 'dbtype)
		'PROP))
	(|notI|
	 (equal (get '|notI| 'dbtype)
		'(DPI PROP DPI (DPI (PF . 0) PF . |false|) PF APP |not| . 1)))
	(|contradiction|
	 (equal (get '|contradiction| 'dbtype)
		'(DPI PROP DPI (DPI (PF APP |not| . 0) PF . |false|) PF . 1)))
	))

(defun save-scip-proof (filename)
  (let ((c t))
    (when (probe-file filename)
      (format t "File exists. Overwrite? [y/n]")
      (let ((resp (read-line)))
	(unless (member resp '("y" "Y" "yes" "Yes") :test #'equal)
	  (setq c nil))))
    (when c
      (let ((f (open filename :direction :output :if-exists :supersede)))
	(format f "(setq *scip-tasks* '(~%")
	(dolist (task *scip-tasks*)
	  (format f "~d" (task-readable-string task)))
	(format f "))~%")
	(format f "(setq *scip-taskstack* '~d)~%"
		(function-readable-string *scip-taskstack*)
		)
	(dolist (v '(*scip-theta*
		     *scip-gevar* *scip-gtp* *scip-usable*
		     *scip-fst-usable* *scip-snd-usable* 
		     *scip-defn-usable* *scip-eager-elims* *scip-assnum*
		     *scip-factnum*))
	  (format f "(setq ~S '~S)~%" v (eval v)))
	(close f)))))

(defun function-readable-string (s)
  (if (consp s)
      (format nil "(~d . ~d)"
	      (function-readable-string (car s))
	      (function-readable-string (cdr s)))
    (if (functionp s)
	(format nil "#'IDENTITY")
      (format nil "~S" s))))

(defun task-readable-string (task)
  (format nil "(~S ~S ~S ~S ~S ~d)"
	  (car task)
	  (cadr task)
	  (caddr task)
	  (caddr (cdr task))
	  (caddr (cddr task))
	  (namesubst-readable-string (caddr (cdddr task)))))

(defun namesubst-readable-string (ns)
  (if (consp ns)
      (format nil "(~d #'IDENTITY . ~d)"
	      (car ns)
	      (namesubst-readable-string (cddr ns)))
    (format nil "~S" ns)))

(defun scip-add-fact (e newtp)
  (multiple-value-bind
   (evar ctx names tp namedectx namesubst)
   (task-components (car *scip-tasks*))
   (let* ((name (format nil "fact~d" (incf *scip-factnum*)))
	  (namez (intern name))
	  (ctx2 (ctx-cons newtp ctx))
	  (newevar (intern-gensym))
	  (tp2 (dbshift-type-n 1 tp))
	  (newevartp (dpi-ctx ctx2 tp2)))
     (setf (get namez 'bvar) t)
     (setf (get namez 'dbtype) (dbsubst-type newtp #'identity namesubst))
     (setf (get newevar 'evar) t)
     (setf (get newevar 'dbtype) newevartp) ; global
     (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
     (pop *scip-tasks*)
     (setq *scip-theta* (compose-theta-1 evar (term-for-extending-ctx ctx newevar e) *scip-theta*))
     (push (list newevar ctx2 (cons name names) tp2
		 (cons (list namez (get namez 'dbtype)) namedectx)
		 (cons namez (cons #'identity namesubst))
		 )
	   *scip-tasks*))))

					; returns values new task list (values tasklist theta)
					; first two tasks on new task list correspond to: 
					; proof of goal using claim; proof of claim
					; never fails
(defun task-claim (claimtp task tasklist theta)
  (let* ((evar (car task))
 	 (ctx (cadr task))
 	 (names (nth 2 task))
 	 (tp (nth 3 task))
 	 (namedectx (nth 4 task))
 	 (namesubst (nth 5 task))
 	 (claimctxtp (dpi-ctx ctx claimtp))
 	 (claimevar (intern-gensym))
 	 (n (length ctx))
 	 (claimtrm (app-n-1-to-0 n claimevar))
 	 (name (format nil "fact~d" (incf *scip-factnum*)))
 	 (namez (intern name))
 	 (ctx2 (ctx-cons claimtp ctx))
 	 (newevar (intern-gensym))
 	 (tp2 (dbshift-type-n 1 tp))
 	 (newevartp (dpi-ctx ctx2 tp2)))
    (setf (get namez 'bvar) t)
    (setf (get namez 'dbtype) (dbsubst-type claimtp #'identity namesubst))
    (setf (get newevar 'evar) t)
    (setf (get newevar 'dbtype) newevartp) ; global
    (setf (get claimevar 'evar) t)
    (setf (get claimevar 'dbtype) claimctxtp) ; global
    (setq theta (compose-theta-1 evar (term-for-extending-ctx ctx newevar claimtrm) theta))
    (setq tasklist
 	  (cons (list newevar ctx2 (cons name names) tp2
 		      (cons (list namez (get namez 'dbtype)) namedectx)
 		      (cons namez (cons #'identity namesubst)))
 		(cons (list claimevar ctx names claimtp namedectx namesubst)
 		      tasklist)))
    (values tasklist theta)))

					; (values [t|nil] theta)
(defun task-done-1 (task theta &optional hence)
  (let ((z (quick-fill-gap (cadr task) (nth 3 task) *scip-usable* t 0 hence)))
    (if z
 	(let ((tmp (caar z)))
 	  (values t (compose-theta-1 (car task) tmp theta)))
      nil)))

#+:allegro
(defun task-done (task theta &optional hence)
  (if *scunak-time-limit*
      (mp:with-timeout (*scunak-time-limit* (scu-out 'TIMED-OUT) (values nil "Timed Out")) (task-done-1 task theta hence))
    (task-done-1 task theta hence)))

#-:allegro
(defun task-done (task theta &optional hence)
  (task-done-1 task theta hence))
					; (values [t|nil] tasklist theta)
(defun task-hence (tp task tasklist theta)
  (multiple-value-bind
   (tasklist2 theta2)
   (task-claim tp task tasklist theta)
   (let ((task1 (car tasklist2))
 	 (task2 (cadr tasklist2)))
     (multiple-value-bind
      (succ theta3)
      (task-done task2 theta2 t)
      (if succ
 	  (values t (cons task1 (cddr tasklist2)) theta3)
 	nil)))))

					; (values [t|nil] tasklist theta)
(defun task-fact (tp task tasklist theta)
  (multiple-value-bind
   (tasklist2 theta2)
   (task-claim tp task tasklist theta)
   (let ((task1 (car tasklist2))
 	 (task2 (cadr tasklist2)))
     (multiple-value-bind
      (succ theta3)
      (task-done task2 theta2 nil)
      (if succ
 	  (values t (cons task1 (cddr tasklist2)) theta3)
 	nil)))))

(defun task-willshow (tp task tasklist theta)
  (multiple-value-bind
   (tasklist2 theta2)
   (task-claim tp task tasklist theta)
   (let ((task1 (car tasklist2))
 	 (task2 (cadr tasklist2)))
     (multiple-value-bind
      (succ theta3)
      (task-done task1 theta2 nil)
      (if succ
 	  (values t (cons task2 (cddr tasklist2)) theta3)
 	nil)))))

(defun task-close-under-simple-elims (task tasklist theta)
  (let ((ctx (cadr task))
	(elims nil))
    (dotimes (i (length ctx))
      (let* ((tp (ctx-extract-type ctx i))
	     (e2
	      (task-close-under-simple-elims-2 ctx i tp)))
	 (setq elims (append e2 elims))))
    (let ((i 0))
      (dolist (e elims)
	(let ((trm2 (dbshift-n i (car e)))
	      (tp2 (dbshift-type-n i (cdr e))))
	  (unless (member-ctx tp2 ctx)
	    (multiple-value-bind
	     (tasks2 theta2)
	     (task-claim tp2 task tasklist theta)
	     (setq task (car tasks2))
	     (setq tasklist (cddr tasks2))
	     (let* ((easy (cadr tasks2))
		    (evar2 (car easy)))
	       (setq theta (compose-theta-1 evar2
					    (lam-ctx ctx trm2)
					    theta2)))
	     (incf i)
	     (setq ctx (cadr task))))))
      (if (> i 0)
	  (values t (cons task tasklist) theta)
	nil))))

(defun task-close-under-simple-elims-2 (ctx trm tp)
  (if (dpi-p tp)
      (let ((e2 (task-close-under-simple-elims-2
		 (ctx-cons (dpi-dom tp) ctx)
		 (gen-lam-body trm)
		 (dpi-cod tp))))
	(mapcar #'(lambda (x)
		    (cons (lam (car x))
			  (dpi (dpi-dom tp) (cdr x))))
		e2))
    (if (dclass-p tp)
	(task-close-under-simple-elims-2
	 ctx (gen-pair-snd trm)
	 (pf (normalize (app (dclass-pred tp) (gen-pair-fst trm)))))
      (if (pf-p tp)
	  (let ((prop (pf-prop tp)))
	    (cond ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|and|))
		   (append (task-close-under-simple-elims-2
			    ctx
			    (app-l '|andEL| 
				   (app-arg (app-func prop))
				   (app-arg prop) trm)
			    (pf (app-arg (app-func prop))))
			   (task-close-under-simple-elims-2
			    ctx
			    (app-l '|andER| 
				   (app-arg (app-func prop))
				   (app-arg prop) trm)
			    (pf (app-arg prop)))))
		  ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|dand|))
		   (let* ((trml (app-l '|dandEL| 
				       (app-arg (app-func prop))
				       (app-arg prop) trm))
			  (pr (normalize (app (app-arg prop) trml))))
		     (append (task-close-under-simple-elims-2
			      ctx trml
			      (pf (app-arg (app-func prop))))
			     (task-close-under-simple-elims-2
			      ctx
			      (app-l '|dandER| 
				     (app-arg (app-func prop))
				     (app-arg prop) trm)
			      pr))))
		  ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|imp|))
		   (let ((tp2 (dpi (pf (app-arg (app-func prop)))
				   (pf (dbshift-n 1 (app-arg prop))))))
		     (task-close-under-simple-elims-2
		      ctx
		      (app-l '|impE|
			     (app-arg (app-func prop))
			     (app-arg prop) trm)
		      tp2)))
		  ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|dimp|))
		   (let ((tp2 (dpi (pf (app-arg (app-func prop)))
				   (pf (normalize (app (dbshift-n 1 (app-arg prop)) 0))))))
		     (task-close-under-simple-elims-2
		      ctx
		      (app-l '|dimpE|
			     (app-arg (app-func prop))
			     (app-arg prop) trm)
		      tp2)))
		  ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|dall|))
		   (let ((tp2 (dpi (dclass (app '|in| (app-arg (app-func prop))))
				   (pf (normalize (app (dbshift-n 1 (app-arg prop)) 0))))))
		     (task-close-under-simple-elims-2
		      ctx
		      (app-l '|dallE|
			     (app-arg (app-func prop))
			     (app-arg prop) trm)
		      tp2)))
		  (t
		   (list (cons trm tp)))))
	nil))))

; replaced with the better version above
; the old version would get {A}(B=>C) from (A=>(B=>C))
; the new version gets {A}{B}C from (A=>(B=>C)) -- without adding the intermediate version..
(defun task-close-under-simple-elims-old (task tasklist theta)
  (let ((ctx (cadr task)))
    (let ((eliminfo
	   (find-simple-elim ctx ctx 0)))
     (if eliminfo
	 (progn
	   (loop while eliminfo do
;		 (format t "ctx = ~S~%eliminfo = ~S~%" ctx eliminfo) ; delete me
		 (case (car eliminfo)
		       (DCLASS
			(let* ((i (cadr eliminfo))
			       (pred (dclass-pred (ctx-extract-type ctx i))))
			  (multiple-value-bind
			   (tasks2 theta2)
			   (task-claim (pf (normalize (app pred (fst i))))
				       task tasklist theta)
			   (setq task (car tasks2))
			   (setq tasklist (cddr tasks2))
			   (setq theta theta2)
			   (let* ((easy (cadr tasks2))
				  (evar2 (car easy))
				  (trm2 (lam-ctx ctx (snd i))))
			     (setq theta (compose-theta-1 evar2 trm2 theta)))
			   (setq ctx (cadr task)))))
		       (ANDEL
			(let* ((i (cadr eliminfo))
			       (con (pf-prop (ctx-extract-type ctx i))))
			  (multiple-value-bind
			   (tasks2 theta2)
			   (task-claim (pf (app-arg (app-func con)))
				       task tasklist theta)
			   (setq task (car tasks2))
			   (setq tasklist (cddr tasks2))
			   (setq theta theta2)
			   (let* ((easy (cadr tasks2))
				  (evar2 (car easy))
				  (trm2 (lam-ctx ctx (app-n '|andEL|
							    (list (app-arg (app-func con))
								  (app-arg con)
								  i)))))
			     (setq theta (compose-theta-1 evar2 trm2 theta)))
			   (setq ctx (cadr task)))))
		       (ANDER
			(let* ((i (cadr eliminfo))
			       (con (pf-prop (ctx-extract-type ctx i))))
			  (multiple-value-bind
			   (tasks2 theta2)
			   (task-claim (pf (app-arg con))
				       task tasklist theta)
			   (setq task (car tasks2))
			   (setq tasklist (cddr tasks2))
			   (setq theta theta2)
			   (let* ((easy (cadr tasks2))
				  (evar2 (car easy))
				  (trm2 (lam-ctx ctx (app-n '|andER|
							    (list (app-arg (app-func con))
								  (app-arg con)
								  i)))))
			     (setq theta (compose-theta-1 evar2 trm2 theta)))
			   (setq ctx (cadr task)))))
		       (IMPE
			(let* ((i (cadr eliminfo))
			       (imp (pf-prop (ctx-extract-type ctx i))))
			  (multiple-value-bind
			   (tasks2 theta2)
			   (task-claim (dpi (pf (app-arg (app-func imp)))
					    (pf (dbshift-n 1 (app-arg imp))))
				       task tasklist theta)
			   (setq task (car tasks2))
			   (setq tasklist (cddr tasks2))
			   (setq theta theta2)
			   (let* ((easy (cadr tasks2))
				  (evar2 (car easy))
				  (trm2 (lam-ctx ctx (app-n '|impE|
							    (list (app-arg (app-func imp))
								  (app-arg imp)
								  i)))))
			     (setq theta (compose-theta-1 evar2 trm2 theta)))
			   (setq ctx (cadr task)))))
		       (DANDEL
			(let* ((i (cadr eliminfo))
			       (con (pf-prop (ctx-extract-type ctx i))))
			  (multiple-value-bind
			   (tasks2 theta2)
			   (task-claim (pf (app-arg (app-func con)))
				       task tasklist theta)
			   (setq task (car tasks2))
			   (setq tasklist (cddr tasks2))
			   (setq theta theta2)
			   (let* ((easy (cadr tasks2))
				  (evar2 (car easy))
				  (trm2 (lam-ctx ctx (app-n '|dandEL|
							    (list (app-arg (app-func con))
								  (app-arg con)
								  i)))))
			     (setq theta (compose-theta-1 evar2 trm2 theta)))
			   (setq ctx (cadr task)))))
		       (DANDER
			(let* ((i (cadr eliminfo))
			       (con (pf-prop (ctx-extract-type ctx i))))
			  (multiple-value-bind
			   (tasks2 theta2)
			   (task-claim (pf (normalize
					    (app (app-arg con) (app-n '|dandEL|
								      (list (app-arg (app-func con))
									    (app-arg con)
									    i)))))
				       task tasklist theta)
			   (setq task (car tasks2))
			   (setq tasklist (cddr tasks2))
			   (setq theta theta2)
			   (let* ((easy (cadr tasks2))
				  (evar2 (car easy))
				  (trm2 (lam-ctx ctx (app-n '|dandER|
							    (list (app-arg (app-func con))
								  (app-arg con)
								  i)))))
			     (setq theta (compose-theta-1 evar2 trm2 theta)))
			   (setq ctx (cadr task)))))
		       (DIMPE
			(let* ((i (cadr eliminfo))
			       (imp (pf-prop (ctx-extract-type ctx i))))
			  (multiple-value-bind
			   (tasks2 theta2)
			   (task-claim (dpi (pf (app-arg (app-func imp)))
					    (pf (normalize (app (dbshift-n 1 (app-arg imp)) 0))))
				       task tasklist theta)
			   (setq task (car tasks2))
			   (setq tasklist (cddr tasks2))
			   (setq theta theta2)
			   (let* ((easy (cadr tasks2))
				  (evar2 (car easy))
				  (trm2 (lam-ctx ctx (app-n '|dimpE|
							    (list (app-arg (app-func imp))
								  (app-arg imp)
								  i)))))
			     (setq theta (compose-theta-1 evar2 trm2 theta)))
			   (setq ctx (cadr task)))))
		       (ALLE
			(let* ((i (cadr eliminfo))
			       (all (pf-prop (ctx-extract-type ctx i))))
			  (multiple-value-bind
			   (tasks2 theta2)
			   (task-claim (dpi (dclass (app '|in| (app-arg (app-func all))))
					    (pf (normalize (app (dbshift-n 1 (app-arg all)) 0))))
				       task tasklist theta)
			   (setq task (car tasks2))
			   (setq tasklist (cddr tasks2))
			   (setq theta theta2)
			   (let* ((easy (cadr tasks2))
				  (evar2 (car easy))
				  (trm2 (lam-ctx ctx (app-n '|dallE|
							    (list (app-arg (app-func all))
								  (app-arg all)
								  i)))))
			     (setq theta (compose-theta-1 evar2 trm2 theta)))
			   (setq ctx (cadr task)))))
		       )
		 (setq eliminfo
		       (find-simple-elim ctx ctx 0)))
	   (values t (cons task tasklist) theta))
       nil))))

(defun find-simple-elim (ctx fullctx &optional (i 0))
  (if ctx
      (if (pf-p (car ctx))
	  (let ((prop (pf-prop (car ctx))))
	    (cond ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|and|)
			(not (member-ctx (pf (dbshift-n (1+ i) (app-arg (app-func prop)))) fullctx)))
		   (list 'ANDEL i))
		  ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|and|)
			(not (member-ctx (pf (dbshift-n (1+ i) (app-arg prop))) fullctx)))
		   (list 'ANDER i))
		  ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|imp|)
			(not (member-ctx (dpi (pf (dbshift-n (1+ i) (app-arg (app-func prop))))
					      (pf (dbshift-n (+ i 2) (app-arg prop))))
					 fullctx)))
		   (list 'IMPE i))
		  ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|dand|)
			(not (member-ctx (pf (dbshift-n (1+ i) (app-arg (app-func prop)))) fullctx)))
		   (list 'DANDEL i))
		  ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|dand|)
			(not (member-ctx (pf
					  (normalize
					   (app
					    (dbshift-n (1+ i) (app-arg prop))
					    (app-n '|dandEL|
						   (list (dbshift-n (1+ i) (app-arg (app-func prop)))
							 (dbshift-n (1+ i) (app-arg prop))
							 i)))))
					 fullctx)))
		   (list 'DANDER i))
		  ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|dimp|)
			(not (member-ctx (dpi (pf (dbshift-n (1+ i) (app-arg (app-func prop))))
					      (pf
					       (normalize
						(app
						 (dbshift-n (+ i 2) (app-arg prop))
						 0))))
					 fullctx)))
		   (list 'DIMPE i))
		  ((and (app-p prop) (app-p (app-func prop))
			(eq (app-func (app-func prop)) '|dall|)
			(not (member-ctx (dpi (dclass (app '|in|
							   (dbshift-n (1+ i) (app-arg (app-func prop)))))
					      (pf (normalize (app (dbshift-n (+ i 2) (app-arg prop))
								  0))))
					 fullctx)))
		   (list 'ALLE i))
		  (t
		   (find-simple-elim (cdr ctx) fullctx (1+ i)))))
	(if (and (dclass-p (car ctx))
		 (not (member-ctx (pf (normalize (app (dbshift-n (1+ i) (dclass-pred (car ctx))) (fst i))))
				  fullctx)))
	    (list 'DCLASS i)
	  (find-simple-elim (cdr ctx) fullctx (1+ i))))
    nil))

(defun member-ctx (tp ctx)
;  (format t "member-ctx~%tp = ~S~%ctx = ~S~%" tp ctx) ; delete me
  (let ((done nil)
	(i -1)
	(n (length ctx)))
    (loop until done do
	  (incf i)
	  (if (< i n)
	      (when (ctx-types-eq ctx tp (ctx-extract-type ctx i))
		(setq done t))
	    (setq i nil done t)))
    i))
      
(defun task-components (task)
  (values (car task) (cadr task) (nth 2 task)
 	  (nth 3 task) (nth 4 task) (nth 5 task)))

(defun print-scip-help ()
  (format t "You are currently in the Scip level (Scunak Interactive Prover).~%")
  (format t "Scip Commands:~%")
  (format t "d  % assert that the goal (or current subgoal) is done.~%")
  (format t "willshow % reduce current goal to given subgoal~%")
  (format t "hence % infer given proposition from last assertion in context~%")
  (format t "clearly % infer given proposition~%")
  (format t "apply % apply a given extraction proof term to infer a proposition~%")
  (format t "claim % assert an arbitrary proposition to be used and proved later~%")
  (format t "claimtype % assert a first-order type returning a proof type to be used and proved later~%")
  (format t "lemma % add a new claim to the global signature and use it in this proof~%")
  (format t "b  % choose a backwards reasoning step introducing at most one new subgoal~%")
  (format t "b2  % choose a backwards reasoning step introducing at most two new subgoals~%")
  (format t "f  % choose a forwards reasoning step introducing at most one new subgoal~%")
  (format t "contradiction % proof by contradiction~%")
  (format t "xmcases % use proof by cases based on P or (not P), where P is given by the user~%")
  (format t "cases % use proof by cases if a disjunction is in the context.~%")
  (format t "exists <name> % claim and use the existence of a member of set satisfying a property~%")
  (format t "intro % apply an (generic) introduction rule to prove a particular kind of goal (depends on the kind of goal)~%")
  (format t "unfoldgoalhead  % If head of goal is an abbreviation, prove the unfolded version~%")
  (format t "unfoldhead <factname> % If factname in context has an abbreviation at the head, unfold it~%")
  (format t "unfoldhead <abbrevname> % Find a fact in context with <abbrevname> at head, and unfold <abbrevname>~%")
  (format t "unfoldgoal <abbrevname> % Unfold outermost occurrences of <abbrevname> in the goal~%")
  (format t "unfold <abbrevname> % Unfold outermost occurrences of <abbrevname> in the most recent fact containing <abbrevname>~%")
  (format t "reducegoal % reduce the goal (eg, using beta and eta rules)~%")
  (format t "args= % reduce a goal ((f A1 ... An)==(f B1 ... Bn)) to showing each Ai is the same as Bi~%")
  (format t "undo  % undo~%")
  (format t "pplan  % print the current plan~%")
  (format t "pplan*  % print the current plan omitting proof term parts of pairs~%")
  (format t "pstatus  % print all gaps with supports~%")
  (format t "choose-task % Choose which gap is current~%")
  (format t "pterm  % print the current (open) proof term~%")
  (format t "help  % print this message~%")
  (format t "help <name> % print info about name~%")
  (format t "q  % quit~%")
  )

(defun symmetric-prop-p (e)
  (if (and (app-p e) (app-p (app-func e)))
      (let ((op (app-func (app-func e))))
	(if (eq op '|eq|) ; later can make this more general
	    '|symeq|
	  nil))
    nil))

; rethink where this up-to-symmetry code belongs
;				(let ((symc (symmetric-prop-p e)))
;				  (if symc
;				      (let ((e2 (app (app (app-func (app-func e) )
;							  (app-arg e))
;						     (app-arg (app-func e)))))
;					(let ((symtp (pf e2)))
;					  (task-claim???)
;					  (multiple-value-bind
;					   (succ1 tasklist1 theta1)
;					   (task-hence newtp task (cdr *scip-tasks*) *scip-theta*)
;					   (if succ1
;					       (progn
;						 (format t "Correct.~%")
;						 (push (list *scip-tasks* *scip-theta*) *scip-taskstack*)
;						 (setq *scip-tasks* tasklist1)
;						 (setq *scip-theta* theta1))
;					     (format t "Could not justify hence.~%")))))

(defun store-scip (name)
  (setf (get name '*scip-gevar*) *scip-gevar*)
  (setf (get name '*scip-gtp*) *scip-gtp*)
  (setf (get name '*scip-taskstack*) *scip-taskstack*)
  (setf (get name '*scip-tasks*) *scip-tasks*)
  (setf (get name '*scip-theta*) *scip-theta*)
  (setf (get name '*scip-assnum*) *scip-assnum*)
  (setf (get name '*scip-factnum*) *scip-factnum*)
  (setf (get name '*scip-usable*) *scip-usable*)
  (setf (get name '*scip-fst-usable*) *scip-fst-usable*)
  (setf (get name '*scip-snd-usable*) *scip-snd-usable*)
  )

(defun restore-scip (name)
  (setq *scip-gevar* (get name '*scip-gevar*))
  (setq *scip-gtp* (get name '*scip-gtp*))
  (setq *scip-taskstack* (get name '*scip-taskstack*))
  (setq *scip-tasks* (get name '*scip-tasks*))
  (setq *scip-theta* (get name '*scip-theta*))
  (setq *scip-assnum* (get name '*scip-assnum*))
  (setq *scip-factnum* (get name '*scip-factnum*))
  (setq *scip-usable* (get name '*scip-usable*))
  (setq *scip-fst-usable* (get name '*scip-fst-usable*))
  (setq *scip-snd-usable* (get name '*scip-snd-usable*))
  )

(defun string-to-string-list (s)
  (let ((sl nil)
	(curr nil))
    (dotimes (i (length s))
      (if (string-to-string-list-space-p (aref s i))
	  (when curr
	    (push curr sl)
	    (setq curr nil))
	(if curr
	    (setq curr (format nil "~d~d" curr (aref s i)))
	  (setq curr (format nil "~d" (aref s i))))))
    (if curr
	(reverse (cons curr sl))
      (reverse sl))))

(defun string-to-string-list-space-p (c)
  (member c '(#\space #'\newline #\return)))

(defun input1l-prop-n (a namedectx)
  (let ((b (input1l-prop a)))
    (if b
	(normalize (named-term-to-db-1 (mapcar #'car namedectx) b))
      nil)))

(defun input1l-extr-n (a namedectx)
  (multiple-value-bind
   (b tp)
   (input1l-extr a)
   (if b
       (values (normalize (named-term-to-db-1 (mapcar #'car namedectx) b))
	       tp)
     nil)))

(defun input1l-dtype-n (a namedectx)
  (let ((b (input1l-dtype a)))
    (if b
	(normalize-type (named-type-to-db-1 (mapcar #'car namedectx) b))
      nil)))
