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

(defvar *tutor-alts-stack* nil)
(defvar *tutor-alts* nil)
(defvar *student-name* "Chad")
(defvar *student-stream* t)
(defvar *main-stream* t)
(defvar *tutor-max-tasks* 2)
(defvar *tutor-compute-result* nil)
(defvar *sig-irrelevant* nil)
(defvar *sig-granularity-toohigh* nil)
(defvar *sig-granularity-perfect* nil)
(defvar *sig-granularity-toolow* nil)
(defvar *tutor-check-low-granularity* nil)
(defvar *tutor-socket* nil)
(defvar *tutor-auto-back* nil)
(defvar *tutor-keep-done* nil)
(defvar *tutor-eager-elims* t)
(defvar *tutor-nl* t)

;(defvar *tutor-language* 'GERMAN)
(defvar *tutor-language* 'ENGLISH)

(defvar *tutor-autoset-sig* nil)

(defun tutor-initfn ()
  (let ((prefilenames (command-line-arg-several "-p"))
	(filenames (command-line-arg-several "-f"))
	(infofilenames (command-line-arg-several "-i"))
	(claimname (command-line-arg "-c"))
	(color (command-line-switch "-C"))
	(mach (command-line-arg "-m"))
	(sock (command-line-arg "-s"))
	(verb (command-line-switch "-v"))
	(verb2 (command-line-switch "-V"))
	(studentname (command-line-arg "-n")))
    (unless claimname
      (fail (format nil "Scutor must be given a claim name using -c")))
    #+:allegro
    (when (and mach sock)
      (setq *tutor-socket*
	    (acl-socket:make-socket :remote-host mach :remote-port (read-from-string sock)))
      (setq *standard-output* *tutor-socket*)
      (setq *standard-input* *tutor-socket*)
      )
    (if studentname
	(setq *student-name* studentname)
      (setq *student-name* "Dude"))
    (when verb
      (setq *verbose* 20))
    (when verb2
      (setq *verbose* 99))
    (unless color
      (setq *style* 'ascii))
    (setq *allow-constants* nil)
    (unless *tutor-socket*
      (scunak-header "Welcome to Scutor, the Scunak Tutor."))
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
    (dolist (infofilename infofilenames)
      (unless (probe-file infofilename)
	(setq infofilename (format nil "~d.lisp" infofilename))
	(unless (probe-file infofilename)
	  (fail (format nil "No file named ~d." infofilename))))
      (load infofilename))
    (let ((c (intern claimname)))
      (tutor c)
      (when *tutor-socket*
	(close *tutor-socket*))
      )))

#+:allegro
(defun save-tutor-image ()
  (set-fail-to-seriously-fail)
  (setq excl:*restart-app-function* 'tutor-initfn)
  (excl:dumplisp :name (format nil "~d/allegro-scunak-tutor.dxl" *dxldir*)))

#+:clisp
(defun save-tutor-image ()
  (set-fail-to-seriously-fail)
  (setq system::*driver* #'tutor-initfn)
  (ext:saveinitmem (format nil "~d/clisp-scunak-tutor.mem" *dxldir*) :quiet t :init-function 'tutor-initfn))

#+:cmu
(defun save-tutor-image ()
  (set-fail-to-seriously-fail)
  (extensions:savelisp (format nil "~d/cmucl-scunak-tutor" *dxldir*) :init-function 'tutor-initfn
		       :print-herald nil))

; *tutor-alts* is a list of tutor-alt's
; tutor-alt is (<theta> <tasklist>)
(defun tutor (c)
  (if (get c 'dbtype)
      (progn
	(setq *scip-usable* *sig-granularity-perfect*)
	(setq *scip-gevar* (intern-gensym))
	(setq *scip-gtp* (get c 'dbtype))
	(setf (get *scip-gevar* 'evar) t)
	(setf (get *scip-gevar* 'dbtype) *scip-gtp*) ; ok to assign the type since gtp has no evars
	(setq *tutor-alts-stack* nil)
	(setq *tutor-alts* (list (list (acons *scip-gevar* *scip-gevar* nil) ; theta (initially id)
				       (list (list *scip-gevar* *emptyctx* nil *scip-gtp* nil 'ID))
				       ))) ; plans (first one focused)
	(setq *scip-assnum* -1)
	(setq *scip-factnum* -1)
	(format t "Hello, ~d.  Please try to prove the following:~%~d~%"
		*student-name*
		(output1-type-string *scip-gtp*))
	(tutor-1))
    (format t "~d has no known type.~%" c)))

(defun tutor-claim (newapp)
  (let ((ctxi *input1-ctx-info*)
	(name (if (consp newapp) (car newapp) newapp))
	(expldeps (if (consp newapp) (cdr newapp) nil)))
    (multiple-value-bind
     (argctx failinfo)
     (varlist-to-ctx expldeps ctxi)
     (if failinfo
	 (format t "Did not understand: ~d~%" failinfo)
       (let ((app name))
	 (dolist (e expldeps)
	   (setq app (app app e)))
	 (let ((tp (ctx-extract-type *emptyctx* app)))
	   (if (dtype-returns-pf-p tp)
	       (tutor-tp-1 tp argctx)
	     (format t "Given term does not have a proof type.~%"))))))))

(defun tutor-tp (pre-tp)
  (multiple-value-bind
   (tp info fail)
   (deptype-fill-in-blanks pre-tp *input1-state* (input1-blanks-prefix *input1-ctx-info*))
   (if (or info fail)
       (format t "Sorry, didn't understand that.~%~d~%" (or info fail))
     (tutor-tp-0 tp))))

(defun tutor-tp-0 (tp)
  (tutor-tp-1 tp
	      (mapcar #'(lambda (x)
			  (list (car x)
				(cadr (caadr x))))
		      *input1-ctx-info*)))

(defun tutor-tp-1 (tp namedectx)
  (let* ((names nil)
	 (ctx *emptyctx*)
	 (namesubst 'ID)
	 (dbtp nil))
    (setq *scip-gtp* tp)
    (do ((nec2 namedectx (cdr nec2)))
	((null nec2))
	(setq *scip-gtp* (dpi (cadar nec2)
			      (quick-db-type (caar nec2) 0 *scip-gtp*))))
    (dolist (ne (reverse namedectx))
      (setq ctx (ctx-cons (named-type-to-db-1 names (cadr ne)) ctx))
      (push (car ne) names)
      (setq namesubst (cons (car ne) (cons #'identity namesubst))))
    (setq dbtp (named-type-to-db-1 names tp))
    (setq *scip-usable* *sig-granularity-perfect*)
    (setq *scip-gevar* (intern-gensym))
    (setf (get *scip-gevar* 'evar) t)
    (setf (get *scip-gevar* 'dbtype) *scip-gtp*) ; ok to assign the type since gtp has no evars
    (setq *tutor-alts-stack* nil)
    (setq *tutor-alts* (post-process-tutor-alt
			(list (acons *scip-gevar* *scip-gevar* nil) ; theta (initially id)
			      (list (list *scip-gevar* ctx names dbtp namedectx namesubst))
			      ))) ; plans (first one focused)
    (setq *scip-assnum* -1)
    (setq *scip-factnum* -1)
    (format t "Hello, ~d.  Please try to prove the following:~%~d~%"
	    *student-name*
	    (output1-type-string tp))
    (if *tutor-nl*
	(nl-tutor-1)
      (if *scunak-socket*
	  (tutor-1-sock)
	(tutor-1)))))

(defun tutor-1 ()
  (let* ((grammar input1-grammar)
	 (quit-command nil)
	 (student-done nil)
	 (r nil)
	 (words nil)
	 (n nil)
	 (ch nil)
	 (res nil)
	 )
    (declare (special quit-command student-done))
    (loop while (and *tutor-alts* (not quit-command) (not student-done)) do
	  (format t "~d> " *student-name*)
	  (setq r (read-line))
	  (setq words (tokenize-str r))
	  (setq n (length words))
	  (setq ch (earley-parse-string 'PFCOMMAND r grammar))
	  (setq res (chart-to-parse-trees words 0 n 'PFCOMMAND grammar ch 1 nil 0))
;	  (setq i (interactive-parse *standard-output* 'PFCOMMAND grammar 0
;				     (format nil "~d> " *student-name*)))
;	  (setq *zzz* i)
	  (if res
	      (let ((c (eval (car res)))
		    (prev *tutor-alts*))
		(when (consp c)
		  (apply (car c) (cdr c))
		  )
;		(multiple-value-setq
;		 (grammar failed failinfo)
;		 (process-parsed-input (list (caadr i)) grammar))
		(unless (equal *tutor-alts* prev)
		  (let ((talts *tutor-alts*))
		    (setq *tutor-alts* nil)
		    (dolist (talt talts)
		      (setq *tutor-alts* (append *tutor-alts*
						 (post-process-tutor-alt talt))))))
		)
	    (if (equal (last words) '(#\?))
		(if (eq *tutor-language* 'GERMAN)
		    (format *student-stream* "Das kann ich nicht beantworten, ~d.~%" *student-name*)
		  (format *student-stream* "I cannot answer that, ~d.~%" *student-name*))
	      (if (eq *tutor-language* 'GERMAN)
		  (format *student-stream* "Das ist unvollstaendig oder nicht ganz korrekt.~%")
		(format *student-stream* "I could not understand you, or what you said was not completely correct, ~d.~%" *student-name*)))))
	  ; prepare *tutor-alts* for the next round and check if any of the alternatives are closed
    (if student-done
	(progn
	  (format *student-stream* "Congratulations, you're done with the proof, ~d!~%" *student-name*)
	  (format t "Successful Term:~%~d~%"
		  (output1-normal-string student-done)))
      (progn
	(format *student-stream* "Okay, ~d, goodbye for now.~%" *student-name*)
	))))

(defun tutor-1-sock ()
  (let* ((grammar input1-grammar)
	 (quit-command nil)
	 (student-done nil)
	 (r nil)
	 (words nil)
	 (n nil)
	 (ch nil)
	 (res nil)
	 )
    (declare (special quit-command student-done))
    (loop while (and *tutor-alts* (not quit-command) (not student-done)) do
	  (force-output *standard-output*)
	  (scu-out 'READY-TUTOR)
	  (setq r (read *scunak-socket* nil nil))
	  (unless (and (open-stream-p *scunak-socket*)
		       (open-stream-p *standard-output*))
	    (setq quit-command t)
	    (setq r nil)
	    )
	  (unless (consp r)
	    (setq r (list r)))
	  (let ((prev *tutor-alts*))
	    (multiple-value-bind
	     (ok failinfo)
	     #+:allegro
	     (if *scunak-time-limit*
		 (mp:with-timeout (*scunak-time-limit* (scu-out 'TIMED-OUT) (values nil "Timed Out")) (tutor1l-execute r))
	       (tutor1l-execute r))
	     #-:allegro
	     (tutor1l-execute r)
;	     (unless ok
;	       (format t "Problem: ~d~%" failinfo)
;	       )
	     )
	    (if (equal *tutor-alts* prev)
		(scu-out 'TUTOR-STATUS-UNCHANGED)
	      (let ((talts *tutor-alts*))
		(setq *tutor-alts* nil)
		(dolist (talt talts)
		  (setq *tutor-alts* (append *tutor-alts*
					     (post-process-tutor-alt talt))))))
	    ))
    (if student-done
	(progn
	  (scu-out 'STUDENT-SUCCESSFUL)
	  (scu-out 'EXIT-TUTOR)
	  (format *student-stream* "Congratulations, you're done with the proof, ~d!~%" *student-name*)
	  (format t "Successful Term:~%~d~%"
		  (output1-normal-string student-done)))
      (progn
	(scu-out 'STUDENT-FAILED)
	(scu-out 'EXIT-TUTOR)
	(format *student-stream* "Okay, ~d, goodbye for now.~%" *student-name*)
	))))

; this returns a list of reasons we may have failed
(defun generic-pfcommand (fn)
  (let ((newtutoralts nil)
	(failreasons nil))
    (dolist (d *tutor-alts*)
      (if (cadr d)
	  (multiple-value-bind
	   (nta failreasons1)
	   (funcall fn (car d) (caadr d) (cdadr d))
	   (setq newtutoralts (append nta newtutoralts))
	   (when failreasons1
	     (setq failreasons (append failreasons1 failreasons))))
	(when *tutor-keep-done*
	  (push d newtutoralts))))
    (if *tutor-compute-result*
	(values failreasons newtutoralts)
      (progn
	(push *tutor-alts* *tutor-alts-stack*)
	(setq *tutor-alts* newtutoralts)
	failreasons))))

(defun generic-back-pfcommand (failreasons default &optional incorrect)
  (if incorrect
      (progn
	(scu-out 'NOT-CORRECT)
	(format *main-stream* "Not Correct.~%"))
    (progn
      (scu-out 'NOT-OK)
      (format *main-stream* "Not OK.~%")))
  (if failreasons
      (let ((ra nil)
	    (ma 0))
	(dolist (fr failreasons)
	  (let ((a (assoc fr ra :test #'string=)))
	    (if a
		(setq ma (max ma (incf (cdr a))))
	      (progn
		(setq ma (max ma 1))
		(push (cons fr 1) ra)))))
	(let ((r (find-if #'(lambda (x)
			      (= (cdr x) ma)) ra)))
	  (format *student-stream* "~d~%" (car r))))
    (progn
      (format *student-stream* "~d~%" default)))
  (setq *tutor-alts* (pop *tutor-alts-stack*)))

(defun print-status ()
  (if (= (length *tutor-alts*) 1)
      (format t "1 Alternative~%")
    (format t "~d Alternatives~%" (length *tutor-alts*)))
  (let ((i 0))
    (dolist (a *tutor-alts*)
      (format t "Alternative ~d.~%" (incf i))
      (format t "Current Pf Term:~%~d~%" (output1-normal-string (normalize (cdr (assoc *scip-gevar* (car a))))))
      (if (cadr a)
	  (let* ((task (caadr a))
		 (ctx (cadr task))
		 (names (nth 2 task)))
	    (if (eq (car task) 'DONE)
		(format t "DONE: ~d~%"
			(output1-type-string (nth 3 (caadr a)) names))
	      (let ((strl nil))
		(when ctx
		  (format t "Support:~%")
		  (do ((names2 names (cdr names2))
		       (ectx2 ctx (cdr ectx2)))
		      ((or (null names2) (null ectx2)))
		      (push (format nil "~d:~d" (car names2) (output1-type-string (car ectx2) (cdr names2))) strl))
		  (dolist (s strl) (format t "~d~%" s)))
		(format t "Goal: ~d~%"
			(output1-type-string (nth 3 (caadr a)) names))))
	    (when (cdadr a)
	      (format t "Delayed Subgoals in Alternative ~d.~%" i)
	      (let ((j 0))
		(dolist (task (cdadr a))
		  (if (eq (car task) 'DONE)
		      (format t "~d) (DONE) ~d ~d~%" (incf j) (nth 2 task) (output1-type-string (nth 3 task) (nth 2 task)))
		    (format t "~d) ~d ~d~%" (incf j) (nth 2 task) (output1-type-string (nth 3 task) (nth 2 task))))))))
	(progn
	  (format t "Complete Proof~%")))))
  t)

(defun quit-pfcommand ()
  (declare (special quit-command))
  (setq quit-command t)
  t)

(defun undo-pfcommand ()
  (when *tutor-alts-stack*
    (setq *tutor-alts* (pop *tutor-alts-stack*)))
  t)

(defun pop-done-alts (theta delayed)
  (let ((newalts (list (list theta delayed))))
    (loop while (and delayed (eq (caar delayed) 'DONE)) do
	  (pop delayed)
	  (push (list theta delayed) newalts))
    newalts))

(defun qed-pfcommand ()
  (declare (special student-done))
  (check-student-done)
  (unless student-done
    (multiple-value-bind
     (failreasons newtutalts) ; actually unused in qed-pfcommand (for now?)
     (generic-pfcommand
      #'(lambda (theta task delayed)
	  (unless (dpi-p (nth 3 task)) ; only check atomic types (otherwise it's buggy)
	    (if (eq (car task) 'DONE)
		(pop-done-alts theta delayed)
	      (multiple-value-bind
	       (succ theta1)
	       (task-done task theta nil)
	       (if succ
		   (pop-done-alts theta1 delayed)
		 (progn
		   (setq *scip-usable* *sig-granularity-toolow*)
		   (multiple-value-bind
		    (succ theta1)
		    (task-done task theta nil)
		    (setq *scip-usable* *sig-granularity-perfect*)
		    (if succ
			(pop-done-alts theta1 delayed)
		      (progn
			(diagnosis-out 'NOT-YET-DONE)
			nil)))))))))))
    (check-student-done)
    (unless student-done
      (if *tutor-alts*
	  (progn
	    (scu-out 'OK)
	    (format *main-stream* "OK~%")
	    (format *student-stream* "Good ~d, you're done with this part of the proof, but there is more to do.~%" *student-name*)
	    )
	(progn
	  (scu-out 'NOT-OK)
	  (format *main-stream* "Not OK~%")
	  (format *student-stream* "You don't seem to actually be done with anything, ~d.~%" *student-name*)
	  (setq *tutor-alts* (pop *tutor-alts-stack*))))))
  t)

(defun check-student-done ()
  (declare (special student-done))
  (let ((tal nil))
    (dolist (d *tutor-alts*)
      (if (cadr d)
	  (push d tal)
	(unless student-done
	  (setq student-done (normalize (cdr (assoc *scip-gevar* (car d)))))
	  (when (or (free-evars student-done) (not (ctx-term-type-p *emptyctx* student-done *scip-gtp*)))
	    (setq student-done nil))))) ; this should be sanity checking, but in case of bugs, better to safely throw away ill-typed or open terms if there are no more open goals
    (setq *tutor-alts* (reverse tal))
    student-done))
    

(defun claim-pfcommand ()
  t
  )

(defun let-pfcommand (xl &optional (pre-dtp nil))
  (let ((reps nil))
    (do ((xl2 xl (cdr xl2)))
	((null xl2))
      (when (and (member (car xl2) (cdr xl2))
		 (not (member (car xl2) reps)))
	(push (car xl2) reps)))
    (if reps
	(if *tutor-compute-result*
	    (values nil 
		    (if (cdr reps)
			(format nil "~d, you tried to declare some variables (eg, ~d) more than once."
				*student-name* (car reps))
		      (format nil "~d, you tried to declare ~d more than once."
			      *student-name* (car reps))))
	  (if (cdr reps)
	      (format *student-stream* "~d, you tried to declare some variables (eg, ~d) more than once.~%"
		      *student-name* (car reps))
	    (format *student-stream* "~d, you tried to declare ~d more than once.~%"
		    *student-name* (car reps))))
      (multiple-value-bind
       (failreasons newtutalts)
       (generic-pfcommand
	#'(lambda (theta task delayed)
	    (multiple-value-bind
	     (evar ctx names tp namedectx namesubst)
	     (task-components task)
	     (unless (eq evar 'DONE)
	     (let ((dup (intersection (mapcar #'car namedectx) xl)))
	       (if dup
		   (values nil (list (format nil "~d is already a declared variable in context." (car dup))))
		 (let ((dtp (obj))
		       (info nil)
		       (fail nil))
		   (when pre-dtp
		     (multiple-value-setq
		      (dtp info fail)
		      (deptype-fill-in-blanks pre-dtp *input1-state* namedectx)))
		   (let ((newvars (remove-duplicates
				   (mapcar #'(lambda (x)
					       (list (cadr x) (caddr x)))
					   (remove-if-not #'(lambda (x) (equal (car x) 'NEWVAR)) info))
				   :test #'equal))
			 (info2 (remove-if #'(lambda (x) (equal (car x) 'NEWVAR)) info)))
		     (if (or fail info2)
			 (progn
			   (diagnosis-out (list 'ILL-FORMED-TYPE info2))
			   (values nil (list "The type you gave for the declared variables was ill-formed.")))
		       (let ((newvars1 newvars))
			 (when *tutor-autoset-sig* (tutor-increase-rules dtp))
			 (if (dpi-p tp)
			     (multiple-value-bind
			      (newalts1 failreasons1)
			      (let-pfcommand-newvars newvars1 xl dtp evar ctx names tp namedectx namesubst theta
						     delayed
						     delayed)
			      (if (cdr newvars1)
				  (multiple-value-bind
				   (newalts2 failreasons2)
				   (let-pfcommand-newvars (reverse newvars1) xl dtp evar ctx names tp namedectx namesubst theta
							  delayed
							  delayed)
				   (values (append newalts1 newalts2)
					   (append failreasons1 failreasons2)))
				(values newalts1 failreasons1)))
			   (let ((back1 (quick-fill-gap ctx tp *scip-usable* nil 2))
				 (failreasons nil)
				 (newalts nil))
			     (dolist (y back1)
			       (let* ((tmp (car y))
				      (newevars (cadr y))
				      (newtasks
				       (mapcar #'(lambda (new)
						   (let ((dtp (cdr new)))
						     (setf (get (car new) 'dbtype) (cdr new)) ; global type, so OK
						     (dotimes (j (length ctx))
						       (when (dpi-p dtp)
							 (setq dtp (dpi-cod dtp))))
						     (list (car new) ctx names dtp
							   namedectx namesubst
							   )))
					       newevars)))
				 (dolist (newtask newtasks) ; the number of new tasks are 0, 1 or 2, so this gives all possible 'orderings' of the tasks
				   (multiple-value-bind
				    (evar1 ctx1 names1 tp1 namedectx1 namesubst1)
				    (task-components newtask)
				    (when (dpi-p tp1)
				      (multiple-value-bind
				       (newalts1 failreasons1)
				       (let-pfcommand-newvars newvars1 xl dtp
							      evar1 ctx1 names1 tp1
							      namedectx1 namesubst1
							      (compose-theta-1 evar tmp theta)
							      (append (remove newtask newtasks)
								      (if (pf-p tp)
									  (cons (list 'DONE ctx names tp namedectx namesubst)
										delayed)
									delayed))
							      (append (remove newtask newtasks)
								      delayed))
				       (setq newalts (append newalts1 newalts))
				       (setq failreasons (append failreasons1 failreasons)))
				    (when (cdr newvars1)
				      (multiple-value-bind
				       (newalts1 failreasons1)
				       (let-pfcommand-newvars (reverse newvars1) xl dtp
							      evar1 ctx1 names1 tp1
							      namedectx1 namesubst1
							      (compose-theta-1 evar tmp theta)
							      (append (remove newtask newtasks)
								      (if (pf-p tp)
									  (cons (list 'DONE ctx names tp namedectx namesubst)
										delayed)
									delayed))
							      (append (remove newtask newtasks)
								      delayed))
				       (setq newalts (append newalts1 newalts))
				       (setq failreasons (append failreasons1 failreasons))))
				    )))))
			     (values newalts failreasons)))))))))))))
       (if *tutor-compute-result*
	   (values newtutalts
		   (or failreasons
		       (list
			(if (cdr xl)
			    (format nil "I could not find any reason for you to declare such variables, ~d."
				    *student-name*)
			  (format nil "I could not find any reason for you to declare such a variable, ~d."
				  *student-name*)))))
	 (if *tutor-alts*
	     (progn
	       (scu-out 'OK)
	       (format *main-stream* "OK~%"))
	   (generic-back-pfcommand
	    failreasons
	    (if (cdr xl)
		(format nil "I could not find any reason for you to declare such variables, ~d."
			*student-name*)
	      (format nil "I could not find any reason for you to declare such a variable, ~d."
		      *student-name*)))))))))

(defun let-pfcommand-newvars (newvars xl dtp evar ctx names tp namedectx namesubst theta delayed delayed2)
  (if newvars
      (if (dpi-p tp)
	  (if (ctx-types-eq ctx (dpi-dom tp) (named-type-to-db-1 (mapcar #'car namedectx) (cadar newvars)))
	      (let ((ctx2 (ctx-cons (dpi-dom tp) ctx)))
		(setf (get (caar newvars) 'bvar) t)
		(setf (get (caar newvars) 'dbtype) (dpi-dom tp))
		(let-pfcommand-newvars
		 (cdr newvars) xl dtp
		 evar ctx2 (cons (caar newvars) names) (dpi-cod tp)
		 (cons (list (caar newvars)
			     (dbsubst-type (dpi-dom tp) #'identity namesubst))
		       namedectx)
		 (cons (caar newvars) (cons #'identity namesubst))
		 theta
		 delayed delayed2))
	    nil)
	nil)
    (let-pfcommand-newvars-2 xl dtp evar ctx names tp namedectx namesubst theta delayed delayed2)))

(defun let-pfcommand-newvars-2 (xl dtp evar ctx names tp namedectx namesubst theta delayed delayed2)
  (if xl
      (if (dpi-p tp)
	  (if (ctx-types-eq ctx (dpi-dom tp) (named-type-to-db-1 (mapcar #'car namedectx) dtp))
	      (let ((ctx2 (ctx-cons (dpi-dom tp) ctx)))
		(setf (get (car xl) 'bvar) t)
		(setf (get (car xl) 'dbtype) (dpi-dom tp))
		(let-pfcommand-newvars-2
		 (cdr xl) dtp
		 evar ctx2 (cons (car xl) names) (dpi-cod tp)
		 (cons (list (car xl)
			     (dbsubst-type (dpi-dom tp) #'identity namesubst))
		       namedectx)
		 (cons (car xl) (cons #'identity namesubst))
		 theta
		 delayed delayed2))
	    (if (dtype-returns-pf-p (dpi-dom tp))
		(if (pf-p (dpi-dom tp))
		    (progn
		      (diagnosis-out (list 'SHOULD-ASSUME (dbsubst (pf-prop (dpi-dom tp)) #'identity namesubst)))
		      nil)
		  nil) ; shouldn't happen actually (due to order restrictions)
	      (progn
		(diagnosis-out (list 'BAD-TYPE-FOR (car xl)))
		(diagnosis-out (list 'SHOULD-LET (dbsubst-type (dpi-dom tp) #'identity namesubst)))
		(values nil (list (format nil "The type you gave for ~d does not seem to be correct." (car xl)))))))
	(progn
	  (diagnosis 'NO-REASON-TO-LET)
	  nil))
    (if (equal delayed delayed2)
	(list (list theta (cons (list evar ctx names tp namedectx namesubst) delayed)))
      (list (list theta (cons (list evar ctx names tp namedectx namesubst) delayed))
	    (list theta (cons (list evar ctx names tp namedectx namesubst) delayed2))
	    ))))

(defun assume-pfcommand (pre-prop)
  (multiple-value-bind
   (failreasons newtutalts)
   (generic-pfcommand
    #'(lambda (theta task delayed)
	(multiple-value-bind
	 (evar ctx names tp namedectx namesubst)
	 (task-components task)
	 (unless (eq evar 'DONE)
	 (multiple-value-bind
	  (prop dtp info fail)
	  (if (consp pre-prop)
	      (app-fill-in-blanks-0 (car pre-prop) (cdr pre-prop) (prop) *input1-state* namedectx t)
	    (app-fill-in-blanks-0 pre-prop nil (prop) *input1-state* namedectx t))
	  (let ((newvars (remove-duplicates
			  (mapcar #'(lambda (x)
				      (list (cadr x) (caddr x)))
				  (remove-if-not #'(lambda (x) (equal (car x) 'NEWVAR)) info))
			  :test #'equal))
		(info2 (remove-if #'(lambda (x) (equal (car x) 'NEWVAR)) info)))
	    (if (or fail info2)
		(progn
		  (diagnosis (list 'ILL-FORMED-ASSUMPTION info2))
		  (values nil (list "The assumption you gave was ill-formed.")))
	      (progn
		(when *tutor-autoset-sig* (tutor-increase-rules (pf prop)))
		(if (dpi-p tp)
		    (multiple-value-bind
		     (newalts1 failreasons1)
		     (assume-pfcommand-newvars newvars prop evar ctx names tp namedectx namesubst theta
					       delayed
					       delayed)
		     (if (cdr newvars) ; if more than one, try reversing (but not all permutations)
			 (multiple-value-bind
			  (newalts2 failreasons2)
			  (assume-pfcommand-newvars (reverse newvars) prop evar ctx names tp namedectx namesubst theta
						    delayed
						    delayed)
			  (values (append newalts1 newalts2) (append failreasons1 failreasons2)))
		       (values newalts1 failreasons1)))
		  (let ((back1 (quick-fill-gap ctx tp *scip-usable* nil
					; we never want more than 2 delayed tasks [varied by *tutor-max-tasks*]...
					; and we never want to introduce more than 1 delayed task in 1 step
					       (min 2 (- *tutor-max-tasks* (length delayed)))
					       ))
			(failreasons nil)
			(newalts nil))
		    (dolist (y back1)
		      (let* ((tmp (car y))
			     (newevars (cadr y))
			     (newtasks
			      (mapcar #'(lambda (new)
					  (let ((dtp (cdr new)))
					    (setf (get (car new) 'dbtype) (cdr new)) ; global type, so OK
					    (dotimes (j (length ctx))
					      (when (dpi-p dtp)
						(setq dtp (dpi-cod dtp))))
					    (list (car new) ctx names dtp
						  namedectx namesubst
						  )))
				      newevars)))
			(dolist (newtask newtasks) ; the number of new tasks are 0, 1 or 2, so this gives all possible 'orderings' of the tasks
			  (multiple-value-bind
			   (evar1 ctx1 names1 tp1 namedectx1 namesubst1)
			   (task-components newtask)
			   (when (dpi-p tp1)
			     (multiple-value-bind
			      (newalts1 failreasons1)
			      (assume-pfcommand-newvars newvars prop
							evar1 ctx1 names1 tp1
							namedectx1 namesubst1
							(compose-theta-1 evar tmp theta)
							(append (remove newtask newtasks)
								(if (pf-p tp)
								    (cons (list 'DONE ctx names tp namedectx namesubst)
									  delayed)
								  delayed))
							(append (remove newtask newtasks)
								delayed))
			      (setq newalts (append newalts1 newalts))
			      (setq failreasons (append failreasons1 failreasons)))
			     (when (cdr newvars)
			       (multiple-value-bind
				(newalts1 failreasons1)
				(assume-pfcommand-newvars (reverse newvars) prop
							  evar1 ctx1 names1 tp1
							  namedectx1 namesubst1
							  (compose-theta-1 evar tmp theta)
							  (append (remove newtask newtasks)
								  (if (pf-p tp)
								      (cons (list 'DONE ctx names tp namedectx namesubst)
									    delayed)
								    delayed))
							  (append (remove newtask newtasks)
								  delayed))
				(setq newalts (append newalts1 newalts))
				(setq failreasons (append failreasons1 failreasons))))
			     )))))
		    (values newalts failreasons)))))))))))
   (if *tutor-compute-result*
       (values newtutalts
	       (or failreasons
		   (list
		    (format nil "I could not find any reason for you to make such an assumption, ~d."
			    *student-name*))))
     (if *tutor-alts*
	 (progn
	   (scu-out 'OK)
	   (format *main-stream* "OK~%"))
       (generic-back-pfcommand
	failreasons
	(format nil "I could not find any reason for you to make such an assumption, ~d."
		*student-name*))))))

(defun assume-pfcommand-newvars (newvars prop evar ctx names tp namedectx namesubst theta delayed delayed2)
  (if newvars
      (if (dpi-p tp)
	  (if (ctx-types-eq ctx (dpi-dom tp) (named-type-to-db-1 (mapcar #'car namedectx) (cadar newvars)))
	      (let ((ctx2 (ctx-cons (dpi-dom tp) ctx)))
		(setf (get (caar newvars) 'bvar) t)
		(setf (get (caar newvars) 'dbtype) (dpi-dom tp))
		(assume-pfcommand-newvars
		 (cdr newvars) prop
		 evar ctx2 (cons (caar newvars) names) (dpi-cod tp)
		 (cons (list (caar newvars)
			     (dbsubst-type (dpi-dom tp) #'identity namesubst))
		       namedectx)
		 (cons (caar newvars) (cons #'identity namesubst))
		 theta
		 delayed delayed2))
	    nil)
	nil)
    (if (dpi-p tp)
	(let ((prop (named-term-to-db-1 (mapcar #'car namedectx) prop)))
	  (if (ctx-types-eq ctx (dpi-dom tp) (pf prop))
	      (let ((ctx2 (ctx-cons (dpi-dom tp) ctx))
		    (name (intern (format nil "ass~d" (incf *scip-assnum*)))))
		(setf (get name 'bvar) t)
		(setf (get name 'dbtype) (pf prop))
		(if (equal delayed delayed2)
		    (list (list theta (cons (list evar ctx2 (cons name names) (dpi-cod tp)
						  (cons (list name (dbsubst-type (dpi-dom tp) #'identity namesubst))
							namedectx)
						  (cons name (cons #'identity namesubst)))
					    delayed)))
		  (list (list theta (cons (list evar ctx2 (cons name names) (dpi-cod tp)
						(cons (list name (dbsubst-type (dpi-dom tp) #'identity namesubst))
						      namedectx)
						(cons name (cons #'identity namesubst)))
					  delayed))
			(list theta (cons (list evar ctx2 (cons name names) (dpi-cod tp)
						(cons (list name (dbsubst-type (dpi-dom tp) #'identity namesubst))
						      namedectx)
						(cons name (cons #'identity namesubst)))
					  delayed2))
			)))
	    (if (pf-p (dpi-dom tp))
		(progn
		  (diagnosis-out (list 'SHOULD-ASSUME (dbsubst (pf-prop (dpi-dom tp)) #'identity namesubst)))
		  nil)
	      (progn
		(diagnosis-out (list 'SHOULD-LET (dbsubst-type (dpi-dom tp) #'identity namesubst)))
		nil))))
      (progn
	(diagnosis 'NO-REASON-TO-MAKE-AN-ASSUMPTION)
	nil))))

(defun subgoal-pfcommand (pre-prop &optional (allownewgaps t))
  (multiple-value-bind
   (failreasons newtutalts)
   (generic-pfcommand
    #'(lambda (theta task delayed)
	(multiple-value-bind
	 (evar ctx names tp namedectx namesubst)
	 (task-components task)
	 (if (or (dpi-p tp) (eq evar 'DONE)) ; assume atomic
	     (values nil (list "It is not clear what you are trying to prove."))
	   (multiple-value-bind
	    (prop info fail)
	    (normal-fill-in-blanks pre-prop (prop) *input1-state* namedectx)
	    (if fail
		(progn
		  (diagnosis-out (list 'ILL-FORMED-PROP info))
		  (values nil (list fail)))
	      (if info
		  (progn
		    (diagnosis-out (list 'ILL-FORMED-PROP info))
		    (values nil (list "The proposition you gave was ill-formed.")))
		(let ((newtp (pf (named-term-to-db-1 (mapcar #'car namedectx) prop))))
		  (when *tutor-autoset-sig* (tutor-increase-rules newtp))
		  (multiple-value-bind
		   (succ1 tasklist1 theta1)
		   (task-willshow newtp task delayed theta)
		   (if succ1
		       (values (list (list theta1 (cons (car tasklist1)
							(cons (list 'DONE ctx names tp namedectx namesubst)
							      (cdr tasklist1))))
				     (list theta1 tasklist1)
				     )
			       nil)
		     (progn
		       (diagnosis-out 'INSUFFICIENT-TO-JUSTIFY-GOAL)
		       (values nil (list "The proposition you gave is insufficient to justify the goal.")))))))))))))
   (if *tutor-alts*
       (if *tutor-compute-result*
	   (values newtutalts failreasons)
	 (progn
	   (scu-out 'OK)
	   (format *main-stream* "OK~%")))
      ; otherwise the student may want to show some subgoal and leave others open
     (if allownewgaps
	 (progn
	   (setq *tutor-alts* (pop *tutor-alts-stack*))
	   (multiple-value-bind
	    (failreasons2 newtutalts2)
	    (generic-pfcommand
	     #'(lambda (theta task delayed)
		 (multiple-value-bind
		  (evar ctx names tp namedectx namesubst)
		  (task-components task)
		  (if (dpi-p tp)
		      (values nil (list "It is not clear what you are trying to prove."))
		    (multiple-value-bind
		     (prop info fail)
		     (normal-fill-in-blanks pre-prop (prop) *input1-state* namedectx)
		     (if fail
			 (progn
			   (diagnosis-out (list 'ILL-FORMED-PROP info))
			   (values nil (list fail)))
		       (if info
			   (progn
			     (diagnosis-out (list 'ILL-FORMED-PROP info))
			     (values nil (list "The proposition you gave was ill-formed.")))
			 (let ((newtp (pf (named-term-to-db-1 (mapcar #'car namedectx) prop))))
			   (multiple-value-bind
			    (tasklist1 theta1)
			    (task-claim newtp task delayed theta)
			    (let* ((task1 (car tasklist1))
				   (delayed1 (cdr tasklist1)))
			      (multiple-value-bind
			       (evar1 ctx1 names1 tp1 namedectx1 namesubst1)
			       (task-components task1)
			       (let ((back1 (quick-fill-gap ctx1 tp1 *scip-usable* nil
					; we never want more than 2 delayed tasks [varied by *tutor-max-tasks*]...
					; and we never want to introduce more than 1 delayed task in 1 step
							    (min 2 (- *tutor-max-tasks* (length delayed1)))
							    t))
				     (failreasons nil)
				     (newalts nil))
				 (dolist (y back1)
				   (let* ((tmp (car y))
					  (newevars (cadr y))
					  (newtasks
					   (mapcar #'(lambda (new)
						       (let ((dtp (cdr new)))
							 (setf (get (car new) 'dbtype) (cdr new)) ; global type, so OK
							 (dotimes (j (length ctx1))
							   (when (dpi-p dtp)
							     (setq dtp (dpi-cod dtp))))
							 (list (car new) ctx1 names1 dtp
							       namedectx1 namesubst1
							       )))
						   newevars)))
				     (dolist (newtask newtasks) ; the number of new tasks are 0, 1 or 2, so this gives all possible 'orderings' of the tasks
				       (multiple-value-bind
					(evar11 ctx11 names11 tp11 namedectx11 namesubst11)
					(task-components newtask)
					(push (list (compose-theta-1 evar1 tmp theta1)
						    (cons (car delayed1)
							  (cons newtask
								(append (remove newtask newtasks)
									(cdr delayed1)))))
					      newalts)))))
				 (values newalts failreasons)))))))))))))
	    (if *tutor-compute-result*
		(values newtutalts2 (or (append failreasons failreasons2)
					(list (format nil "The proposition you gave is insufficient to justify the goal."))))
	      (if *tutor-alts*
;		  (format *main-stream* "Correct (with new delayed subgoals)~%")
		  (progn
		    (scu-out 'OK)
		    (format *main-stream* "OK~%"))
		(generic-back-pfcommand
		 (append failreasons failreasons2)
		 (format nil "The proposition you gave is insufficient to justify the goal.")
		 nil)))))
       (if *tutor-compute-result*
	   (values nil (or failreasons
			   (list (format nil "The proposition you gave is insufficient to justify the goal."))))
	 (generic-back-pfcommand
	  failreasons
	  (format nil "The proposition you gave is insufficient to justify the goal.")
	  nil))))))

(defun since-pfcommand (pre-conds pre-prop)
  (multiple-value-bind
   (failreasons newtutalts)
   (generic-pfcommand
    #'(lambda (theta task delayed)
	(multiple-value-bind
	 (evar ctx names tp namedectx namesubst)
	 (task-components task)
	 (if (dpi-p tp) ; assume atomic
	     (values nil (list "It is not clear what you are trying to prove."))
	   (let ((conds nil)
		 (fail nil))
	     (dolist (pc pre-conds)
	       (unless fail
		 (multiple-value-bind
		  (c info fail2)
		  (normal-fill-in-blanks pc (prop) *input1-state* namedectx)
		  (if (or info fail2)
		      (setq fail (or fail2 (if (cdr pre-conds) "The preconditions were ill-formed." "The precondition was ill-formed.")))
		    (push c conds)))))
	     (if fail
		 (values nil (list fail))
	       (progn
		 (setq conds (reverse conds))
	 (multiple-value-bind
	    (prop info fail)
	    (normal-fill-in-blanks pre-prop (prop) *input1-state* namedectx)
	    (if fail
		(values nil (list fail))
	      (if info
		  (values nil (list "The proposition you gave was ill-formed."))
		(let* ((newtp (pf (named-term-to-db-1 (mapcar #'car namedectx) prop)))
		       (newalts nil)
		       (failvals nil))
		  (dolist (c conds)
		    (unless fail
		      (let ((ctp (pf (named-term-to-db-1 (mapcar #'car namedectx) c))))
			(multiple-value-bind
			 (succ1 tasklist1 theta1)
			 (task-fact ctp task delayed theta)
			 (if succ1
			     (progn
			       (setq task (car tasklist1))
			       (setq delayed (cdr tasklist1))
			       (setq theta theta1))
			   (if (eq *tutor-language* 'GERMAN)
			       (setq fail (if (cdr pre-conds) "A precondition is not ganz klar." "The precondition is not ganz klar."))
			     (setq fail (if (cdr pre-conds) "A precondition is not clear." "The precondition is not clear."))))))))
		  (if fail
		      (values nil (list fail))
		    (progn
		  (when *tutor-autoset-sig* (tutor-increase-rules newtp))
		  (if (eq evar 'DONE)
		      (if (ctx-types-eq ctx tp newtp)
			  (values (list (list theta delayed)) nil)
			(values nil (list (format nil "We have not shown that."))))
		    (progn
;		  (when (supertype-of-pf-term-p *emptyctx* (normalize (cdr (assoc *scip-gevar* theta))) *scip-gtp* nil newtp (length ctx)) ; done
;		    (push (list theta (cons task delayed)) newalts) ; already done the thing, no change
;		    )
;		  (when (supertype-of-pf-term-p *emptyctx* (normalize (cdr (assoc *scip-gevar* theta))) *scip-gtp* evar newtp (length ctx))
;		    (multiple-value-bind
;		     (succ theta1)
;		     (task-done task theta nil)
;		     (when succ
;		       (push (list theta1 delayed) newalts))))
		      (let ((in-set-fragment (tutor-in-set-fragment-p (mapcar #'cadr namedectx) prop)))
		  (if (and in-set-fragment
			   (mls*-tableau (remove-if #'null (mapcar #'(lambda (x)
								       (if (pf-p (cadr x))
									   (pf-prop (cadr x))
									 nil))
								   namedectx))
					 (list prop)))
		      (if newalts
			  (values newalts failvals)
			(values nil (list (format nil "I'm afraid that doesn't follow, ~d." *student-name*))))
		    (progn
		      (setq *scip-usable* *sig-granularity-toolow*)
		      (multiple-value-bind
		       (succ1 tasklist1 theta1)
		       (if *tutor-check-low-granularity*
			   (task-hence newtp task delayed theta)
			 nil)
		       (setq *scip-usable* *sig-granularity-perfect*)
		       (if succ1
			   (if newalts
			       (values newalts failvals)
			     (values nil (list (format nil "That step is too trivial."))))
			 (multiple-value-bind
			  (succ1 tasklist1 theta1)
			  (task-hence newtp task delayed theta)
			  (if succ1
			      (values (cons (list theta1 tasklist1) newalts) failvals)
			    (if newalts
				(values newalts failvals)
			      (progn
				(setq *scip-usable* *sig-irrelevant*)
				(multiple-value-bind
				 (succ1 tasklist1 theta1)
				 (task-hence newtp task delayed theta)
				 (setq *scip-usable* *sig-granularity-perfect*)
				 (if succ1
				     (values nil (list (format nil "That step is true, but irrelevant.")))
				   (progn
				     (setq *scip-usable* *sig-granularity-toohigh*)
				     (multiple-value-bind
				      (succ1 tasklist1 theta1)
				      (if in-set-fragment
					  t ; already know it's true in this case
					(task-hence newtp task delayed theta))
				      (setq *scip-usable* *sig-granularity-perfect*)
				      (if succ1
					  (values nil (list (format nil "How does that follow, ~d?  Try using smaller steps." *student-name*)))
					(values nil (list (format nil "I am not sure that statement follows, ~d." *student-name*))))))))))))))))))))))))))))))))
   (if *tutor-compute-result*
       (values newtutalts
	       (or failreasons
		   (list 
		    (format nil "I am not sure that statement follows, ~d." *student-name*))))
     (if *tutor-alts*
	 (progn
	   (scu-out 'OK)
	   (format *main-stream* "OK~%"))
       (generic-back-pfcommand
	failreasons
	(format nil "I am not sure that statement follows, ~d." *student-name*)
	nil)))))

(defun hence-pfcommand (pre-prop)
  (multiple-value-bind
   (failreasons newtutalts)
   (generic-pfcommand
    #'(lambda (theta task delayed)
	(multiple-value-bind
	 (evar ctx names tp namedectx namesubst)
	 (task-components task)
	 (if (dpi-p tp) ; assume atomic
	     (if (pf-p (dpi-dom tp))
		 (progn
		   (diagnosis-out (list 'SHOULD-ASSUME (dbsubst (pf-prop (dpi-dom tp)) #'identity namesubst)))
		   (values nil (list "It is not clear what you are trying to prove.")))
	       (progn
		 (diagnosis-out (list 'SHOULD-LET (dbsubst-type (dpi-dom tp) #'identity namesubst)))
		 (values nil (list "It is not clear what you are trying to prove."))))
	   (multiple-value-bind
	    (prop info fail)
	    (normal-fill-in-blanks pre-prop (prop) *input1-state* namedectx)
	    (if fail
		(progn
		  (diagnosis-out (list 'ILL-FORMED-PROP info))
		  (values nil (list fail)))
	      (if info
		  (progn
		    (diagnosis-out (list 'ILL-FORMED-PROP info))
		    (values nil (list "The proposition you gave was ill-formed.")))
		(let* ((newtp (pf (named-term-to-db-1 (mapcar #'car namedectx) prop)))
		       (newalts nil)
		       (failvals nil))
		  (when *tutor-autoset-sig* (tutor-increase-rules newtp))
		  (if (eq evar 'DONE)
		      (if (ctx-types-eq ctx tp newtp)
			  (values (list (list theta delayed)) nil)
			(progn
			  (when (pf-p tp) ; should always happen
			    (diagnosis-out (list 'EXPECTED-CONCLUSION (dbsubst (pf-prop tp) #'identity namesubst))))
			  (values nil (list (format nil "We have not shown that.")))))
		    (progn
;		  (when (supertype-of-pf-term-p *emptyctx* (normalize (cdr (assoc *scip-gevar* theta))) *scip-gtp* nil newtp (length ctx)) ; done
;		    (push (list theta (cons task delayed)) newalts) ; already done the thing, no change
;		    )
;		  (when (supertype-of-pf-term-p *emptyctx* (normalize (cdr (assoc *scip-gevar* theta))) *scip-gtp* evar newtp (length ctx))
;		    (multiple-value-bind
;		     (succ theta1)
;		     (task-done task theta nil)
;		     (when succ
;		       (push (list theta1 delayed) newalts))))
		      (let ((in-set-fragment (tutor-in-set-fragment-p (mapcar #'cadr namedectx) prop)))
		  (if (and in-set-fragment
			   (mls*-tableau (remove-if #'null (mapcar #'(lambda (x)
								       (if (pf-p (cadr x))
									   (pf-prop (cadr x))
									 nil))
								   namedectx))
					 (list prop)))
		      (if newalts
			  (values newalts failvals)
			(progn
			  (diagnosis-out 'UNTRUE-CONCLUSION)
			  (values nil (list (format nil "I'm afraid that doesn't follow, ~d." *student-name*)))))
		    (progn
		      (setq *scip-usable* *sig-granularity-toolow*)
		      (multiple-value-bind
		       (succ1 tasklist1 theta1)
		       (if *tutor-check-low-granularity*
			   (task-hence newtp task delayed theta)
			 nil)
		       (setq *scip-usable* *sig-granularity-perfect*)
		       (if succ1
			   (if newalts
			       (values newalts failvals)
			     (progn
			       (diagnosis-out 'STEP-TOO-SMALL)
			       (values nil (list (format nil "That step is too trivial." *student-name*)))))
			 (multiple-value-bind
			  (succ1 tasklist1 theta1)
			  (task-hence newtp task delayed theta)
			  (if succ1
			      (values (cons (list theta1 tasklist1) newalts) failvals)
			    (if newalts
				(values newalts failvals)
			      (progn
				(setq *scip-usable* *sig-irrelevant*)
				(multiple-value-bind
				 (succ1 tasklist1 theta1)
				 (task-hence newtp task delayed theta)
				 (setq *scip-usable* *sig-granularity-perfect*)
				 (if succ1
				     (progn
				       (diagnosis-out 'STEP-IRRELEVANT)
				       (values nil (list (format nil "That step is true, but irrelevant." *student-name*))))
				   (progn
				     (setq *scip-usable* *sig-granularity-toohigh*)
				     (multiple-value-bind
				      (succ1 tasklist1 theta1)
				      (if in-set-fragment
					  t ; already know it's true in this case
					(task-hence newtp task delayed theta))
				      (setq *scip-usable* *sig-granularity-perfect*)
				      (if succ1
					  (progn
					    (diagnosis-out 'STEP-TOO-BIG)
					    (values nil (list (format nil "How does that follow, ~d?  Try using smaller steps." *student-name*))))
					(progn
					  (diagnosis-out 'STEP-UNJUSTIFIED)
					  (values nil (list (format nil "I am not sure that statement follows, ~d." *student-name*))))))))))))))))))))))))))))
   (if *tutor-compute-result*
       (values newtutalts
	       (or failreasons
		   (list 
		    (format nil "I am not sure that statement follows, ~d." *student-name*))))
     (if *tutor-alts*
	 (progn
	   (scu-out 'OK)
	   (format *main-stream* "OK~%"))
       (generic-back-pfcommand
	failreasons
	(format nil "I am not sure that statement follows, ~d." *student-name*)
	nil)))))

(defun clearly-pfcommand (pre-prop)
  (multiple-value-bind
   (failreasons newtutalts)
   (generic-pfcommand
    #'(lambda (theta task delayed)
	(multiple-value-bind
	 (evar ctx names tp namedectx namesubst)
	 (task-components task)
	 (if (dpi-p tp) ; assume atomic
	     (if (pf-p (dpi-dom tp))
		 (progn
		   (diagnosis-out (list 'SHOULD-ASSUME (dbsubst (pf-prop (dpi-dom tp)) #'identity namesubst)))
		   (values nil (list "It is not clear what you are trying to prove.")))
	       (progn
		 (diagnosis-out (list 'SHOULD-LET (dbsubst-type (dpi-dom tp) #'identity namesubst)))
		 (values nil (list "It is not clear what you are trying to prove."))))
	   (multiple-value-bind
	    (prop info fail)
	    (normal-fill-in-blanks pre-prop (prop) *input1-state* namedectx)
	    (if fail
		(progn
		  (diagnosis-out (list 'ILL-FORMED-PROP info))
		  (values nil (list fail)))
	      (if info
		  (progn
		    (diagnosis-out (list 'ILL-FORMED-PROP info))
		    (values nil (list "The proposition you gave was ill-formed.")))
		(let ((newtp (pf (named-term-to-db-1 (mapcar #'car namedectx) prop)))
		      (newalts nil)
		      (failvals nil))
		  (when *tutor-autoset-sig* (tutor-increase-rules newtp))
;		  (when (supertype-of-pf-term-p *emptyctx* (normalize (cdr (assoc *scip-gevar* theta))) *scip-gtp* nil newtp (length ctx)) ; done
;		    (setq newalts (list (list theta (cons task delayed))))) ; already done the thing, no change
		  (if (eq evar 'DONE)
		      (if (ctx-types-eq ctx tp newtp)
			  (values (list (list theta delayed)) nil)
			(progn
			  (when (pf-p tp) ; should always happen
			    (diagnosis-out (list 'EXPECTED-CONCLUSION (dbsubst (pf-prop tp) #'identity namesubst))))
			  (values nil (list (format nil "We have not shown that.")))))
		    (progn
;		    (when (supertype-of-pf-term-p *emptyctx* (normalize (cdr (assoc *scip-gevar* theta))) *scip-gtp* evar newtp (length ctx))
;		    (multiple-value-bind
;		     (succ theta1)
;		     (task-done task theta nil)
;		     (when succ
;		       (push (list theta1 delayed)
;			     newalts))))
		      (let ((in-set-fragment (tutor-in-set-fragment-p (mapcar #'cadr namedectx) prop)))
		    (if (and in-set-fragment
			   (mls*-tableau (remove-if #'null (mapcar #'(lambda (x)
								       (if (pf-p (cadr x))
									   (pf-prop (cadr x))
									 nil))
								   namedectx))
					 (list prop)))
			(if newalts
			    (values newalts failvals)
			  (progn
			    (diagnosis-out 'UNTRUE-CONCLUSION)
			    (values nil (list (format nil "I'm afraid that doesn't follow, ~d." *student-name*)))))
		    (progn
		      (setq *scip-usable* *sig-granularity-toolow*)
		      (multiple-value-bind
		       (succ1 tasklist1 theta1)
		       (if *tutor-check-low-granularity*
			   (task-fact newtp task delayed theta)
			 nil)
		       (setq *scip-usable* *sig-granularity-perfect*)
		       (if succ1
			   (if newalts
			       (values newalts failvals)
			     (progn
			       (diagnosis-out 'STEP-TOO-SMALL)
			       (values nil (list (format nil "That step is too trivial." *student-name*)))))
			 (multiple-value-bind
			  (succ1 tasklist1 theta1)
			  (task-fact newtp task delayed theta)
			  (if succ1
			      (values (cons (list theta1 tasklist1) newalts) nil)
			    (if newalts
				(values newalts failvals)
			      (progn
			      (setq *scip-usable* *sig-irrelevant*)
			      (multiple-value-bind
			       (succ1 tasklist1 theta1)
			       (task-fact newtp task delayed theta)
			       (setq *scip-usable* *sig-granularity-perfect*)
			       (if succ1
				   (progn
				     (diagnosis-out 'STEP-IRRELEVANT)
				     (values nil (list (format nil "That step is true, but irrelevant." *student-name*))))
				 (progn
				   (setq *scip-usable* *sig-granularity-toohigh*)
				   (multiple-value-bind
				    (succ1 tasklist1 theta1)
				    (if in-set-fragment
					t ; already know it's true in this case
				      (task-fact newtp task delayed theta))
				    (setq *scip-usable* *sig-granularity-perfect*)
				    (if succ1
					(progn
					  (diagnosis-out 'STEP-TOO-BIG)
					  (values nil (list (format nil "How does that follow, ~d?  Try using smaller steps." *student-name*))))
				      (progn
					(diagnosis-out 'STEP-UNJUSTIFIED)
					(values nil (list 
						     (if (eq *tutor-language* 'GERMAN)
							 (format nil "Das ist nicht ganz klar, ~d." *student-name*)
						       (format nil "The statement is not so obvious to me, ~d." *student-name*)))))))))))))))))))))))))))))
   (if *tutor-compute-result*
       (values newtutalts
	       (or failreasons
		   (list 
		    (if (eq *tutor-language* 'GERMAN)
			(format nil "Das ist nicht ganz klar, ~d." *student-name*)
		      (format nil "The statement is not so obvious to me, ~d." *student-name*)))))
     (if *tutor-alts*
	 (progn
	   (scu-out 'OK)
	   (format *main-stream* "OK~%"))
       (generic-back-pfcommand
	failreasons
	(if (eq *tutor-language* 'GERMAN)
	    (format nil "Das ist nicht ganz klar, ~d." *student-name*)
	  (format nil "The statement is not so obvious to me, ~d." *student-name*))
	nil)))))

; returns T if some term which contains at most the evars given has type goaltp
; trm normal
(defun supertype-of-pf-term-p (ctx trm tp evar goaltp n)
  (cond ((dpi-p tp)
	 (supertype-of-pf-term-p (ctx-cons (dpi-dom tp) ctx) (gen-lam-body trm) (dpi-cod tp) evar goaltp n))
	((dclass-p tp)
	 (or (supertype-of-pf-term-p ctx (gen-pair-fst trm) (obj) evar goaltp n)
	     (supertype-of-pf-term-p ctx (gen-pair-snd trm) (pf (normalize (app (dclass-pred tp) (gen-pair-fst trm)))) evar goaltp n)))
	(t
	 (supertype-of-pf-coerce-p ctx trm tp evar goaltp n))))

; trm extraction (evar may be nil, then look for closed subterms)
(defun supertype-of-pf-coerce-p (ctx trm tp evar goaltp n)
;  (when (equal (remove-duplicates (free-evars trm)) (list evar)) (format t "Supergoal: ~d) ~d~% ~d) ~d~%~d~%" (length ctx) tp n goaltp (dbshift-type-n (- (length ctx) n) goaltp))) ; delete me
  (if (and ; (ctx-types-eq ctx tp goaltp)
       (heq tp (dbshift-type-n (- (length ctx) n) goaltp)) ; this is a bit of a hack
       (if evar
	   (equal (remove-duplicates (free-evars trm)) (list evar))
	 (null (free-evars trm))))
      t
    (supertype-of-pf-extr-p ctx trm evar goaltp n)))

; trm extraction
(defun supertype-of-pf-extr-p (ctx trm evar goaltp n)
  (cond ((app-p trm)
	 (if (supertype-of-pf-extr-p ctx (app-func trm) evar goaltp n)
	     t
	   (let ((etp (ctx-extract-type ctx (app-func trm))))
	     (if (dpi-p etp)
		 (supertype-of-pf-term-p ctx (app-arg trm) (dpi-dom etp) evar goaltp n)
	       nil))))
	((fst-p trm)
	 (supertype-of-pf-extr-p ctx (fst-arg trm) evar goaltp n))
	((snd-p trm)
	 (supertype-of-pf-extr-p ctx (snd-arg trm) evar goaltp n))
	(t nil)))
	 

; this doesn't do what's intended yet (call all commands and combine results as alternatives)
(defun alt-pfcommands (pcl)
  (let ((newtutoralts nil)
	(validalts nil)
	(failreasonsl nil)
	(i 0))
    (setq *tutor-compute-result* T)
    (dolist (pc pcl)
      (when (consp pc)
	(when (member (car pc) '(let-pfcommand assume-pfcommand
					       subgoal-pfcommand
					       since-pfcommand
					       hence-pfcommand
					       clearly-pfcommand
					       contradiction-pfcommand
					       cases-pfcommand
					       exists-pfcommand
					       ))
	  (multiple-value-bind
	   (tutalts failreasons)
	   (apply (car pc) (cdr pc))
	   (push failreasons failreasonsl)
	   (when tutalts (push i validalts))
	   (incf i)
	   (setq newtutoralts (append tutalts newtutoralts))))))
    (setq *tutor-compute-result* NIL)
    (push *tutor-alts* *tutor-alts-stack*)
    (setq *tutor-alts* newtutoralts)))

; exists basically combines
; clearly, let, assume
(defun exists-pfcommand (name &optional pre-bd pre-prop)
  (when (stringp name) (setq name (intern name)))
  (let ((ex-prop (list '|dex| pre-bd (cons 'LAM (cons (list name) pre-prop)))))
    (multiple-value-bind
     (failreasons newtutalts)
     (generic-pfcommand
      #'(lambda (theta task delayed)
	  (multiple-value-bind
	   (evar ctx names tp namedectx namesubst)
	   (task-components task)
	   (if (dpi-p tp) ; assume atomic
	       (if (pf-p (dpi-dom tp))
		   (progn
		     (diagnosis-out (list 'SHOULD-ASSUME (dbsubst (pf-prop (dpi-dom tp)) #'identity namesubst)))
		     (values nil (list "It is not clear what you are trying to prove.")))
		 (progn
		   (diagnosis-out (list 'SHOULD-LET (dbsubst-type (dpi-dom tp) #'identity namesubst)))
		   (values nil (list "It is not clear what you are trying to prove."))))
	     (if (eq evar 'DONE)
		 (progn
		   (when (pf-p tp)
		     (diagnosis-out (list 'EXPECTED-CONCLUSION (dbsubst (pf-prop tp) #'identity namesubst))))
		   (values nil (list "It is not clear what you are trying to prove.")))
	     (multiple-value-bind
	      (prop info fail)
	      (normal-fill-in-blanks ex-prop (prop) *input1-state* namedectx)
	      (if fail
		  (progn
		    (diagnosis-out (list 'ILL-FORMED-PROP info))
		    (values nil (list fail)))
		(if info
		    (progn
		      (diagnosis-out (list 'ILL-FORMED-PROP info))
		      (values nil (list "The proposition you gave was ill-formed.")))
		  (let ((newtp (pf (named-term-to-db-1 (mapcar #'car namedectx) prop)))
			(newalts nil)
			(failvals nil))
		    (when *tutor-autoset-sig* (tutor-increase-rules newtp))
					;		  (when (supertype-of-pf-term-p *emptyctx* (normalize (cdr (assoc *scip-gevar* theta))) *scip-gtp* nil newtp (length ctx)) ; done
					;		    (setq newalts (list (list theta (cons task delayed))))) ; already done the thing, no change
		    (unless (eq evar 'DONE)
					;		    (when (supertype-of-pf-term-p *emptyctx* (normalize (cdr (assoc *scip-gevar* theta))) *scip-gtp* evar newtp (length ctx))
					;		    (multiple-value-bind
					;		     (succ theta1)
					;		     (task-done task theta nil)
					;		     (when succ
					;		       (push (list theta1 delayed)
					;			     newalts))))
		      (let ((in-set-fragment (tutor-in-set-fragment-p (mapcar #'cadr namedectx) prop)))
			(if (and in-set-fragment
				 (mls*-tableau (remove-if #'null (mapcar #'(lambda (x)
									     (if (pf-p (cadr x))
										 (pf-prop (cadr x))
									       nil))
									 namedectx))
					       (list prop)))
			    (if newalts
				(values newalts failvals)
			      (progn
				(diagnosis-out 'UNTRUE-CONCLUSION)
				(values nil (list (format nil "I'm afraid that doesn't follow, ~d." *student-name*)))))
			  (progn
			    (setq *scip-usable* *sig-granularity-perfect*)
			    (multiple-value-bind
			     (succ1 tasklist1 theta1)
			     (task-fact newtp task delayed theta)
			     (if (and succ1 tasklist1)
				 (let ((task1 (car tasklist1))
				       (delayed1 (cdr tasklist1)))
				   (multiple-value-bind
				    (evar1 ctx1 names1 tp1 namedectx1 namesubst1)
				    (task-components task1)
				    (let ((jtp (ctx-extract-type ctx1 0)))
				      (when (and (pf-p jtp)
						 (app-p (pf-prop jtp))
						 (app-p (app-func (pf-prop jtp)))
						 (eq (app-func (app-func (pf-prop jtp))) '|dex|)
						 (not (eq evar1 'DONE))
						 (pf-p tp1))
					(multiple-value-bind
					 (tasklist2 theta2)
					 (task-claim (dpi (dclass (app '|in| (app-arg (app-func (pf-prop jtp)))))
							  (dpi (pf (gen-lam-body (app-arg (pf-prop jtp))))
							       (dbshift-type-n 2 tp1)))
						     task1
						     delayed1 theta1)
					 (let ((task2 (car tasklist2)))
					   (multiple-value-bind
					    (evar2 ctx2 names2 tp2 namedectx2 namesubst2)
					    (task-components task2)
					    (let ((pftrm
						   (app-l '|dexE|
							  (dbshift-n 1 (app-arg (app-func (pf-prop jtp))))
							  (dbshift-n 1 (app-arg (pf-prop jtp)))
							  1
							  (pf-prop tp2)
							  0)))
;					      (unless (ctx-term-type-p nil (lam-ctx ctx2 pftrm) (get evar2 'dbtype)) (break)) ; delete me
					      (setq theta2 (compose-theta-1 evar2 (lam-ctx ctx2 pftrm) theta2))
					      (let ((task3 (cadr tasklist2))
						    (aname (intern (format nil "ass~d" (incf *scip-assnum*)))))
						(multiple-value-bind
						 (evar3 ctx3 names3 tp3 namedectx3 namesubst3)
						 (task-components task3)
						 (setq task3
						       (list evar3
							     (ctx-cons (dpi-dom (dpi-cod tp3))
								       (ctx-cons (dpi-dom tp3)
										 ctx3))
							     (cons aname ; "existential-assumption"
								   (cons name names3))
							     (dpi-cod (dpi-cod tp3))
							     (cons (list aname (dbsubst-type (dpi-dom (dpi-cod tp3))
											     #'identity
											     (cons name (cons #'identity namesubst3))))
								   (cons (list name (dbsubst-type (dpi-dom tp3)
												  #'identity
												  namesubst3))
									 namedectx3))
							     (cons aname (cons #'identity (cons name (cons #'identity namesubst3))))))
						 (values (cons (list theta2 (cons task3 (cddr tasklist2))) newalts) nil)
						 ))))))))))
			       (if newalts
				   (values newalts failvals)
				 (progn
				   (setq *scip-usable* *sig-irrelevant*)
				   (multiple-value-bind
				    (succ1 tasklist1 theta1)
				    (task-fact newtp task delayed theta)
				    (setq *scip-usable* *sig-granularity-perfect*)
				    (if succ1
					(progn
					  (diagnosis-out 'STEP-IRRELEVANT)
					  (values nil (list (format nil "That step is true, but irrelevant." *student-name*))))
				      (progn
					(setq *scip-usable* *sig-granularity-toohigh*)
					(multiple-value-bind
					 (succ1 tasklist1 theta1)
					 (if in-set-fragment
					     t ; already know it's true in this case
					   (task-fact newtp task delayed theta))
					 (setq *scip-usable* *sig-granularity-perfect*)
					 (if succ1
					     (progn
					       (diagnosis-out 'STEP-TOO-BIG)
					       (values nil (list (format nil "How does that follow, ~d?  Try using smaller steps." *student-name*))))
					   (progn
					     (diagnosis-out 'STEP-UNJUSTIFIED)
					     (values nil (list 
							  (if (eq *tutor-language* 'GERMAN)
							      (format nil "Das ist nicht ganz klar, ~d." *student-name*)
							    (format nil "The statement is not so obvious to me, ~d." *student-name*)))))))))))))))))))))))))))
     (if *tutor-compute-result*
	 (values newtutalts
		 (or failreasons
		     (list 
		      (if (eq *tutor-language* 'GERMAN)
			  (format nil "Das ist nicht ganz klar, ~d." *student-name*)
			(format nil "The statement is not so obvious to me, ~d." *student-name*)))))
       (if *tutor-alts*
	   (progn
	     (scu-out 'OK)
	     (format *main-stream* "OK~%"))
	 (generic-back-pfcommand
	  failreasons
	  (if (eq *tutor-language* 'GERMAN)
	      (format nil "Das ist nicht ganz klar, ~d." *student-name*)
	    (format nil "The statement is not so obvious to me, ~d." *student-name*))
	  nil))))))

					; unused at the moment
(defun cases-pfcommand (&optional pre-prop)
  (if pre-prop
      (progn
	(multiple-value-bind
	 (failreasons newtutalts)
	 (generic-pfcommand
	  #'(lambda (theta task delayed)
	      (multiple-value-bind
	       (evar ctx names tp namedectx namesubst)
	       (task-components task)
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
		       (values (list (list (compose-theta-1 evar ap theta))
				     (cons (list evar3 ctx names ftp3
						 namedectx namesubst)
					   (cons (list evar4 ctx names ftp4
						       namedectx namesubst)
						 delayed)))
			       nil))
		   (values nil
			   (list "You cannot apply cases.  There is no disjunction in context.")))))))
	 (if *tutor-compute-result*
	     (values newtutalts failreasons)
	   (if *tutor-alts*
	       (progn
		 (scu-out 'OK)
		 (format *main-stream* "OK~%"))
	     (generic-back-pfcommand
	      failreasons
	      (format nil "It is not clear why you should use proof by cases.")
	      nil)))))
    t ; to do
    ))

(defun contradiction-pfcommand ()
  (multiple-value-bind
   (failreasons newtutalts)
   (generic-pfcommand
    #'(lambda (theta task delayed)
	(multiple-value-bind
	 (evar ctx names tp namedectx namesubst)
	 (task-components task)
	 (if (and (pf-p tp) (not (eq evar 'DONE)))
	     (let ((C (pf-prop tp))
		   (pffalse (pf '|false|)))
	       (if (eq C '|false|)
		   (values nil (list "You are already proving false, ~d." *student-name*))
					; I should also check if ~C is already on the ctx, in which case pf by contradiction is unreasonable
		 (let* ((newevar (intern-gensym))
			(trm1 (app-n-1-to-0 (length ctx) newevar))
			(trm (app (app '|contradiction| C) trm1))
			(z (intern-gensym "ass"))
			(atp (pf (app '|not| C)))
			(tp2 (dpi atp pffalse)))
		   (setf (get z 'bvar) t)
		   (setf (get z 'dbtype) (dbsubst-type (dpi-dom tp) #'identity namesubst))
		   (setf (get newevar 'evar) t)
		   (setf (get newevar 'dbtype) (dpi-ctx ctx tp2))
		   (dotimes (n (length ctx)) (setq trm (lam trm)))
		   (values (list (list (compose-theta-1 evar trm theta)
				       (cons (list newevar (ctx-cons atp ctx) (cons z names) pffalse
						   (cons (list z (get z 'dbtype)) namedectx)
						   (cons z (cons #'identity namesubst)))
					     delayed)))
			   nil))))
	   (values nil (list "It is not clear what you are trying to prove."))))))
   (if *tutor-compute-result*
       (values newtutalts failreasons)
     (if *tutor-alts*
	 (progn
	   (scu-out 'OK)
	   (format *main-stream* "OK~%"))
       (generic-back-pfcommand
	failreasons
	(format nil "It is not clear why you should use proof by contradiction.")
	nil)))))

(defun tutor-in-set-fragment-p (tps prop)
  (if tps
      (let ((tp (car tps)))
	(if (or (obj-p tp)
		(and (dclass-p tp) 
		     (app-p (dclass-pred tp))
		     (eq (app-func (dclass-pred tp)) '|in|)
		     (iterated-powerset-p (app-arg (dclass-pred tp))))
		(and (pf-p tp)
		     (prop-comp-set-fragment-p (pf-prop tp))))
	    (tutor-in-set-fragment-p (cdr tps) prop)
	  nil))
    (prop-comp-set-fragment-p prop)))

(defun post-process-tutor-alt (talt)
  (if (cadr talt)
      (let ((theta (car talt))
	    (task (caadr talt))
	    (delayed (cdadr talt))
	    (ret nil))
	; sanity check
;	(dolist (x (free-evars (normalize (cdr (assoc *scip-gevar* theta))))) (unless (assoc x (cons task delayed)) (format t "1 Lost ~d~%" x) (setq *talt* talt) (break)))
	(when *tutor-eager-elims*
	  (multiple-value-bind
	   (succ1 tasklist1 theta1)
	   (task-close-under-simple-elims task delayed theta)
	   (when succ1
	     (setq theta theta1)
	     (setq task (car tasklist1))
	     (setq delayed (cdr tasklist1)))))
	; sanity check
;	(dolist (x (free-evars (normalize (cdr (assoc *scip-gevar* theta))))) (unless (assoc x (cons task delayed)) (format t "2 Lost ~d~%" x) (setq *talt* talt) (break)))
	(setq ret (list (list theta (cons task delayed))))
	(multiple-value-bind
	 (evar ctx names tp namedectx namesubst)
	 (task-components task)
	 (let ((back1 (quick-fill-gap ctx tp *tutor-auto-back* nil 2)))
	   (dolist (y back1)
	     (let* ((tmp (car y))
		    (newtheta (compose-theta-1 evar tmp theta))
		    (newevars (cadr y)))
	       (if newevars
		   (if (cdr newevars) ; 2 new subgoals - put in both orders
		       (let ((ev1 (caar newevars))
			     (dtp1 (cdar newevars))
			     (ev2 (caadr newevars))
			     (dtp2 (cdadr newevars)))
			 (setf (get ev1 'dtype) dtp1) ; global type, so OK
			 (setf (get ev2 'dtype) dtp2) ; global type, so OK
			 (dotimes (j (length ctx))
			   (when (dpi-p dtp1)
			     (setq dtp1 (dpi-cod dtp1)))
			   (when (dpi-p dtp2)
			     (setq dtp2 (dpi-cod dtp2))))
			 (let ((subtask1 (list ev1 ctx names dtp1 namedectx namesubst))
			       (subtask2 (list ev2 ctx names dtp2 namedectx namesubst)))
			   (push (list newtheta
				       (cons subtask1
					     (cons subtask2
						   delayed))
				       )
				 ret)
			   (push (list newtheta
				       (cons subtask2
					     (cons subtask1
						   delayed))
				       )
				 ret)
			   (push (list newtheta
				       (cons subtask1
					     (cons subtask2
						   (cons (list 'DONE ctx names tp namedectx namesubst)
							 delayed)))
				       )
				 ret)
			   (push (list newtheta
				       (cons subtask2
					     (cons subtask1
						   (cons (list 'DONE ctx names tp namedectx namesubst)
							 delayed)))
				       )
				 ret)))
					; 1 new subgoal
		     (let ((ev1 (caar newevars))
			   (dtp1 (cdar newevars)))
		       (setf (get ev1 'dtype) dtp1) ; global type, so OK
		       (dotimes (j (length ctx))
			 (when (dpi-p dtp1)
			   (setq dtp1 (dpi-cod dtp1))))
		       (let ((subtask1 (list ev1 ctx names dtp1 namedectx namesubst)))
			 (push (list newtheta
				     (cons subtask1
					   delayed)
				     )
			       ret)
			 (push (list newtheta
				     (cons subtask1
					   (cons (list 'DONE ctx names tp namedectx namesubst)
						 delayed))
				     )
			       ret)
			 )))
					; no new subgoal (secretly solved, let's see if the student notices...)
		 (progn
		   (push (list newtheta delayed)
			 ret)
		   (push (list newtheta
			       (cons (list 'DONE ctx names tp namedectx namesubst)
				     delayed))
			 ret)
		   )))))
	 ret))
    (list talt)))

(defun print-tutor-help ()
  (format t "Commands:~%")
  (format t "qed.  % assert that the goal (or current subgoal) is done.~%")
  (format t "let x.  % introduce a variable x for an object~%")
  (format t "let x y ... z.  % introduce variables x, y, ... z for objects~%")
  (format t "let x y ... z:A.  % introduce variables x, y, ... z for objects of type A~%")
  (format t "assume <Proposition>.  % introduce an assumption~%")
  (format t "willshow <Proposition>.  % reduce current goal to given subgoal~%")
  (format t "clearly <Proposition>.  % infer given proposition~%")
  (format t "hence <Proposition>.  % infer given proposition from last assertion in context~%")
;  (format t "since <Propositions>, we have <Proposition>.  % infer given proposition from last assertion in context~%")
;  (format t "showing <Proposition>. % indicate what the current goal is~%")
  (format t "i give up.  % quit~%")
  )

(defun tutor-increase-rules (newtp)
  (let ((cl (dtype-sig-elts newtp)))
    (dolist (c *global-sigma*)
      (unless (member c *sig-granularity-perfect*)
	(when (and (or (dtype-returns-pf-p (get c 'dbtype)) (dtype-returns-dclass-p (get c 'dbtype)))
		   (intersection cl (dtype-sig-elts (get c 'dbtype))))
	  (push c *sig-granularity-perfect*))))))

(defun tutor1l-execute (comm)
  (case (car comm)
	(STATUS (print-status))
	(HELP (print-tutor-help))
	((QED DONE) (qed-pfcommand))
	(UNDO (undo-pfcommand))
	((Q X QUIT EXIT I-GIVE-UP) (quit-pfcommand))
	(LET
	 (let ((nl (mapcar #'(lambda (x)
			       (if (symbolp x) x (intern x)))
			   (if (consp (cadr comm))
			       (cadr comm)
			     (list (cadr comm)))))
	       (tp (if (caddr comm) (input1l-predtype (caddr comm)) nil)))
	   (let-pfcommand nl tp)))
	(ASSUME
	 (let ((e (input1l-preextr (cadr comm))))
	   (assume-pfcommand e)))
	(WILLSHOW
	 (let ((e (input1l-preextr (cadr comm))))
	   (subgoal-pfcommand e)))
	(EXISTS
	 (exists-pfcommand (cadr comm)
			   (input1l-preextr (caddr comm))
			   (input1l-preextr (cadddr comm))))
	(CASES
	 (if (cadr comm)
	     (cases-pfcommand (input1l-preextr (caddr comm)))
	   (cases-pfcommand)))
	(CONTRADICTION (contradiction-pfcommand))
	(HENCE
	 (hence-pfcommand (input1l-preextr (cadr comm))))
	(CLEARLY
	 (clearly-pfcommand (input1l-preextr (cadr comm))))
	(LISP (eval (cadr comm)))
	(t
	 (scu-out 'NOT-TUTOR-COMMAND))))

(defun diagnosis-out (x)
  (when (> *verbose* 19)
    (format t "Diagnosis: ~d~%" x))
  (scu-out (list 'DIAGNOSIS x)))
