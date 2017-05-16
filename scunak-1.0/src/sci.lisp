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
; January 2006

(defvar *sci-socket* nil)
(defvar *sci-namedectx* nil)
(defvar *sci-ctx* nil)
(defvar *sci-namesubst* nil)

(defvar *sci-ready* 0)
(defvar *sci-variable-already-declared* 1)
(defvar *sci-variable-ill-typed* 2)
(defvar *sci-assumption-ill-typed* 3)
(defvar *sci-formula-ill-typed* 4)
(defvar *sci-formula-true* 5)
(defvar *sci-formula-false* 6)
(defvar *sci-formula-truth-value-unknown* 7)
(defvar *sci-bad-input* 8)
(defvar *sci-formula-neg-satisfiable* 9)

(defvar *sci-comp-set* nil)

(defvar *sci-output-time* t)
(defvar *sci-socket-plus* t)

(defun sci-initfn ()
  (let ((prefilenames (command-line-arg-several "-p"))
	(filenames (command-line-arg-several "-f"))
	(mach (command-line-arg "-m"))
	(sock (command-line-arg "-s"))
	(color (command-line-switch "-C"))
	(verb (command-line-switch "-v"))
	(verb2 (command-line-switch "-V")))
    (when verb
      (setq *verbose* 20))
    (when verb2
      (setq *verbose* 99))
    (unless color
      (setq *style* 'ascii))
    #+:allegro
    (when (and mach sock)
      (setq *sci-socket*
	    (acl-socket:make-socket :remote-host mach :remote-port (read-from-string sock))))
    (unless *sci-socket*
      (scunak-header "Welcome to SCI: Scunak Interactive."))
    (setq *allow-constants* nil)
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
    (sci)
    (exit)))

#+:allegro
(defun save-sci-image ()
  (set-fail-to-throw-fail)
  (setq excl:*restart-app-function* 'sci-initfn)
  (excl:dumplisp :name (format nil "~d/allegro-scunak-sci.dxl" *dxldir*)))

#+:clisp
(defun save-sci-image ()
  (set-fail-to-throw-fail)
  (setq system::*driver* #'sci-initfn)
  (ext:saveinitmem (format nil "~d/clisp-scunak-sci.mem" *dxldir*) :quiet t :init-function 'sci-initfn))

#+:cmu
(defun save-sci-image ()
  (set-fail-to-throw-fail)
  (extensions:savelisp (format nil "~d/cmucl-scunak-sci" *dxldir*) :init-function 'sci-initfn
		       :print-herald nil))

(defun sci ()
  (setq *sci-namedectx* nil)
  (setq *sci-ctx* nil)
  (setq *sci-namesubst* nil)
  (setq *sci-comp-set* t)
  (let ((sci-done nil))
    (declare (special sci-done))
    (loop until sci-done do
	  (catch 'fail
	    (unless *sci-socket*
	      (format t ">")
	      )
	    (let* ((r (if *sci-socket*
			  (progn
			    (sci-out *sci-ready*)
			    (read-line *sci-socket*)
			    )
			(read-line)))
		   (words (tokenize-str r))
		   (n (length words))
		   (inittime (get-internal-run-time)) 
		   (ch (earley-parse-string 'SCI-ITEM r input1-grammar))
		   (parsetime (get-internal-run-time)) 
		   (res (chart-to-parse-trees words 0 n 'SCI-ITEM input1-grammar ch 1))
		   (evaltime (get-internal-run-time)))
	      (when *sci-output-time*
		(format t "Parse Time: ~d~%" (- parsetime inittime))
		(format t "Eval Time: ~d~%" (- evaltime parsetime))
		(format t "Total Time: ~d~%" (- evaltime inittime)))
	      (when (> *verbose* 5)
		(format t "Read ~d~%" r))
	      (unless res
		(if *sci-socket*
		    (sci-out *sci-bad-input*)
		  (format t "Did not understand sci input.~%~d~%" words))))))
    (when *sci-socket*
      (close *sci-socket*))
    ))

(defun sci-quit-command ()
  (declare (special sci-done))
  (setq sci-done t)
  t)

(defun sci-check (pre-prop)
  (multiple-value-bind
   (prop info fail)
   (normal-fill-in-blanks pre-prop (prop) *input1-state* *sci-namedectx*)
   (if (or info fail)
       (if *sci-socket*
	   (sci-out *sci-formula-ill-typed*)
	 (format t "Proposition to check was ill-typed~%"))
     (let ((dbprop (named-term-to-db-1 (mapcar #'car *sci-namedectx*) prop)))
       (if (and *sci-comp-set* (prop-comp-set-fragment-p prop))
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
		   (when (> *verbose* 10)
		     (format t "Counterexample~%")
		     (dolist (p (car br))
		       (format t "~d~%" (output1-extraction-string p nil nil))))
		   (if *sci-socket*
		       (sci-out *sci-formula-neg-satisfiable*)
		     (format t "There is a countermodel for formula in context.~%")))
	       (if *sci-socket*
		   (sci-out *sci-formula-true*)
		 (format t "Formula is true in context.~%"))))
	 (if (quick-fill-gap *sci-ctx* (pf dbprop) *global-sigma* t 0 nil)
	     (if *sci-socket*
		 (sci-out *sci-formula-true*)
	       (format t "Formula is true in context.~%"))
	   (let ((negprop (sci-neg-prop dbprop)))
	     (if (quick-fill-gap *sci-ctx* (pf negprop) *global-sigma* t 0 nil)
		 (if *sci-socket*
		     (sci-out *sci-formula-false*)
		   (format t "Formula is false in context.~%"))
	       (if *sci-socket*
		   (sci-out *sci-formula-truth-value-unknown*)
		 (format t "Formula has an unknown truth value in context.~%")))))))))
  t)

(defun sci-newvar (x pre-tp)
  (when (stringp x)
    (setq x (intern x)))
  (if (member x (mapcar #'car *sci-namedectx*))
       (if *sci-socket*
	   (sci-out *sci-variable-already-declared*)
	 (format t "~d already declared.~%" x))
    (multiple-value-bind
     (tp info fail)
     (deptype-fill-in-blanks pre-tp *input1-state* *sci-namedectx*)
     (if (or info fail)
	 (if *sci-socket*
	     (sci-out *sci-variable-ill-typed*)
	   (format t "Could not parse type~%"))
       (let ((dbtp (named-type-to-db *sci-namedectx* tp)))
	 (when *sci-comp-set*
	   (unless (or (obj-p tp)
		       (and (dclass-p tp) 
			    (app-p (dclass-pred tp))
			    (eq (app-func (dclass-pred tp)) '|in|)
			    (iterated-powerset-p (app-arg (dclass-pred tp))))
		       (and (pf-p tp)
			    (prop-comp-set-fragment-p (pf-prop tp))))
	     (setq *sci-comp-set* nil)))
	 (setf (get x 'bvar) t)
	 (setf (get x 'dbtype) dbtp)
	 (push (list x tp) *sci-namedectx*)
	 (setq *sci-ctx* (ctx-cons dbtp *sci-ctx*))
	 (setq *sci-namesubst*
	       (cons x (cons #'identity *sci-namesubst*)))
	 ))))
  t)
  
(defun sci-assume (pre-tp)
  (multiple-value-bind
   (tp info fail)
   (deptype-fill-in-blanks pre-tp *input1-state* *sci-namedectx*)
   (if (or info fail)
       (if *sci-socket*
	   (sci-out *sci-assumption-ill-typed*)
	 (format t "Could not parse assumption type~%"))
     (let ((x (intern-gensym "ass"))
	   (dbtp (named-type-to-db *sci-namedectx* tp)))
       (when *sci-comp-set*
	 (unless (and (pf-p tp)
		      (prop-comp-set-fragment-p (pf-prop tp)))
	   (setq *sci-comp-set* nil)))
       (setf (get x 'bvar) t)
       (setf (get x 'dbtype) dbtp)
       (push (list x tp) *sci-namedectx*)
       (setq *sci-ctx* (ctx-cons dbtp *sci-ctx*))
       (setq *sci-namesubst*
	     (cons x (cons #'identity *sci-namesubst*))))))
  t)
  
(defun sci-out (n)
  (when (> *verbose* 5) (format t "sci-out ~d~%" n))
;  (when *sci-socket-plus* (format t "<RESPONSE value=\"~d\"></RESPONSE>~%" n))
  (when *sci-socket-plus* (format t "Response: ~d~%" n))
;  (write-byte n *sci-socket*)
  (format *sci-socket* "~d~%" n)
  (force-output *sci-socket*))

(defun sci-neg-prop (prop)
  (if (and (app-p prop) (eq (app-func prop) '|not|))
      (app-arg prop)
    (app '|not| prop)))

(defun iterated-powerset-p (trm)
  (or (bvar-p trm)
      (and (app-p trm)
	   (eq (app-func trm) '|powerset|)
	   (iterated-powerset-p (app-arg trm)))))
