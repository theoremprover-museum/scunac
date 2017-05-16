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
; Date: February, 2006

(defvar *scunak-socket* nil)
(defvar *scunak-kernel* nil)

(defvar *scunak-time-limit* nil)

(defvar *scunak-namedectx* nil)
(defvar *scunak-ctx* nil)
(defvar *scunak-namesubst* nil)
(defvar *scunak-comp-set* nil)
(defvar *scunak-output-time* nil)

(defvar *scunak-main-dir* nil)

(defvar *initialized* nil)
(defvar *flag-logo* nil)

(defun scunak-initfn ()
  (catch 'fail
    (unless *initialized*
    (let ((prefilenames (command-line-arg-several "-p"))
	  (filenames (command-line-arg-several "-f"))
	  (mach (command-line-arg "-m"))
	  (sock (command-line-arg "-s"))
	  (dir (command-line-arg "-d"))
	  (color (command-line-switch "-C"))
	  (af (command-line-switch "-A"))
	  (kernel (command-line-arg "-k"))
	  (verb (command-line-switch "-v"))
	  (verb2 (command-line-switch "-V"))
	  (studentname (command-line-arg "-n")))
      (when verb
	(setq *verbose* 20))
      (when verb2
	(setq *verbose* 99))
      (if color
	  (setq *style* 'ansi-color)
	(setq *style* 'ascii))
      (when dir
	(if (directory dir)
	    (setq *scunak-main-dir* dir)
	  (format t "No directory ~d exists~%" dir)))
      #+(or :allegro :clisp)
      (when (and mach sock)
	(setq *scunak-socket* (create-socket mach (read-from-string sock)))
	(scu-out 'SCUNAK)
	(scu-out '1.0)
	(setq *standard-output* (create-socket mach (read-from-string sock)))
	(format t "Scunak Text Output Socket~%"))
      #-(or :allegro :clisp)
      (when (and mach sock)
	(format t "Sockets connections are not available using Scunak with this lisp.~%"))
      (when af (setq *flag-logo* t))
      (unless *scunak-socket*
	(let ((heads '("Welcome to Scunak."
		       "Welcome to Scunak, the Mathematical Assistant System with Scunakation"
		       "Welcome to Scunak, the Scunakating Mathematical Assistant System"
		       "Welcome to Scunak.  Please enjoy your Scunakation experience."
		       "Welcome to Scunak.  Scunakate with pleasure."
		       "Welcome to Scunak.  The Future of Scunak is You."
		       "Welcome to Scunak.  Assistenzsystem der Zukunft."
		       "I AM SCUNAK."
		       "Welcome to Scunak.  A is A."
		       "Welcome to Scunak.  Run Into The Abyss."
		       )))
	  (scunak-header (nth (mod (get-universal-time) (length heads)) heads))))
      (when (and *scunak-main-dir* (probe-file (format nil "~d/patch.lisp" *scunak-main-dir*)))
	(format t "Loading main patch file.~%")
	(load (format nil "~d/patch.lisp" *scunak-main-dir*)))
      (when (probe-file "patch.lisp")
	(format t "Loading local patch file.~%")
	(load "patch.lisp"))
      (if studentname
	  (setq *student-name* studentname)
	(setq *student-name* "Dave"))
      (cond ((string= kernel "mu")
	     (if (s-probe-file "mu-kernel.lisp")
		 (s-load "mu-kernel.lisp")
	       (fail "Cannot find kernel lisp file")))
	    ((or (null kernel) (string= kernel "macu"))
	     (if (s-probe-file "macu-kernel.lisp")
		 (s-load "macu-kernel.lisp")
	       (fail "Cannot find kernel lisp file")))
	    ((not (string= kernel "none"))
	     (let ((kernelfile (format nil "~d-kernel.lisp" kernel)))
	       (if (s-probe-file kernelfile)
		   (s-load kernelfile)
		 (fail "Cannot find kernel lisp file"))))
	    (t
	     (format t "Starting Scunak with no kernel.~%"))
	    )
      (setq *allow-constants* t)
      (dolist (prefilename prefilenames)
	(unless (s-probe-file prefilename)
	  (setq prefilename (format nil "~d.lisp" prefilename))
	  (unless (s-probe-file prefilename)
	    (fail (format nil "No file named ~d." prefilename))))
	(s-load prefilename))
      (catch 'fail
	(dolist (filename filenames)
	  (unless (s-probe-file filename)
	    (fail (format nil "No file named ~d." filename)))
	  (readinput1 filename)))
      (setq *initialized* t))
    (scunak-pre-top)
    ))
  (exit))

(defun scunak-pre-top ()
  (if *scunak-socket*
      (scunak-top-sock)
    (scunak-top)))

#+:allegro
(defun save-scunak-image ()
  (set-fail-to-throw-fail)
  (setq excl:*restart-app-function* 'scunak-initfn)
  (excl:dumplisp :name (format nil "~d/scunak-allegro.dxl" *dxldir*)))

#+:clisp
(defun save-scunak-image ()
  (set-fail-to-throw-fail)
  (setq system::*driver* #'scunak-initfn)
  (ext:saveinitmem (format nil "~d/scunak-clisp.mem" *dxldir*) :quiet t :init-function 'scunak-initfn))

; cmu lisp is not fully supported, but I did start
#+:cmu
(defun save-scunak-image ()
  (set-fail-to-throw-fail)
  (extensions:savelisp (format nil "~d/scunak-cmucl-image" *dxldir*) :init-function 'scunak-initfn
		       :print-herald nil))

(defun scunak-top ()
  (setq *scunak-namedectx* nil)
  (setq *scunak-ctx* nil)
  (setq *scunak-namesubst* nil)
  (setq *scunak-comp-set* t)
  (setq *justify-usable* *global-sigma*)
  (let ((scunak-done nil))
    (declare (special scunak-done))
    (loop until scunak-done do
	  (catch 'fail
	    (format t ">")
	    (let* ((r (read-line))
		   (words (remove-nach-wh (tokenize-str r))))
	      (when words
		(let* ((n (length words))
		       (inittime (get-internal-run-time)) 
		       (inittime2 (get-universal-time)) 
		       (ch (earley-parse-string 'TOP-ITEM r input1-grammar))
		       (parsetime (get-internal-run-time)) 
		       (parsetime2 (get-universal-time)) 
		       (res (chart-to-parse-trees words 0 n 'TOP-ITEM input1-grammar ch 1))
		       (evaltime (get-internal-run-time))
		       (evaltime2 (get-universal-time)))
		  (when *scunak-output-time*
		    (format t "Parse Time: ~d (real ~d)~%" (- parsetime inittime) (- parsetime2 inittime2))
		    (format t "Eval Time: ~d (real ~d)~%" (- evaltime parsetime) (- evaltime2 parsetime2))
		    (format t "Total Time: ~d (real ~d)~%" (- evaltime inittime) (- evaltime2 inittime2)))
		  (when (> *verbose* 5)
		    (format t "Read ~d~%" r))
		  (unless res
		    (format t "Did not understand input.~%~d~%" words)))))))
    ))

(defun scunak-top-sock ()
  (setq *scunak-namedectx* nil)
  (setq *scunak-ctx* nil)
  (setq *scunak-namesubst* nil)
  (setq *scunak-comp-set* t)
  (setq *justify-usable* *global-sigma*)
  (let ((scunak-done nil))
    (declare (special scunak-done))
    (loop until scunak-done do
	  (catch 'fail
	    (force-output *standard-output*)
	    (scu-out 'READY)
	    (let* ((r (read *scunak-socket* nil nil)))
	      (scunak-top-sock-1 r)
	      ))))
  (close *scunak-socket*)
  )
  
(defun scunak-top-sock-1 (r)
  (unless (and (open-stream-p *scunak-socket*)
	       (open-stream-p *standard-output*))
    (dolist (a *quick-fill-gap-external-agents*)
      (when (and (streamp (cadr a))
		 (open-stream-p (cadr a)))
	(close (cadr a))))
    (setq scunak-done t)
    (setq r nil)
    )
  (when (> *verbose* 5)
    (format t "Read ~d~%" r))
  (when r
    (cond ((member r '(Q X EXIT QUIT))
	   (setq scunak-done t))
	  ((and (consp r) (eq (car r) 'LISP))
	   (eval (cadr r)))
	  ((and (consp r) (eq (car r) 'PROVE))
	   (let ((xs (cadr r)))
	     (let* ((x (if (stringp xs) (intern xs) (if (symbolp xs) xs nil)))
		    (ts (get x 'timestamp)))
	       (if (and (claimname-p x) ts)
		   (if (dtype-returns-pf-p (get x 'dbtype))
		       (scip x)
		     (progn
		       (scu-out 'PROVE-NOT-PROOF-TYPE)
		       (scu-out 'FAILED)
		       (format t "~d does not have a proof type.~%" x)))
		 (progn
		   (scu-out 'PROVE-NOT-CLAIM)
		   (scu-out 'FAILED)
		   (format t "~d is not an open claim.~%" x))))))
	  ((and (consp r) (eq (car r) 'TUTOR))
	   (let ((n (if (symbolp (cadr r))
			(cadr r)
		      (if (stringp (cadr r))
			  (intern (cadr r))
			(if (consp (cadr r))
			    (if (symbolp (caadr r))
				(caadr r)
			      (if (stringp (caadr r))
				  (intern (caadr r))
				nil)))))))
	     (if (and n (get n 'dbtype)
		      (dtype-returns-pf-p (get n 'dbtype)))
		 (progn
		   (setq *tutor-nl* nil)
		   (tutor-claim (input1l-newapp (cadr r))))
	       (progn
		 (scu-out 'BAD-TUTOR-CLAIM)
		 (scu-out 'FAILED)
		 (format t "~d does not return a proof type.~%" (cadr r))
		 nil))))
	  (t
	   (unless (consp r)
	     (setq r (list r)))
	   (multiple-value-bind
	    (ok failinfo)
	    #+:allegro
	    (if *scunak-time-limit*
		(mp:with-timeout (*scunak-time-limit* (scu-out 'TIMED-OUT) (values nil "Timed Out")) (input1l-execute r))
	      (input1l-execute r))
	    #-:allegro
	    (input1l-execute r)
	    (unless ok
	      (scu-out 'FAILED)
	      (format t "Problem: ~d~%" failinfo)
	      ))))))

(defun remove-nach-wh (words)
  (if words
      (if (equal words '(WH))
	  nil
	(cons (car words) (remove-nach-wh (cdr words))))
    nil))

(defun top-quit-command ()
  (declare (special scunak-done))
  (setq scunak-done t))

(defun top-lisp-command ()
  (let ((r (read)))
    (eval r)
    t))

(defun print-help-name (name)
  (cond ((constname-p name)
	 (when *scunak-socket*
	   (scu-out (list 'CONST name (get name 'dbtype))))
 	 (format t "~d is a constant of type:~%~d~%" name
 		 (output1-type-string (get name 'dbtype))
 		 )
 	 (if (get name 'auto-gen)
 	     (format t "~d was automatically generated for handling folding/unfolding of an abbreviation.~%" name)
 	   (when (dtype-returns-pf-p (get name 'dbtype))
 	     (format t "~d is essentially a basic proof rule.~%" name))))
 	((abbrevname-p name)
	 (when *scunak-socket*
	   (scu-out (list 'ABBREV name (get name 'dbtype) (get name 'defn))))
 	 (format t "~d is an abbreviation of type:~%~d~%" name
 		 (output1-type-string (get name 'dbtype)))
 	 (format t "Defn: ~d~%"
 		 (output1-normal-string (get name 'defn)))
 	 (case (classify-type (get name 'dbtype))
 	       (TFUNC
 		(let ((df (auto-gen-name name "F" 'defn-tfunc-fold))
 		      (du (auto-gen-name name "U" 'defn-tfunc-unfold)))
 		  (format t "There are two related constants for folding and unfolding this abbreviation:~%")
 		  (format t "~d : ~d~%" df (output1-type-string (get df 'dbtype)))
 		  (format t "~d : ~d~%" du (output1-type-string (get du 'dbtype)))))
 	       (FUNC
 		(let ((df (auto-gen-name name "F" 'defn-func-fold))
 		      (du (auto-gen-name name "U" 'defn-func-unfold)))
 		  (format t "There are two related constants for folding and unfolding this abbreviation:~%")
 		  (format t "~d : ~d~%" df (output1-type-string (get df 'dbtype)))
 		  (format t "~d : ~d~%" du (output1-type-string (get du 'dbtype)))))
 	       (RELN
 		(let ((df (auto-gen-name name "F" 'defn-reln-fold))
 		      (du (auto-gen-name name "U" 'defn-reln-unfold)))
 		  (format t "There are two related constants for folding and unfolding this abbreviation:~%")
 		  (format t "~d : ~d~%" df (output1-type-string (get df 'dbtype)))
 		  (format t "~d : ~d~%" du (output1-type-string (get du 'dbtype)))))
 	       (t
 		(format t "~d is essentially a derived proof rule.~%" name)
 		(format t "Due to proof irrelevance, the abbreviation never needs to be expanded.~%")
 		)))
 	((claimname-p name)
	 (when *scunak-socket*
	   (scu-out (list 'CLAIM name (get name 'dbtype))))
 	 (format t "~d is a claim of type:~%~d~%" name
 		 (output1-type-string (get name 'dbtype)))
 	 (if (dtype-returns-pf-p (get name 'dbtype))
 	     (format t "~d is essentially an open conjecture.~%" name)
 	   (if (dtype-returns-prop-p (get name 'dbtype))
 	       (format t "~d is essentially a property which has not yet been defined.~%" name)
 	     (format t "~d is essentially an object which has not yet been defined.~%" name))))
	((get name 'bvar)
	 (when *scunak-socket*
	   (scu-out (list 'BVAR name (get name 'dbtype))))
 	 (format t "~d is a bound variable of type:~%~d~%" name
 		 (output1-type-string (get name 'dbtype))))
	((get name 'notation)
	 (when *scunak-socket*
	   (scu-out (list 'NOTATION name (get name 'notation))))
	 (format t "~d is notation for ~d~%" name (get name 'notation)))
 	(t (format t "Sorry, I have no information about ~d.~%" name))))

(defun print-help-top ()
  (format t "You are currently in the top level.~%Some Top Level Commands:~%")
  (format t "[x:A] - adds a variable x of type A to context~%")
  (format t "c:A? - adds a claim c of type A to the signature~%")
  (format t "c:A=D. - defines abbreviation c of type A using term D.~%")
  (format t "coercion PFTERM. - if PFTERM has type |- (A <= B), then any term of type A can be used as a term of type B.~%")
  (format t "notation NAME EXTRACT. - declare NAME as shorthand for EXTRACT~%")
  (format t "load \"FILENAME\"! - load pam FILENAME~%")
  (format t "loadl \"FILENAME\"! - load lisp FILENAME~%")
  (format t "show-ctx - print variables in current context~%")
  (format t "typeof EXTRACT - give type of EXTRACT, if possible~%")
  (format t "justify EXTRACT - search for a proof term for EXTRACT~%")
  (format t "use NAMES - change the constants justify uses to try to build a proof term~%")
  (format t "unif+ - increase unification bounds~%")
  (format t "unif- - decrease unification bounds~%")
  (format t "all-claims - print all current claims~%")
  (format t "prove CLAIMNAME - enter scip (Scunak Interactive Prover) to prove CLAIMNAME.~%")
  (format t "tutor CLAIMNAME - enter tutor with claim~%")
  (format t "tutor (CLAIMNAME BVARS) - enter tutor with claim applied to bvars~%")
  (format t "tutor-student-usable NAME ... NAME. - indicate explicitly which signature elements are usable by the student and tutor~%")
  (format t "tutor-only-usable NAME ... NAME. - indicate explicitly which signature elements are usable by the tutor only~%")
  (format t "input-sig-agent \"MACHINE\" \"PORTNUM\"[ \"INFO\"] - input a signature from a remote agent~%")
  (format t "output-sig-agent \"MACHINE\" \"PORTNUM\"[ \"INFO\"[ \"BEGINTIMESTAMP\"[ \"ENDTIMESTAMP\"]]]. - output signature to a remote agent~%")
  (format t "add-fill-gap-agent NAME \"MACHINE\" \"PORTNUM\" - add a remote agent for filling gaps~%")
  (format t "add-fill-gap-agent-usable NAME \"MACHINE\" \"PORTNUM\" - add a remote agent for filling gaps with an explicit usable set~%")
  (format t "remove-fill-gap-agent NAME - remove a remote agent for filling gaps~%")
  (format t "q - quit~%")
  (format t "lisp - Enter a lisp S-expression to evaluate~%")
  (format t "help SYMBOL - print help message for SYMBOL~%")
  )

(defun scu-out (s)
  (when (and *scunak-socket* (open-stream-p *scunak-socket*))
    (format *scunak-socket* "~S~%" s)
    (force-output *scunak-socket*)))

(defun s-probe-file (f)
  (or (probe-file f)
      (and *scunak-main-dir*
	   (probe-file (format nil "~d/~d" *scunak-main-dir* f)))))

(defun s-load (f)
  (if (probe-file f)
      (load f)
    (if (and *scunak-main-dir*
	     (probe-file (format nil "~d/~d" *scunak-main-dir* f)))
	(load (format nil "~d/~d" *scunak-main-dir* f))
      nil)))
