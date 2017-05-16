; Author: Chad E Brown
; June 2006
; Testing Scunak on examples in the manual

(setq pass (acl-socket:make-socket :connect :passive))
(setq passport (acl-socket:local-port pass))

(defun scunak-connect-acl (args)
  (format t "Socket : ~d~%" pass)
  (format t "*** Test scunak-acl socket~%")
  (excl:run-shell-command (format nil "scunak-acl ~d -m 0 -s ~d -n Chad &" args passport))
  (setq a (acl-socket:accept-connection pass))
  (setq b (acl-socket:accept-connection pass))
  (setq manual-test-file (open "manual-test-file" :direction :output :if-exists :supersede))
  (setq a-writing nil)
  (setq b-writing nil)
  (mp:process-run-function "b" #'read-b)
  (read-a-to-ready)
  )

(defun scunak-connect-clisp (args)
  (format t "Socket : ~d~%" pass)
  (format t "*** Test scunak-clisp socket~%")
  (excl:run-shell-command (format nil "scunak-clisp ~d -m 0 -s ~d &" args passport))
  (setq a (acl-socket:accept-connection pass))
  (setq b (acl-socket:accept-connection pass))
  (setq manual-test-file (open "manual-test-file-clisp" :direction :output :if-exists :supersede))
  (setq a-writing nil)
  (setq b-writing nil)
  (mp:process-run-function "b" #'read-b)
  (read-a-to-ready)
  )

(defun scunak-disconnect ()
  (format a "Q~%")
  (force-output a)
  (close a)
  )

(defun read-b ()
  (loop while (and (streamp b) (open-stream-p b)) do
	(let ((r (read-line b nil nil)))
	  (if r
	      (progn
		(loop while a-writing do
		      (sleep 1))
		(setq b-writing t)
		(format manual-test-file "{\\bf B} sends & \\verb+~d+ \\\\~%" r)
		(setq b-writing nil)
		)
	    (progn
	      (close b)
	      (close manual-test-file)
	      )))))

(defun read-a-to-ready (&optional expected unexpected)
  (do ((r (read a nil nil) (read a nil nil)))
      ((member r '(READY READY-TUTOR READY-SCIP
			 PROMPT-BOOL
			 PROMPT-FILENAME
			 PROMPT-NAME
			 PROMPT-NUM
			 ))
       (loop while b-writing do
	     (sleep 1))
       (setq a-writing t)
       (format manual-test-file "{\\bf A} sends & \\verb+~S+ \\\\~%\\end{tabular}~%\\begin{tabular}{ll}~%" r)
       (setq a-writing nil)
       (when expected
	 (format t "*** EXPECTED: ~d~%" expected)
	 (break)))
      (if (consp r)
	  (when (member (car r) unexpected)
	    (format t "*** UNEXPECTED: ~d~%" r)
	    (break))
	(when (member r unexpected)
	  (format t "*** UNEXPECTED: ~d~%" r)
	  (break)))
      (if (consp r)
	  (when (member (car r) expected)
	    (setq expected (remove (car r) expected)))
	(when (member r expected)
	  (setq expected (remove r expected))))
      (loop while b-writing do
	    (sleep 1))
      (setq a-writing t)
      (format manual-test-file "{\\bf A} sends & \\verb+~S+ \\\\~%" r)
      (setq a-writing nil)
      (format t "A: ~d~%" r)))

(defun send-a (s &optional expected unexpected)
  (format t "Sending: ~S~%" s)
  (format a "~S~%" s)
  (force-output a)
  (loop while b-writing do
	(sleep 1))
  (setq a-writing t)
  (format manual-test-file "{\\bf A} gets & \\verb+~S+ \\\\~%" s)
  (setq a-writing nil)
  (read-a-to-ready expected unexpected)
  )

(defun send-a-line (s &optional expected unexpected)
  (send-a (list 'LINE s) expected unexpected))

(defun manual-test ()
  (send-a '(TUTOR-AUTO-BACK "setextsub"))
  (send-a '(TUTOR-STUDENT-USABLE "notE" "contradiction" "subsetI1" "subsetI2" "binintersectEL" "binintersectER" "binintersectI" "binunionIL" "binunionIR" "binunionE" "binunionCases" "emptysetsubset" "subsetemptysetimpeq"))
  (send-a '(LET "A" OBJ))
  (send-a '(LET "B" OBJ))
  (send-a '(tutor ("unionComm" "A" "B")))
  (send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN ("A" CUP "B"))) '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("x" IN "B")) '(NOT-OK) '(OK))
  (send-a '(CLEARLY ("x" IN ("B" CUP "A"))) '(OK) '(NOT-OK))
  (send-a '(QED) '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN "A")) '(NOT-OK) '(OK))
  (send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
  (send-a '(QED) '(OK) '(NOT-OK))
  (send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN ("A" CUP "B"))) '(NOT-OK) '(OK))
  (send-a '(ASSUME ("x" IN ("B" CUP "A"))) '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
  (send-a '(QED) '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (scunak-disconnect)
)
(scunak-connect-acl "-k macu -p bool-props-sets-sm -f setrules.pam bool-props-sets.pam")
(manual-test)
(scunak-connect-clisp "-k macu -p bool-props-sets-sm -f setrules.pam bool-props-sets.pam")
(manual-test)

