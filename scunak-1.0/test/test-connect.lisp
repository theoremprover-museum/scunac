(setq pass (acl-socket:make-socket :connect :passive))
(setq passport (acl-socket:local-port pass))

(defun scunak-connect-acl (args)
  (format t "Socket : ~d~%" pass)
  (format t "*** Test scunak-acl socket~%")
  (excl:run-shell-command (format nil "scunak-acl ~d -m 0 -s ~d -n Chad &" args passport))
  (setq a (acl-socket:accept-connection pass))
  (setq b (acl-socket:accept-connection pass))
  (mp:process-run-function "b" #'read-b)
  (read-a-to-ready)
  )

(defun scunak-connect-clisp (args)
  (format t "Socket : ~d~%" pass)
  (format t "*** Test scunak-clisp socket~%")
  (excl:run-shell-command (format nil "scunak-clisp ~d -m 0 -s ~d &" args passport))
  (setq a (acl-socket:accept-connection pass))
  (setq b (acl-socket:accept-connection pass))
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
	      (format t "B: ~d~%" r)
	    (progn
	      (close b)
	      )))))

(defun read-a-to-ready (&optional expected unexpected)
  (do ((r (read a nil nil) (read a nil nil)))
      ((or (member r '(READY READY-TUTOR READY-SCIP
			     PROMPT-BOOL
			     PROMPT-FILENAME
			     PROMPT-NAME
			     PROMPT-LINE
			     ))
	   (and (consp r) (eq (car r) 'PROMPT-NUM)))
       (format t "*A: ~S~%" r)
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
      (format t "A: ~d~%" r)))

(defun send-a (s &optional expected unexpected)
  (format t "Sending: ~S~%" s)
  (format a "~S~%" s)
  (force-output a)
  (read-a-to-ready expected unexpected)
  )

(defun send-a-line (s &optional expected unexpected)
  (format t "Sending Line: ~d~%" s)
  (format a "(LINE ~S)~%" s)
  (force-output a)
  (read-a-to-ready expected unexpected)
  )





