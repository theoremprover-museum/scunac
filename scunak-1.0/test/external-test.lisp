(load "test-connect.lisp")

(setq *socks* nil)
(setq *which* 0)

(defun fake-server ()
  (loop while t do
	(setq c (acl-socket:accept-connection pass))
	(incf *which*)
	(push c *socks*)
	(case *which*
	      (1
	       (setq r (read c nil nil))
	       (unless (equal r 'SCUNAK-INPUT)
		 (format t "Remote Input Problem 1a~%")
		 (break))
	       (setq info (read c nil nil))
	       (when info
		 (format t "Remote Input Problem 1b~%")
		 (break))
	       (format c "PAMELA~%")
	       (format c "~S~%" '(LET "x" OBJ))
	       (format c "~S~%" '(LET "y" OBJ))
	       (format c "~S~%" '(ABBREV ("noteq" "x" "y") PROP ("not" ("x" == "y"))))
	       (close c))
	      (2
	       (setq r (read c nil nil))
	       (unless (equal r 'SCUNAK-INPUT)
		 (format t "Remote Input Problem 2a~%")
		 (break))
	       (setq info (read c nil nil))
	       (unless (eq info 'INFO)
		 (format t "Remote Input Problem 2b~%")
		 (break))
	       (format c "LISP~%")
	       (format c "~S~%" '(newclaim '|notirrefl| (dpi (obj) (pf (app '|not| (app (app '|noteq| 0) 0))))))
	       (close c))
	      (3
	       (setq r (read c nil nil))
	       (unless (equal r 'SCUNAK-OUTPUT)
		 (format t "Remote Output Problem 3a ~S~%" r)
		 (break))
	       (setq info (read c nil nil))
	       (when info
		 (format t "Remote Output Problem 3b~%")
		 (break))
	       (format c "PAM~%")
	       (force-output c)
	       (format t "***** PAM Output:~%")
	       (do ((x (read-line c nil nil) (read-line c nil nil)))
		   ((null x))
		   (format t "~d~%" x))
	       (close c)
	       )
	      (4
	       (setq r (read c nil nil))
	       (unless (equal r 'SCUNAK-OUTPUT)
		 (format t "Remote Output Problem 4a~%")
		 (break))
	       (setq info (read c nil nil))
	       (unless (eq info 'INFO)
		 (format t "Remote Output Problem 4b~%")
		 (break))
	       (format c "LISP~%")
	       (force-output c)
	       (format t "***** LISP Output:~%")
	       (do ((x (read c nil nil) (read c nil nil)))
		   ((null x))
		   (format t "~d~%" x))
	       (close c)
	       )
	      (5
	       (setq r (read c nil nil))
	       (unless (equal r 'SCUNAK-OUTPUT)
		 (format t "Remote Output Problem 5a~%")
		 (break))
	       (setq info (read c nil nil))
	       (unless (eq info 'INFO2)
		 (format t "Remote Output Problem 5b~%")
		 (break))
	       (format c "LISP-PROPS~%")
	       (force-output c)
	       (format t "***** LISP-PROPS Output:~%")
	       (do ((x (read c nil nil) (read c nil nil)))
		   ((null x))
		   (format t "~d~%" x))
	       (close c)
	       )
	      (6
	       (setq r (read c nil nil))
	       (unless (eq r 'SCUNAK-FILL)
		 (format t "Remote Fill Problem 6a~%")
		 (break))
	       (mp:process-run-function "fga" #'(lambda (s) (fga1 s)) c))
	      (7
	       (setq r (read c nil nil))
	       (unless (eq r 'SCUNAK-FILL)
		 (format t "Remote Fill Problem 7a~%")
		 (break))
	       (mp:process-run-function "fga" #'(lambda (s) (fga2 s)) c))
	      (t
	       (format c "Unwritten Server Test Case")
	       (break)))))

(defun fga1 (s)
  (do ((r (read s nil nil) (read s nil nil)))
      ((null r) (close s))
      (when (and (consp r) (eq (car r) 'SCUNAK-FILL-REQUEST))
	(let ((ctx (cadr r))
	      (pftp (caddr r))
	      (alist (cdddr r)))
	  (format t "FGA1: ~S~%" r)
	  (if (and ctx (eq (car ctx) 'OBJ)
		   (equal pftp
			  '(PF APP |not| APP (APP |noteq| . 0) . 0)))
	      (format s "~S~%"
		      (list 'ANSWER
			    '(LAM APP (APP |notI| APP (APP |noteq| . 0) . 0) LAM APP
				  (APP (APP (APP |notE| APP (APP |eq| . 1) . 1) . |false|) APP |eqI|
				       . 1)
				  APP (APP (APP |noteq#U| . 1) . 1) . 0)))
	    (format s "(ANSWER NIL)~%"))
	  (force-output s)))))

(defun fga2 (s)
  (do ((r (read s nil nil) (read s nil nil)))
      ((null r) (close s))
      (when (and (consp r) (eq (car r) 'SCUNAK-FILL-REQUEST))
	(let* ((ctx (cadr r))
	       (pftp (caddr r))
	       (alist (cdddr r))
	       (usable (cdr (assoc 'usable alist))))
	  (format t "FGA2: ~S~%" r)
	  (if (and ctx (eq (car ctx) 'OBJ)
		     (equal pftp
			    '(PF APP |not| APP (APP |noteq| . 0) . 0)))
	      (progn
		(format s "~S~%" '(SIGELT "notI"))
		(force-output s)
		(let ((r2 (read s nil nil)))
		  (if (and (consp r2) (not (eq (car r2) 'UNKNOWN)))
		      (if (member '|notI| usable)
			  (format s "~S~%"
				  (list 'ANSWER
					'(LAM APP (APP |notI| APP (APP |noteq| . 0) . 0) LAM APP
					      (APP (APP (APP |notE| APP (APP |eq| . 1) . 1) . |false|) APP |eqI|
						   . 1)
					      APP (APP (APP |noteq#U| . 1) . 1) . 0)))
			(format s "~S~%"
				(list 'ANSWER
				      '(LAM APP (APP |notI| APP (APP |noteq| . 0) . 0) LAM APP
					    (APP (APP (APP |notE| APP (APP |eq| . 1) . 1) . |false|) APP |eqI|
						 . 1)
					    APP (APP (APP |noteq#F| . 1) . 1) . 0))))
		    (format s "(ANSWER NIL)~%"))))
	    (format s "(ANSWER NIL)~%"))
	  (force-output s)))))

(defun external-test ()
  (setq *socks* nil)
  (setq *which* 0)
  (setq proc (mp:process-run-function "c" #'fake-server))
  (send-a '(LISP (TRACE input1l-execute)))
  (send-a (list 'INPUT-SIG-AGENT "0" passport))
  (send-a '(HELP "noteq") '(ABBREV) nil)
  (send-a (list 'INPUT-SIG-AGENT "0" passport "INFO"))
  (send-a '(HELP "notirrefl") '(CLAIM) nil)
  (send-a '(PROVE "notirrefl"))
  (send-a-line "x")
  (send-a '(D) '(SUBGOAL-NOT-FINISHED))
  (send-a '(Q) '(PFTERM-HAS-FREES SCIP-OUT))
;  (send-a '(PROVE "notirrefl"))
;  (send-a-line "x")
;  (send-a '(D))
;  (send-a '(CLAIM ("not" ("not" ("x" == "x")))))
;  (send-a '(PSTATUS))
;  (send-a '(PPLAN))
;  (send-a '(D))
;  (send-a '(PPLAN))
;  (send-a '(D))
;  (send-a '(lisp (newclaim '|notirrefl| (dpi (obj) (pf (app '|not| (app (app '|noteq| 0) 0)))))))

  (send-a (list 'OUTPUT-SIG-AGENT "0" passport))
  (send-a (list 'OUTPUT-SIG-AGENT "0" passport "INFO" "450"))
  (send-a (list 'OUTPUT-SIG-AGENT "0" passport "INFO" 450))
  (send-a (list 'OUTPUT-SIG-AGENT "0" passport "INFO2" 450 470))

  (send-a (list 'ADD-FILL-GAP-AGENT 'FGA1 "0" passport))
  (send-a '(PROVE "notirrefl"))
  (send-a-line "x")
  (send-a '(D) '(DONE-WITH-SUBGOAL SCIP-PFTERM))
  (send-a nil)
  (send-a nil)
  (send-a '(HELP "notirrefl"))
  (send-a (list 'ADD-FILL-GAP-AGENT-USABLE 'FGA2 "0" passport))
  (send-a '(lisp (newclaim '|notirrefl| (dpi (obj) (pf (app '|not| (app (app '|noteq| 0) 0)))))))
  (send-a '(PROVE "notirrefl"))
  (send-a-line "x")
  (send-a '(D) '(DONE-WITH-SUBGOAL SCIP-PFTERM))
  (send-a nil)
  (send-a nil)
  (send-a '(HELP "notirrefl"))
  (send-a '(lisp (newclaim '|notirrefl| (dpi (obj) (pf (app '|not| (app (app '|noteq| 0) 0)))))))
  (send-a '(PROVE "notirrefl"))
  (send-a-line "x")
  (send-a '(USE "none"))
  (send-a '(D) '(DONE-WITH-SUBGOAL SCIP-PFTERM))
  (send-a nil)
  (send-a nil)
  (send-a '(HELP "notirrefl"))
  (send-a (list 'REMOVE-FILL-GAP-AGENT 'FGA1 "0" passport))
  (send-a '(lisp (newclaim '|notirrefl| (dpi (obj) (pf (app '|not| (app (app '|noteq| 0) 0)))))))
  (send-a '(PROVE "notirrefl"))
  (send-a-line "x")
  (send-a '(USE "notI"))
  (send-a '(D) '(DONE-WITH-SUBGOAL SCIP-PFTERM))
  (send-a nil)
  (send-a nil)
  (send-a '(HELP "notirrefl"))
  (send-a '(lisp (newclaim '|notirrefl| (dpi (obj) (pf (app '|not| (app (app '|noteq| 0) 0)))))))
  (send-a '(PROVE "notirrefl"))
  (send-a-line "x")
  (send-a '(USE "none"))
  (send-a '(D) '(SUBGOAL-NOT-FINISHED))
  (send-a '(Q) '(PFTERM-HAS-FREES SCIP-OUT))
  (send-a (list 'REMOVE-FILL-GAP-AGENT 'FGA2 "0" passport))

  (mp:process-kill proc)
  (scunak-disconnect)
  )

(scunak-connect-acl "-k mu")
(external-test)
(scunak-connect-clisp "-k mu")
(external-test)

