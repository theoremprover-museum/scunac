; Author: Chad E Brown
; June 2006
; Runs Scunak on the woz1 and woz2 examples, generating tex description of socket interface


(setq pass (acl-socket:make-socket :connect :passive))
(setq passport (acl-socket:local-port pass))

(defun scunak-connect-acl (args)
  (format t "Socket : ~d~%" pass)
  (format t "*** Test scunak-acl socket~%")
  (excl:run-shell-command (format nil "scunak-acl ~d -m 0 -s ~d -n Chad &" args passport))
  (setq a (acl-socket:accept-connection pass))
  (setq b (acl-socket:accept-connection pass))
  (setq manual-test-file (open "manual-test-file" :direction :output :if-exists :append))
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
  (setq manual-test-file (open "manual-test-file-clisp" :direction :output :if-exists :append))
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
       (format manual-test-file "{\\bf A} sends & \\verb+~S+ \\\\~%\\end{tabular}\\~%\\begin{tabular}{ll}~%" r)
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

(defun woz1-test ()
  (send-a '(LET "U" OBJ))
  (send-a '(LET "A" ("powerset" "U")))
  (send-a '(LET "B" ("powerset" "U")))
  (send-a '(LET "C" ("powerset" "U")))
  (send-a '(LET "D" ("powerset" "U")))
  (send-a '(TUTOR-AUTO-BACK "setextsub" "orE" "powersetTI"))
  (send-a '(TUTOR-STUDENT-USABLE "notE" "xmcases" "eqI" "notI" "contradiction" "symeq" "transeq" "symtrans1eq" "symtrans2eq" "binunionT" "binintersectT" "powersetT" "setminusT" "complementT" "setextT" "subsetTI" "powersetTI" "powersetTE" "powersetTI1" "powersetTE1" "complementTI" "complementTE" "complementTI1" "complementTE1" "binintersectTEL" "binintersectTER" "binintersectTI" "binunionTE1" "binunionTE" "binunionTIL" "binunionTIR" "binintersectTELcontra" "binintersectTERcontra" "binunionTILcontra" "binunionTIRcontra" "binunionTEcontra" "demorgan1a" "demorgan2a" "demorgan2a1" "demorgan2a2" "demorgan1b" "demorgan2b2" "demorgan2b" "demorgan1" "demorgan2" "demorgan1Eq2" "demorgan2Eq2" "demorgan3Eq2" "demorgan4Eq2" "contrasubsetT" "contrasubsetT1" "binintersectTSub1" "binintersectTSub2" "binunionTSub1" "binunionTSub2" "impI" "impE" "woz13rule1" "woz13rule2" "woz13rule3" "doubleComplementSub1" "doubleComplementSub2" "doubleComplementEq" "subsetTrans"))
  (send-a '(TUTOR-ONLY-USABLE "woz13rule4"))
  (send-a '(TUTOR ("woz1_1" "U" "A" "B")))
  (send-a '(LET ("x") "U"))
  (send-a '(ASSUME ("x" IN ("complementT" "U" "A"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("not" ("x" IN "A"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("not" ("x" IN ("binintersectT" "U" "A" "B")))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (send-a '(TUTOR ("woz1_1" "U" "A" "B")))
  (send-a '(LET ("x") "U") '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN ("complementT" "U" "A"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("not" ("x" IN "A"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("not" ("x" IN ("binintersectT" "U" "A" "B")))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY (("complementT" "U" "A") <= ("complementT" "U" ("binintersectT" "U" "A" "B")))) '(NOT-OK) '(OK))
  (send-a '(CLEARLY ("x" IN ("complementT" "U" ("binintersectT" "U" "A" "B")))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY (("complementT" "U" "A") <= ("complementT" "U" ("binintersectT" "U" "A" "B")))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (send-a '(TUTOR ("woz1_2" "U" "A" "B" "C" "D")))
  (send-a '(CLEARLY (("complementT" "U" ("binintersectT" "U" ("binunionT" "U" "A" "B") ("binunionT" "U" "C" "D"))) == ("binunionT" "U" ("complementT" "U" ("binunionT" "U" "A" "B")) ("complementT" "U" ("binunionT" "U" "C" "D"))))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY (("complementT" "U" ("binunionT" "U" "A" "B"))==("binintersectT" "U" ("complementT" "U" "A") ("complementT" "U" "B")))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY (("complementT" "U" ("binunionT" "U" "C" "D"))==("binintersectT" "U" ("complementT" "U" "C") ("complementT" "U" "D")))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (send-a '(TUTOR ("woz1_3" "U" "A" "B" "C")))
  (send-a '(CLEARLY ("A" <= ("binunionT" "U" "A" "C"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("B" <= ("binunionT" "U" "B" "C"))) '(OK) '(NOT-OK))
  (send-a '(QED) '(NOT-OK) '(OK))
  (send-a '(CLEARLY (("binintersectT" "U" "A" "B") <= ("binintersectT" "U" ("binunionT" "U" "A" "C") ("binunionT" "U" "B" "C")))) '(NOT-OK DIAGNOSIS) '(OK))
  (send-a '(CLEARLY (("binintersectT" "U" "A" "B") <= ("binunionT" "U" "A" "C"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY (("binintersectT" "U" "A" "B") <= ("binunionT" "U" "B" "C"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY (("binintersectT" "U" "A" "B") <= ("binintersectT" "U" ("binunionT" "U" "A" "C") ("binunionT" "U" "B" "C")))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (send-a '(TUTOR ("woz1_4" "U" "A" "B")))
  (send-a '(ASSUME ("A" <= ("complementT" "U" "B"))) '(OK) '(NOT-OK))
  (send-a '(QED) '(NOT-OK) '(OK STUDENT-SUCCESSFUL EXIT-TUTOR))
  (send-a '(LET ("x") "U") '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("not" ("x" IN "A"))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (send-a '(TUTOR ("woz1_4" "U" "A" "B")))
  (send-a '(ASSUME ("A" <= ("complementT" "U" "B"))) '(OK) '(NOT-OK))
  (send-a '(LET ("x") "U") '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("not" ("x" IN "A"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("x" IN ("complementT" "U" "A"))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (send-a '(TUTOR ("woz1_5" "U" "A" "B")))
  (send-a '(LET ("x") "U") '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN ("complementT" "U" ("binunionT" "U" "A" "B")))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("not" ("x" IN ("binunionT" "U" "A" "B")))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("not" ("x" IN "A"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("x" IN ("complementT" "U" "A"))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (send-a '(TUTOR ("woz1_5" "U" "A" "B")))
  (send-a '(LET ("x") "U") '(OK) '(NOT-OK))
  (send-a '(ASSUME ("x" IN ("complementT" "U" ("binunionT" "U" "A" "B")))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("not" ("x" IN ("binunionT" "U" "A" "B")))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("not" ("x" IN "A"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("x" IN ("complementT" "U" "A"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY (("complementT" "U" ("binunionT" "U" "A" "B")) <= ("complementT" "U" "A"))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (send-a '(TUTOR-STUDENT-USABLE "woz1_4" "notE" "xmcases" "eqI" "notI" "contradiction" "symeq" "transeq" "symtrans1eq" "symtrans2eq" "binunionT" "binintersectT" "powersetT" "setminusT" "complementT" "setextT" "subsetTI" "powersetTI" "powersetTE" "powersetTI1" "powersetTE1" "complementTI" "complementTE" "complementTI1" "complementTE1" "binintersectTEL" "binintersectTER" "binintersectTI" "binunionTE1" "binunionTE" "binunionTIL" "binunionTIR" "binintersectTELcontra" "binintersectTERcontra" "binunionTILcontra" "binunionTIRcontra" "binunionTEcontra" "demorgan1a" "demorgan2a" "demorgan2a1" "demorgan2a2" "demorgan1b" "demorgan2b2" "demorgan2b" "demorgan1" "demorgan2" "demorgan1Eq2" "demorgan2Eq2" "demorgan3Eq2" "demorgan4Eq2" "contrasubsetT" "contrasubsetT1" "binintersectTSub1" "binintersectTSub2" "binunionTSub1" "binunionTSub2" "impI" "impE" "woz13rule1" "woz13rule2" "woz13rule3" "doubleComplementSub1" "doubleComplementSub2" "doubleComplementEq" "subsetTrans"))
  (send-a '(TUTOR ("woz1_5" "U" "A" "B")))
  (send-a '(CLEARLY ("A" <= ("binunionT" "U" "A" "B"))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY (("binunionT" "U" "A" "B") <= ("complementT" "U" ("complementT" "U" ("binunionT" "U" "A" "B"))))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY ("A" <= ("complementT" "U" ("complementT" "U" ("binunionT" "U" "A" "B"))))) '(OK) '(NOT-OK))
  (send-a '(CLEARLY (("complementT" "U" ("binunionT" "U" "A" "B")) <= ("complementT" "U" "A"))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (scunak-disconnect)
)

(defun woz2-test ()
(send-a '(LET "M" OBJ))
(send-a '(LET "R" ("breln1" "M")))
(send-a '(LET "S" ("breln1" "M")))
(send-a '(LET "T" ("breln1" "M")))
(send-a '(TYPEOF ("woz2W" "M" "R")) '(TYPE))
(send-a '(TUTOR-AUTO-BACK "setextsub" "orE"))
(send-a '(TUTOR-STUDENT-USABLE "breln1invprop" "breln1inv" "breln1invI" "breln1invE" "breln1compprop" "breln1comp" "breln1compI" "breln1compE" "breln1unionprop" "breln1union" "breln1unionI" "breln1unionIL" "breln1unionIR" "breln1unionE" "breln1all" "subbreln1" "contradiction"))
(send-a '(TUTOR ("woz2Ex" "M" "R")))
(send-a '(LET ("x" "y")) '(NOT-OK) '(OK))
(send-a '(LET ("x" "y") "M") '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN "R")) '(OK) '(NOT-OK))
(send-a '(QED) '(NOT-OK) '(OK))
(send-a '(CLEARLY (("kpair" "x" "y") IN ("breln1inv" "M" "R"))) '(NOT-OK) '(OK))
(send-a '(CLEARLY (("kpair" "y" "x") IN ("breln1inv" "M" "R"))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET ("x" "y") "M") '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN "R")) '(NOT-OK) '(OK))
(send-a '(ASSUME (("kpair" "x" "y") IN ("breln1inv" "M" ("breln1inv" "M" "R")))) '(OK) '(NOT-OK))
(send-a '(WILLSHOW (("kpair" "y" "x") IN ("breln1inv" "M" "R"))) '(OK) '(NOT-OK))
(send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(TUTOR ("woz2Ex" "M" "R")))
(send-a '(LET ("x" "y") "M") '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN ("breln1inv" "M" ("breln1inv" "M" "R")))) '(OK) '(NOT-OK))
(send-a '(HENCE (("kpair" "y" "x") IN ("breln1inv" "M" "R"))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET ("u" "v") "M") '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "u" "v") IN "R")) '(OK) '(NOT-OK))
(send-a '(QED) '(NOT-OK) '(OK))
(send-a '(HENCE (("kpair" "y" "x") IN ("breln1inv" "M" "R"))) '(NOT-OK) '(OK))
(send-a '(HENCE (("kpair" "v" "u") IN ("breln1inv" "M" "R"))) '(OK) '(NOT-OK))
(send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(TUTOR ("woz2Ex" "M" "R")))
(send-a '(LET ("x" "y") "M") '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN ("breln1inv" "M" ("breln1inv" "M" "R")))) '(OK) '(NOT-OK))
(send-a '(WILLSHOW (("kpair" "y" "x") IN ("breln1inv" "M" "R"))) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "y" "x") IN ("breln1inv" "M" "R"))) '(OK) '(NOT-OK))
(send-a '(LET ("x" "y") "M") '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN "R")) '(OK) '(NOT-OK))
(send-a '(WILLSHOW (("kpair" "y" "x") IN ("breln1inv" "M" "R"))) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "y" "x") IN ("breln1inv" "M" "R"))) '(OK) '(NOT-OK))
(send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(TUTOR ("woz2W" "M" "R" "S")))
(send-a '(LET ("x" "y") "M") '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN ("breln1inv" "M" ("breln1comp" "M" "R" "S")))) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "y" "x") IN ("breln1comp" "M" "R" "S"))) '(OK) '(NOT-OK))
(send-a '(EXISTS "z" "M" ((("kpair" "y" "z") IN "R") & (("kpair" "z" "x") IN "S"))) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "z" "y") IN ("breln1inv" "M" "R"))) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "x" "z") IN ("breln1inv" "M" "S"))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET ("x" "y") "M") '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN ("breln1comp" "M" ("breln1inv" "M" "S") ("breln1inv" "M" "R")))) '(OK) '(NOT-OK))
(send-a '(EXISTS "z" "M" ((("kpair" "x" "z") IN ("breln1inv" "M" "S")) & (("kpair" "z" "y") IN ("breln1inv" "M" "R")))) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "z" "x") IN "S")) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "y" "z") IN "R")) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "y" "x") IN ("breln1comp" "M" "R" "S"))) '(OK) '(NOT-OK))
(send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(TUTOR-STUDENT-USABLE "woz2W" "woz2Ex" "breln1invprop" "breln1inv" "breln1invI" "breln1invE" "breln1compprop" "breln1comp" "breln1compI" "breln1compE" "breln1unionprop" "breln1union" "breln1unionI" "breln1unionIL" "breln1unionIR" "breln1unionE" "breln1all" "subbreln1" "contradiction"))
(send-a '(TUTOR ("woz2A" "M" "R" "S" "T")))
(send-a '(LET ("x" "y") "M") '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN ("breln1comp" "M" ("breln1union" "M" "R" "S") "T"))) '(OK) '(NOT-OK))
(send-a '(EXISTS "z" "M" ((("kpair" "x" "z") IN ("breln1union" "M" "R" "S")) & (("kpair" "z" "y") IN "T"))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ((("kpair" "x" "z") IN "R") OR (("kpair" "x" "z") IN "S"))) '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "z") IN "R")) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "x" "y") IN ("breln1comp" "M" "R" "T"))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "z") IN "S")) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "x" "y") IN ("breln1comp" "M" "S" "T"))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET ("x" "y") "M") '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN ("breln1union" "M" ("breln1comp" "M" "R" "T") ("breln1comp" "M" "S" "T")))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ((("kpair" "x" "y") IN ("breln1comp" "M" "R" "T")) OR (("kpair" "x" "y") IN ("breln1comp" "M" "S" "T")))) '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN ("breln1comp" "M" "R" "T"))) '(OK) '(NOT-OK))
(send-a '(EXISTS "z" "M" ((("kpair" "x" "z") IN "R") & (("kpair" "z" "y") IN "T"))) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "x" "z") IN ("breln1union" "M" "R" "S"))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME (("kpair" "x" "y") IN ("breln1comp" "M" "S" "T"))) '(OK) '(NOT-OK))
(send-a '(EXISTS "z" "M" ((("kpair" "x" "z") IN "S") & (("kpair" "z" "y") IN "T"))) '(OK) '(NOT-OK))
(send-a '(CLEARLY (("kpair" "x" "z") IN ("breln1union" "M" "R" "S"))) '(OK) '(NOT-OK))
(send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(TUTOR-STUDENT-USABLE "breln1unionCommutes" "woz2A" "woz2W" "woz2Ex" "breln1invprop" "breln1inv" "breln1invI" "breln1invE" "breln1compprop" "breln1comp" "breln1compI" "breln1compE" "breln1unionprop" "breln1union" "breln1unionI" "breln1unionIL" "breln1unionIR" "breln1unionE" "breln1all" "subbreln1" "contradiction"))
(send-a '(TUTOR ("woz2B" "M" "R" "S" "T")))
(send-a '(CLEARLY
 (("breln1comp" "M" ("breln1union" "M" "R" "S") "T") ==
  ("breln1union" "M" ("breln1comp" "M" "R" "T")
   ("breln1comp" "M" "S" "T")))) '(OK) '(NOT-OK))
(send-a '(CLEARLY
 (("breln1comp" "M" "R" "T") ==
  ("breln1inv" "M" ("breln1inv" "M" ("breln1comp" "M" "R" "T"))))) '(OK) '(NOT-OK))
(send-a '(CLEARLY
 (("breln1comp" "M" "S" "T") ==
  ("breln1inv" "M" ("breln1inv" "M" ("breln1comp" "M" "S" "T"))))) '(OK) '(NOT-OK))
(send-a '(CLEARLY
 (("breln1comp" "M" ("breln1union" "M" "R" "S") "T") ==
  ("breln1union" "M"
   ("breln1inv" "M" ("breln1inv" "M" ("breln1comp" "M" "R" "T")))
   ("breln1inv" "M" ("breln1inv" "M" ("breln1comp" "M" "S" "T")))))) '(OK) '(NOT-OK))
(send-a '(CLEARLY
 (("breln1inv" "M" ("breln1comp" "M" "R" "T")) ==
  ("breln1comp" "M" ("breln1inv" "M" "T") ("breln1inv" "M" "R")))) '(OK) '(NOT-OK))
(send-a '(CLEARLY
 (("breln1inv" "M" ("breln1comp" "M" "S" "T")) ==
  ("breln1comp" "M" ("breln1inv" "M" "T") ("breln1inv" "M" "S")))) '(OK) '(NOT-OK))
(send-a '(CLEARLY
 (("breln1comp" "M" ("breln1union" "M" "R" "S") "T") ==
  ("breln1union" "M"
   ("breln1inv" "M"
    ("breln1comp" "M" ("breln1inv" "M" "T") ("breln1inv" "M" "R")))
   ("breln1inv" "M"
    ("breln1comp" "M" ("breln1inv" "M" "T") ("breln1inv" "M" "S")))))) '(OK) '(NOT-OK))
(send-a '(CLEARLY
 (("breln1union" "M"
   ("breln1inv" "M"
    ("breln1comp" "M" ("breln1inv" "M" "T") ("breln1inv" "M" "R")))
   ("breln1inv" "M"
    ("breln1comp" "M" ("breln1inv" "M" "T") ("breln1inv" "M" "S"))))
  ==
  ("breln1union" "M"
   ("breln1inv" "M"
    ("breln1comp" "M" ("breln1inv" "M" "T") ("breln1inv" "M" "S")))
   ("breln1inv" "M"
    ("breln1comp" "M" ("breln1inv" "M" "T") ("breln1inv" "M" "R")))))) '(OK) '(NOT-OK))
(send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (scunak-disconnect)
)


(scunak-connect-acl "-k macu -p woz1-sm.lisp -f woz1-lemmas.pam woz1-claims.pam")
(woz1-test)
(scunak-connect-acl "-k macu -p woz2-sm.lisp -f woz2-lemmas.pam woz2-claims.pam")
(woz2-test)

