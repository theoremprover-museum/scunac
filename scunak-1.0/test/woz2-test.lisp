; Author: Chad E Brown
; June 2006
; Tests the woz2 problems about binary relations on a set M

(load "test-connect.lisp")

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
(send-a '(PROVE "woz2Ex"))
(send-a-line "M")
(send-a-line "R")
(send-a '(PPLAN))
(send-a '(INTRO) '(OK))
(send-a '(CLAIMTYPE (PI "x" "M" (PI "y" "M" ((PF (("kpair" "x" "y") IN "R")) -> (PF (("kpair" "x" "y") IN ("breln1inv" "M" ("breln1inv" "M" "R")))))))) '(OK))
(send-a '(APPLY ("subbreln1" "M" "R" ("breln1inv" "M" ("breln1inv" "M" "R")) "fact1")) '(OK))
(send-a '(PPLAN))
(send-a '(D) '(DONE-WITH-SUBGOAL))
(send-a-line "x")
(send-a-line "y")
(send-a '(CLEARLY (("kpair" "y" "x") IN ("breln1inv" "M" "R"))) '(CORRECT))
(send-a '(D) '(DONE-WITH-SUBGOAL))
(send-a '(CLAIMTYPE (PI "x" "M" (PI "y" "M" ((PF (("kpair" "x" "y") IN ("breln1inv" "M" ("breln1inv" "M" "R")))) -> (PF (("kpair" "x" "y") IN "R")))))) '(OK))
(send-a '(PPLAN))
(send-a '(APPLY ("subbreln1" "M" ("breln1inv" "M" ("breln1inv" "M" "R")) "R" "fact6")) '(OK))
(send-a '(D) '(DONE-WITH-SUBGOAL))
(send-a-line "x")
(send-a-line "y")
(send-a '(PPLAN))
(send-a '(WILLSHOW (("kpair" "y" "x") IN ("breln1inv" "M" "R"))) '(CORRECT))
(send-a '(D) '(DONE-WITH-SUBGOAL))
(send-a NIL)
(send-a NIL)
(send-a '(HELP "woz2Ex"))
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

(scunak-connect-acl "-k macu -p woz2-sm.lisp -f woz2-lemmas.pam woz2-claims.pam")
(woz2-test)
(scunak-connect-clisp "-k macu -p woz2-sm.lisp -f woz2-lemmas.pam woz2-claims.pam")
(woz2-test)
