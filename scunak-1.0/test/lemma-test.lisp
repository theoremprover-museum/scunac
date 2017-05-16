; Author: Chad E Brown
; July 2006
; Tests the Scip Lemma command

(load "test-connect.lisp")

(defun lemma-test ()
(send-a '(PROVE "bs114d"))
(send-a-line "A")
(send-a-line "B")
(send-a-line "C")
(send-a '(INTRO))
(send-a '(INTRO))
(send-a-line "x")
(send-a '(CLEARLY ("x" IN "A")) '(CORRECT))
(send-a '(CLEARLY (("x" IN "B") OR ("x" IN "C"))) '(COULD-NOT-JUSTIFY))
(send-a '(CLEARLY ("x" IN ("B" CUP "C"))) '(CORRECT))
(send-a '(CLEARLY (("x" IN "B") OR ("x" IN "C"))) '(CORRECT))
(send-a '(CASES))
(send-a '(LEMMA "mysetl1" ("x" "fact1" "ass0") (PF ("x" IN (("A" CAP "B") CUP ("A" CAP "C"))))) '(BAD-LEMMA-CTX))
(send-a '(LEMMA "mysetl1" ("A" "B" "C" "x" "fact1" "ass0") (PF ("x" IN (("A" CAP "B") CUP ("A" CAP "C"))))))
(send-a '(D) '(DONE-WITH-SUBGOAL))
(send-a '(LEMMA "mysetl2" ("A" "B" "C" "x" "fact1" "ass1") (PF ("x" IN (("A" CAP "B") CUP ("A" CAP "C"))))))
(send-a '(D) '(DONE-WITH-SUBGOAL))
(send-a '(CHKTERM) '(OK))
(send-a '(LEMMA "mysetl3" ("A" "B" "C") (PF ((("A" CAP "B") CUP ("A" CAP "C")) <= ("A" CAP ("B" CUP "C"))))))
(send-a '(D) '(DONE-WITH-SUBGOAL))
(send-a-line "")
(send-a-line "")
(send-a-line "")
(send-a-line "")
(send-a '(HELP "bs114d") '(ABBREV))
(send-a '(ALL-CLAIMS))
(scunak-disconnect)
)

(scunak-connect-acl "-f bs-1-1-4d.pam")
(lemma-test)
(scunak-connect-clisp "-f bs-1-1-4d.pam")
(lemma-test)