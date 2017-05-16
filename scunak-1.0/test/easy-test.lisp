; Author: Chad E Brown
; June 2006
; Tests examples from the manual

(load "test-connect.lisp")

(defun easy-test ()
(send-a '(LET "A" OBJ))
(send-a '(LET "B" OBJ))
(send-a '(LET "C" OBJ))
(send-a '(justify ("A" <= ("A" CUP "B"))) '(JUSTIFICATION))
(send-a '(typeof ("binunionLsub" "A" "B")) '(TYPE))
(send-a '(justify ("B" <= ("A" CUP "B"))) '(JUSTIFICATION))
(send-a '(justify ("B" <= ("A" CUP ("B" CUP "C")))) '(COULD-NOT-JUSTIFY))
(send-a '(CLAIM ("myclaim" "A" "B" "C") (PF ("B" <= ("A" CUP ("B" CUP "C"))))))
(send-a '(prove "myclaim"))
(send-a-line "A")
(send-a-line "B")
(send-a-line "C")
(send-a '(pplan))
(send-a '(intro))
(send-a-line "x")
(send-a '(pplan))
(send-a '(clearly ("x" IN ("B" CUP "C"))) '(CORRECT))
(send-a '(pplan))
(send-a '(d) '(DONE-WITH-SUBGOAL SCIP-PFTERM))
(send-a t)
(send-a-line "")
(send-a t)
(send-a-line "")
(send-a '(help "myclaim") '(ABBREV))
(scunak-disconnect)
)

(scunak-connect-acl "-k f")
(easy-test)
(scunak-connect-clisp "-k f")
(easy-test)
