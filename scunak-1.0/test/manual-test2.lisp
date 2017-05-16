; Author: Chad E Brown
; June 2006
; Testing Scunak on examples in the manual

(load "test-connect.lisp")

(defun manual-test2 ()
  (send-a '(PROVE "unionintersectDist2"))
  (send-a-line "X")
  (send-a-line "Y")
  (send-a-line "Z")
  (send-a '(PPLAN))
  (send-a '(INTRO))
  (send-a '(PPLAN))
  (send-a '(PSTATUS))
  (send-a '(CHOOSE-TASK))
  (send-a 1)
  (send-a '(PSTATUS))
  (send-a '(PPLAN))
  (send-a '(INTRO))
  (send-a-line "a")
  (send-a '(PPLAN))
  (send-a '(CLEARLY ("a" IN ("X" CUP "Y"))) '(CORRECT))
  (send-a '(CLEARLY (("a" IN "X") OR ("a" IN "Y"))) '(CORRECT))
  (send-a '(PPLAN))
  (send-a '(CASES))
  (send-a '(PPLAN))
  (send-a '(PSTATUS))
  (send-a '(D))
  (send-a '(PPLAN))
  (send-a '(CLEARLY ("a" IN ("X" CUP "Z"))) '(CORRECT))
  (send-a '(PPLAN))
  (send-a '(CLEARLY (("a" IN "X") OR ("a" IN "Z"))) '(CORRECT))
  (send-a '(PPLAN))
  (send-a '(CASES))
  (send-a '(PPLAN))
  (send-a '(D))
  (send-a '(PSTATUS))
  (send-a '(PPLAN))
  (send-a '(CLEARLY ("a" IN ("Y" CAP "Z"))) '(CORRECT))
  (send-a '(PPLAN))
  (send-a '(D))
  (send-a '(PSTATUS))
  (send-a '(PPLAN))
  (send-a '(INTRO))
  (send-a-line "a")
  (send-a '(CLEARLY (("a" IN "X") OR ("a" IN ("Y" CAP "Z")))) '(CORRECT))
  (send-a '(PPLAN))
  (send-a '(CASES))
  (send-a '(PPLAN))
  (send-a '(CLEARLY ("a" IN ("X" CUP "Y"))) '(CORRECT))
  (send-a '(CLEARLY ("a" IN ("X" CUP "Z"))) '(CORRECT))
  (send-a '(PPLAN))
  (send-a '(D))
  (send-a '(PSTATUS))
  (send-a '(CLEARLY ("a" IN "Y")) '(CORRECT))
  (send-a '(CLEARLY ("a" IN "Z")) '(CORRECT))
  (send-a '(PPLAN))
  (send-a '(CLEARLY ("a" IN ("X" CUP "Y"))) '(CORRECT))
  (send-a '(CLEARLY ("a" IN ("X" CUP "Z"))) '(CORRECT))
  (send-a '(D))
  (send-a T)
  (send-a-line "")
  (send-a T)
  (send-a-line "")
  (send-a '(HELP "unionintersectDist2") '(ABBREV))
  (scunak-disconnect)
)
(scunak-connect-acl "-k macu -f bool-props-sets.pam")
(manual-test2)
(scunak-connect-clisp "-k macu -f bool-props-sets.pam")
(manual-test2)

