; Author: Chad E Brown
; June 2006
; Tests the proofreader as reported on in MKM 2006

(load "test-connect.lisp")

(defun proofread-test ()
(send-a '(LET "A" OBJ))
(send-a '(LET "B" OBJ))
(send-a '(LET "C" OBJ))
(send-a '(PROOFREAD "bs-justpf.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-SUCCESSFUL) '(PROOFREAD-FAILED PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-shorterpf.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-SUCCESSFUL) '(PROOFREAD-FAILED PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-shorterpf2.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-SUCCESSFUL) '(PROOFREAD-FAILED PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-badpf1.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-FAILED) '(PROOFREAD-SUCCESSFUL PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-badpf2.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-FAILED) '(PROOFREAD-SUCCESSFUL PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-badpf3.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-FAILED) '(PROOFREAD-SUCCESSFUL PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-badpf4.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-FAILED) '(PROOFREAD-SUCCESSFUL PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-badpf5.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-FAILED) '(PROOFREAD-SUCCESSFUL PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-badpf6.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-FAILED) '(PROOFREAD-SUCCESSFUL PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-badpf7.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-FAILED) '(PROOFREAD-SUCCESSFUL PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-badpf8.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-FAILED) '(PROOFREAD-SUCCESSFUL PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-badpf9.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-FAILED) '(PROOFREAD-SUCCESSFUL PROOFREAD-INCOMPLETE))
(send-a '(PROOFREAD "bs-incompletepf.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-INCOMPLETE) '(PROOFREAD-SUCCESSFUL PROOFREAD-FAILED))
(send-a '(PROOFREAD "bs-badincompletepf.tex" ("bs114d" "A" "B" "C")) '(PROOFREAD-FAILED) '(PROOFREAD-SUCCESSFUL PROOFREAD-INCOMPLETE))
(scunak-disconnect)
)

(scunak-connect-acl "-k mu -p bs-1-1-4d-mode.lisp -f bs-1-1-4d.pam")
(proofread-test)
(scunak-connect-clisp "-k mu -p bs-1-1-4d-mode.lisp -f bs-1-1-4d.pam")
(proofread-test)
