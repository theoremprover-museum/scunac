; Author: Chad E Brown
; June 2006
; Tests the Injective Cantor Theorem problem as reported on at IJCAR 2006
; (Requires Vampire)

(setq *vampire-executable* "vampire-8.0")
(load "test-connect.lisp")

(scunak-connect-acl "-k ijcar2006")
(send-a '(VAMPIRE "injCantorThm") '(VAMPIRE-SUCCEEDED) '(VAMPIRE-FAILED NOT-A-PFCLAIM))
(scunak-disconnect)
(scunak-connect-clisp "-k ijcar2006")
(send-a '(VAMPIRE "injCantorThm") '(VAMPIRE-SUCCEEDED) '(VAMPIRE-FAILED NOT-A-PFCLAIM))
(scunak-disconnect)

