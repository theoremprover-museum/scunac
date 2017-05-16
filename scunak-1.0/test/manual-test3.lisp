; Author: Chad E Brown
; June 2006
; Testing Scunak on examples in the manual

(load "test-connect.lisp")

(defun manual-test3 ()
  (send-a '(help "false"))
  (send-a '(lisp (newconst '|false| (prop) '("Chad Edward Brown"))))
  (send-a '(help "false"))
  (send-a '(lisp
	    (newconst '|imp| (dpi (prop) (dpi (prop) (prop)))
		      '("Chad Edward Brown"))))
  (send-a '(lisp
	    (newabbrev '|not| (dpi (prop) (prop))
		       (lam (app (app '|imp| '0) '|false|))
		       '("Chad Edward Brown") '("Chad Edward Brown"))))
  (send-a '(help "not"))
  (send-a '(lisp
	    (newconst '|impI|
		      (dpi (prop)
			   (dpi (prop)
				(dpi (dpi (pf '1) (pf '1))
				     (pf (app (app '|imp| '2) '1)))))
		      '("Chad Edward Brown"))))
  (send-a '(lisp
	    (newconst '|impE|
		      (dpi (prop)
			   (dpi (prop)
				(dpi (pf (app (app '|imp| '1) '0))
				     (dpi (pf '2) (pf '2))))) '("Chad Edward Brown"))))
  (send-a '(lisp
	    (newabbrev '|notI|
		       (dpi (prop)
			    (dpi (dpi (pf '0) (pf '|false|))
				 (pf (app '|not| '1))))
		       (lam (lam (app (app '|not#F| '1)
				      (app (app (app '|impI| '1) '|false|) '0))))
		       '("Chad Edward Brown") '("Chad Edward Brown"))))
  (send-a '(lisp
	    (newclaim '|notE|
		      (dpi (prop)
			   (dpi (pf (app '|not| '0))
				(dpi (pf '1) (pf '|false|)))) '("Chad Edward Brown"))))
  (send-a '(help "notE"))
  (send-a '(lisp
	    (claim2abbrev '|notE| (lam (lam (app (app (app '|impE| '1) '|false|)
						 (app (app '|not#U| '1) '0))))
			  '("Chad Edward Brown"))))
  (send-a '(help "notE"))
  (scunak-disconnect)
)
(scunak-connect-acl "-k none")
(manual-test3)
(scunak-connect-clisp "-k none")
(manual-test3)

