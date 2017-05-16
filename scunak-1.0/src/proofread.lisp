;   Scunak: A Mathematical Assistant System
;   Copyright (C) 2006 Chad E Brown (cebrown2323@yahoo.com)
;
;   This program is free software; you can redistribute it and/or modify
;   it under the terms of the GNU General Public License as published by
;   the Free Software Foundation; either version 2 of the License, or
;   (at your option) any later version.
;
;   This program is distributed in the hope that it will be useful,
;   but WITHOUT ANY WARRANTY; without even the implied warranty of
;   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;   GNU General Public License for more details.
;
;   You should have received a copy of the GNU General Public License along
;   with this program; if not, write to the Free Software Foundation, Inc.,
;   51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

; Author: Chad E Brown
; March 2006

(defvar *proofread-autoset-sig* nil)

(defun proofread (filename newapp)
  (let ((ctxi *input1-ctx-info*)
	(name (if (consp newapp) (car newapp) newapp))
	(expldeps (if (consp newapp) (cdr newapp) nil)))
    (multiple-value-bind
     (argctx failinfo)
     (varlist-to-ctx expldeps ctxi)
     (if failinfo
	 (format t "Did not understand: ~d~%" failinfo)
       (let ((app name))
	 (dolist (e expldeps)
	   (setq app (app app e)))
	 (let ((tp (ctx-extract-type *emptyctx* app)))
	   (if (dtype-returns-pf-p tp)
	       (proofread-0 filename tp argctx)
	     (format t "Given term does not have a proof type.~%"))))))))

(defun proofread-0 (infile tp namedectx)
  (let* ((names nil)
	 (ctx *emptyctx*)
	 (namesubst 'ID)
	 (dbtp nil))
    (setq *scip-gtp* tp)
    (do ((nec2 namedectx (cdr nec2)))
	((null nec2))
	(setq *scip-gtp* (dpi (cadar nec2)
			      (quick-db-type (caar nec2) 0 *scip-gtp*))))
    (dolist (ne (reverse namedectx))
      (setq ctx (ctx-cons (named-type-to-db-1 names (cadr ne)) ctx))
      (push (car ne) names)
      (setq namesubst (cons (car ne) (cons #'identity namesubst))))
    (setq dbtp (named-type-to-db-1 names tp))
    (setq *scip-usable* *sig-granularity-perfect*)
    (setq *scip-gevar* (intern-gensym))
    (setf (get *scip-gevar* 'evar) t)
    (setf (get *scip-gevar* 'dbtype) *scip-gtp*) ; ok to assign the type since gtp has no evars
    (setq *tutor-alts-stack* nil)
    (setq *tutor-alts* (post-process-tutor-alt
			(list (acons *scip-gevar* *scip-gevar* nil) ; theta (initially id)
			      (list (list *scip-gevar* ctx names dbtp namedectx namesubst))
			      ))) ; plans (first one focused)
    (setq *scip-assnum* -1)
    (setq *scip-factnum* -1)
    (proofread-1 infile)))
  
(defun proofread-1 (infile)
  (let ((ppp (pre-scunakate-proof infile))
	(done nil)
	(*student-stream* (make-string-output-stream))
	(*main-stream* (make-string-output-stream))
	(quit-command nil)
	(student-done nil)
	(res nil)
	(save-tas *tutor-autoset-sig*)
	)
    (declare (special quit-command student-done
		      scunakator~pds scunakator~method-store
		      *student-stream* *main-stream*))
    (when *proofread-autoset-sig* 
      (setq *tutor-autoset-sig* t)
      (setq *sig-granularity-perfect* nil)
      (tutor-increase-rules *scip-gtp*)
      )
    (when (> *verbose* 20) (proofread-comm "status."))
    (setq scunakator~pds (make-scunakator~pds :maingcat 'PROOF0))
    (loop until (or done student-done (not ppp)) do
	  (let ((ret
		 (scunakator-plan (scunakator~pds-maingcat scunakator~pds)
				   ppp scunakator~method-store)))
	    (if ret
		(let ((possannl (mapcar #'post-scunakate-scunakation
					(cadr ret))))
;		  (setq *ret* ret *ppp* ppp) (break) ; delete me
		  (if possannl
		      (if (cdr possannl)
			  (let ((str (format nil "alts")))
			    (dolist (p possannl)
			      (setq str (format nil "~d [~d]" str p)))
			    (proofread-comm str))
			(proofread-comm (car possannl)))
;		    (push-out (car ret))
		    nil
		    )
		  (setq res (get-output-stream-string *main-stream*))
		  (cond ((or (and (> (length res) 1) (string-equal res "OK" :start1 0 :end1 2))
			     (and (> (length res) 6) (string-equal res "Correct" :start1 0 :end1 7)))
			 (get-output-stream-string *student-stream*))
			(t
			 (scu-out (list 'PROOFREAD-FAILED res (stringify-charlist (car ret))))
			 (setq done 'FAILED)
			 (format t "~d~%Verification Problem:~%~d~%~d~%"
				 res
				 (stringify-charlist (car ret))
				 (get-output-stream-string *student-stream*))))
		  (when (> *verbose* 20) (proofread-comm "status."))
		  (setf (scunakator~pds-lastfactkey scunakator~pds)
			(scunakator~pds-nextfactkey scunakator~pds))
		  (setf (scunakator~pds-nextfactkey scunakator~pds) nil)
		  (setq ppp (caddr ret))
		  )
	      (let ((unpars (pop ppp)))
;		(push-out unpars)
		nil
		))))
;    (proofread-comm "qed.")
    (unless (eq done 'FAILED)
      (unless student-done
	(check-student-done))
      (if student-done
	  (progn
	    (format t "Proof successfully checked!~%")
	    (format t "Proof Term:~%~d~%"
		    (output1-normal-string student-done))
	    (scu-out (list 'PROOFREAD-SUCCESSFUL student-done))
	    )
	(progn
	  (scu-out 'PROOFREAD-INCOMPLETE)
	  (format t "File ended without completing proof.~%")
	  )))
    (close *student-stream*)
    (close *main-stream*)
    (setq *tutor-autoset-sig* save-tas)
    ))
  
(defun nl-tutor-1 ()
  (let ((done nil)
	(quit-command nil)
	(student-done nil)
	(r nil)
	(res nil)
	(save-tas *tutor-autoset-sig*)
	)
    (declare (special quit-command student-done
		      scunakator~pds scunakator~method-store
		      *student-stream* *main-stream*))
    (when *proofread-autoset-sig* 
      (setq *tutor-autoset-sig* t)
      (setq *sig-granularity-perfect* nil)
      (tutor-increase-rules *scip-gtp*)
      )
    (when (> *verbose* 20) (proofread-comm "status."))
    (setq scunakator~pds (make-scunakator~pds :maingcat 'PROOF0))
    (loop until (or (not *tutor-alts*) quit-command done student-done) do
	  (format *student-stream* "~d>" *student-name*)
	  (setq r (read-line))
	  (cond ((or (equal r "status") (equal r "status."))
		 (proofread-comm "status."))
		((or (equal r "q") (equal r "q.") (equal r "i give up") (equal r "i give up."))
		 (proofread-comm "i give up"))
		(t
		 (let* ((ppp 
			 (mapcar #'(lambda (x)
				     (if (eq x 'WH)
					 #\space
				       x))
				 (tokenize-str r)))
			(ret
			 (scunakator-plan (scunakator~pds-maingcat scunakator~pds)
					  ppp scunakator~method-store)))
;		  (setq *ret* ret *ppp* ppp) (break) ; delete me
		   (if ret
		       (let ((possannl (mapcar #'post-scunakate-scunakation
					       (cadr ret))))
			 (if possannl
;			     (if (cdr possannl)
;				 (let ((str (format nil "alts")))
;				   (dolist (p possannl)
;				     (setq str (format nil "~d [~d]" str p)))
;				   (proofread-comm str))
			       (proofread-comm (car possannl))
;			   )
					;		    (push-out (car ret))
			   nil
			   )
			 (when (> *verbose* 20) (proofread-comm "status."))
			 (setf (scunakator~pds-lastfactkey scunakator~pds)
			       (scunakator~pds-nextfactkey scunakator~pds))
			 (setf (scunakator~pds-nextfactkey scunakator~pds) nil)
			 )
		     (format t "Wie bitte?~%")
		     )))))
;    (proofread-comm "qed.")
    (unless (eq done 'FAILED)
      (unless student-done
	(check-student-done))
      (if student-done
	  (progn
	    (format *student-stream* "Congratulations, you're done with the proof, ~d!~%" *student-name*)
	    (format t "Successful Term:~%~d~%"
		    (output1-normal-string student-done)))
	(progn
	  (format *student-stream* "Okay, ~d, goodbye for now.~%" *student-name*))))))
  
(defun proofread-comm (r)
  (let* ((words (tokenize-str r))
	 (n (length words))
	 (ch (earley-parse-string 'PFCOMMAND r input1-grammar))
	 (res (chart-to-parse-trees words 0 n 'PFCOMMAND input1-grammar ch 1 nil 0)))
    (if res
	(let ((c (eval (car res)))
	      (prev *tutor-alts*))
	  (when (consp c)
	    (apply (car c) (cdr c))
	    )
	  (unless (equal *tutor-alts* prev)
	    (let ((talts *tutor-alts*))
	      (setq *tutor-alts* nil)
	      (dolist (talt talts)
		(setq *tutor-alts* (append *tutor-alts*
					   (post-process-tutor-alt talt))))))
	  )
;      (format *student-stream* "Sorry, ~d, but I got confused when you said~%~d~%" *student-name* words))
      nil) ; signal scunak bug?
    ))

(defun stringify-charlist (cl)
  (let ((str ""))
    (dolist (c cl)
      (setq str (format nil "~d~d" str c)))
    str))

