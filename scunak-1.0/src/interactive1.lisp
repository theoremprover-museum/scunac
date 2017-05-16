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

; October 2005
; Chad E Brown

(defun read-extract1-prop (namedectx)
  (let* ((r (read-line))
	 (words (tokenize-str r))
	 (n (length words))
	 (ch (earley-parse-string 'EXTRACT r input1-grammar))
	 (res (chart-to-parse-trees words 0 n 'EXTRACT input1-grammar ch)))
    (if res
	(let ((pre-prop (car res)))
	  (multiple-value-bind
	   (prop info fail)
	   (normal-fill-in-blanks pre-prop (prop) *input1-state* namedectx)
	   (if (or info fail)
	       nil
	     (normalize (named-term-to-db-1 (mapcar #'car namedectx) prop)))))
      nil)))

(defun read-extract1 (namedectx)
  (read-extract1-0 namedectx (read-line)))

(defun read-extract1-0 (namedectx r)
  (let* ((words (tokenize-str r))
	 (n (length words))
	 (ch (earley-parse-string 'EXTRACT r input1-grammar))
	 (res (chart-to-parse-trees words 0 n 'EXTRACT input1-grammar ch)))
    (if res
	(let ((pre-ex (car res)))
	  (multiple-value-bind
	   (ex dtp info fail)
	   (extr-fill-in-blanks-1 pre-ex *input1-state* namedectx)
	   (if (or info fail)
	       nil
	     (values (normalize (named-term-to-db-1 (mapcar #'car namedectx) ex))
		     (normalize-type (named-type-to-db-1 (mapcar #'car namedectx) dtp))))))
      nil)))

(defun read-dtype1 (namedectx)
  (read-dtype1-0 namedectx (read-line)))

(defun read-dtype1-0 (namedectx r)
  (let* ((words (tokenize-str r))
	 (n (length words))
	 (ch (earley-parse-string 'DTYPE1 r input1-grammar))
	 (res (chart-to-parse-trees words 0 n 'DTYPE1 input1-grammar ch)))
    (if res
	(let ((pre-tp (car res)))
	  (multiple-value-bind
	   (tp info fail)
	   (deptype-fill-in-blanks pre-tp *input1-state* namedectx)
	   (if (or info fail)
	       nil
	     (if (deptype1-p tp) ; check before switching to dbruijn indices
		 (normalize-type (named-type-to-db namedectx tp))
	       nil))))
      nil)))

(defun read-extract1-prop-sock (namedectx)
  (scu-out 'PROMPT-PROP)
  (let* ((res (read *scunak-socket* nil nil)))
    (if res
	(let ((pre-prop (input1l-preextr res)))
	  (multiple-value-bind
	   (prop info fail)
	   (normal-fill-in-blanks pre-prop (prop) *input1-state* namedectx)
	   (if (or info fail)
	       nil
	     (normalize (named-term-to-db-1 (mapcar #'car namedectx) prop)))))
      nil)))

(defun read-extract1-sock (namedectx)
  (scu-out 'PROMPT-EXTR)
  (read-extract1-0-sock namedectx (read *scunak-socket* nil nil)))

(defun read-extract1-0-sock (namedectx res)
  (if res
      (let ((pre-ex (input1l-preextr res)))
	(multiple-value-bind
	 (ex dtp info fail)
	 (extr-fill-in-blanks-1 pre-ex *input1-state* namedectx)
	 (if (or info fail)
	     nil
	   (values (normalize (named-term-to-db-1 (mapcar #'car namedectx) ex))
		   (normalize-type (named-type-to-db-1 (mapcar #'car namedectx) dtp))))))
    nil))

(defun read-dtype1-sock (namedectx)
  (scu-out 'PROMPT-DTYPE)
  (read-dtype1-0-sock namedectx (read *scunak-socket* nil nil)))

(defun read-dtype1-0-sock (namedectx res)
  (if res
      (let ((pre-tp (input1l-predtype res)))
	(multiple-value-bind
	 (tp info fail)
	 (deptype-fill-in-blanks pre-tp *input1-state* namedectx)
	 (if (or info fail)
	     nil
	   (if (deptype1-p tp) ; check before switching to dbruijn indices
	       (normalize-type (named-type-to-db namedectx tp))
	     nil))))
    nil))

(defun iprove (trm fill-constraints unif-constraints usable-rules usable-class-rules)
  (let ((fail nil)
	(theta nil)
	(changed nil))
    (loop while (and (not fail) (or fill-constraints unif-constraints)) do
	  (multiple-value-setq
	   (fail changed fill-constraints unif-constraints theta)
	   (simplify-constraints fill-constraints unif-constraints))
	  (unless fail
	    (if changed
		(progn
		  (when theta
		    (setq trm (normalize (simul-subst theta trm)))
		    (setq theta nil)))
	      (if fill-constraints
		  (let* ((locctx (caar fill-constraints))
			 (ftrm (cadar fill-constraints))
			 (evar (term-app-head ftrm))
			 (dtp (caddar fill-constraints))
			 (supp (cadddr (car fill-constraints)))
			 (options
			  (generate-pf-rule-options dtp usable-rules usable-class-rules supp locctx)))
		    (if options
			(let ((cmd (iprove-read-cmd)))
			  (cond ((string= cmd "pstatus")
				 (format t "Subgoals:~%")
				 (let ((i 0))
				   (format t "(Current) ~d : ~d~%" evar (output1-type-string dtp))
				   (dolist (ft (cdr fill-constraints))
				     (format t "~d ~d : ~d~%" (incf i) (cadr ft) (output1-type-string (caddr ft))))))
				((string= cmd "pgoal")
				 (format t "Goal : ~d~%" (output1-type-string dtp)))
				((string= cmd "pplan")
				 (format t "Goal : ~d~%" (output1-type-string dtp))
				 (when supp
				   (format t "Support:~%")
				   (dolist (s supp)
				     (format t "~d : ~d~%" (output1-normal-string (car s)) (output1-type-string (cadr s))))))
				((string= cmd "q")
				 (setq fail "User Aborted"))
				((or (string= cmd "choose-subgoal") (string= cmd "csg"))
				 (format t "Enter a number between 0 and ~d~%" (- (length fill-constraints) 1))
				 (let ((z (read)))
				   (if (and (numberp z) (nth z fill-constraints))
				       (let ((y (nth z fill-constraints)))
					 (setq fill-constraints (cons y (remove y fill-constraints))))
				     (format t "Subgoal Unchanged: ~d is not a number between 0 and ~d~%" z (- (length fill-constraints) 1)))))
				((string= cmd "b?")
				 (format t "Options:~%")
				 (let ((i -1))
				   (dolist (op options)
				     (format t "~d ~d~%" (incf i) (output1-type-string (car op))))))
				((string= cmd "b")
				 (format t "Enter a number between 0 and ~d~%" (- (length options) 1))
				 (let ((z (read)))
				   (if (and (numberp z) (nth z options))
				       (let ((op (nth z options)))
					 (setq trm (cadr op))
					 (setq fill-constraints (caddr op))
					 (setq unif-constraints (cadddr op))
					 )
				     (format t "No Action: ~d is not a number between 0 and ~d~%" z (- (length options) 1)))))
				(t nil)))
		      (setq fail (format nil "No option for filling type~%~S~%"
					 dtp)))
		    (fail "Sorry - I haven't handled interactive unif yet" trm unif-constraints))))))
    (if fail
	(values trm fail)
      trm)))
  
(defun iprove-read-cmd (&optional (prompt ">"))
  (format t "~d" prompt)
  (do ((r (read-line) (read-line))) 
      ((not (equal r ""))
       r)))


; dtp returns a pf type
(defun generate-pf-rule-options (dtp usable-rules usable-class-rules supp locctx)
  nil
					; ??????
  )

(defun simplify-term-type-pairs (mal &optional (ctx *emptyctx*) (skiptps nil))
  (let ((mal2 nil))
    (dolist (ma mal)
      (let ((m (car ma))
	    (a (cdr ma)))
	(unless (member a skiptps :test #'(lambda (x) (ctx-types-eq *emptyctx* x a)))
	  (let ((z (find-if #'(lambda (nb)
				(and (ctx-types-eq ctx a (cdr nb))
				     (ctx-terms-eq-type ctx m (car nb) a)))
			    mal2)))
	    (if z
		(when (< (termsize m) (termsize (car z)))
		  (setq mal2 (cons ma (remove z mal2))))
	      (push ma mal2))))))
    mal2))

(defun simplify-subgoal-list (sgl)
  (let ((sgl2 nil))
    (dolist (sg sgl)
      (let ((trm (car sg))
	    (evars (cadr sg)))
	(unless
	    (find-if #'(lambda (sg2)
			 (equal-global-tp-lists (mapcar #'cdr evars)
						(mapcar #'cdr (cadr sg2))))
		     sgl2)
	  (push sg sgl2))))
    sgl2))

(defun equal-global-tp-lists (tpl1 tpl2)
  (if tpl1
      (if tpl2
	  (and (ctx-types-eq *emptyctx* (car tpl1) (car tpl2))
	       (equal-global-tp-lists (cdr tpl1) (cdr tpl2)))
	nil)
    (if tpl2
	nil
      t)))

