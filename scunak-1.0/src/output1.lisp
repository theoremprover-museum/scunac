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
; November 2005/December 2005

; Outputs a signature in a format readable by input1

(defvar *output1-skip-snd* nil)

(defun output1-sig (names &optional (str t) (reset-names t))
  (setq *authors* nil)
  (when reset-names
    (setq *input1-ctx-info* nil))
  (let ((objvarnamenum -1)
	(propvarnamenum -1)
	(funcvarnamenum -1)
	(predvarnamenum -1)
	(pfvarnamenum -1)
	(rulevarnamenum -1))
    (declare (special objvarnamenum propvarnamenum funcvarnamenum
		      predvarnamenum 
		      pfvarnamenum rulevarnamenum))
    (dolist (z names)
      (unless (get z 'auto-gen)
	(output1-sig-1 z str)))))

(defun output1-sig-1 (z &optional (str t))
  (cond ((get z 'abbrev)
	 (multiple-value-bind
	  (bvars tp trm)
	  (output1-nctx-for-type-and-term (get z 'dbtype) (get z 'defn) str)
	  (if (equal (get z 'abbrev-type-authors)
		     (get z 'abbrev-defn-authors))
	      (progn
		(unless (equal *authors* (get z 'abbrev-type-authors))
		  (setq *authors* (get z 'abbrev-type-authors))
		  (format str "authors ~d!~%" (author-names)))
		(format str "~d~%" (output1-abbrev z tp trm bvars)))
	    (if (equal (get z 'abbrev-type-authors) '("AUTO"))
		(progn
		  (unless (equal *authors* (get z 'abbrev-defn-authors))
		    (setq *authors* (get z 'abbrev-defn-authors))
		    (format str "authors ~d!~%" (author-names)))
		  (format str "~d~%" (output1-abbrev-extr z trm bvars)))
	      (progn
		(unless (equal *authors* (get z 'abbrev-type-authors))
		  (setq *authors* (get z 'abbrev-type-authors))
		  (format str "authors ~d!~%" (author-names)))
		(format str "~d~%" (output1-claim z tp bvars))
		(unless (equal *authors* (get z 'abbrev-defn-authors))
		  (setq *authors* (get z 'abbrev-defn-authors))
		  (format str "authors ~d!~%" (author-names)))
		(format str "~d~%" (output1-abbrev-extr z trm bvars)))))))
	((get z 'const)
	 (multiple-value-bind
	  (bvars tp)
	  (output1-nctx-for-type (get z 'dbtype) str)
	  (unless (equal *authors* (get z 'const-authors))
	    (setq *authors* (get z 'const-authors))
	    (format str "authors ~d!~%" (author-names)))
	  (format str "~d~%" (output1-const z tp bvars))))
	((get z 'claim)
	 (multiple-value-bind
	  (bvars tp)
	  (output1-nctx-for-type (get z 'dbtype) str)
	  (unless (equal *authors* (get z 'claim-authors))
	    (setq *authors* (get z 'claim-authors))
	    (format str "authors ~d!~%" (author-names)))
	  (format str "~d~%" (output1-claim z tp bvars))))
	(t (format str "% Skipping ~d~%" z))))

(defun output1-const (name dtype &optional argvars)
  (if argvars
      (format nil "(~d ~d):~d." name
	      (output1-argvars argvars)
	      (output1-type-string dtype))
    (format nil "~d:~d." name
	    (output1-type-string dtype))))

(defun output1-claim (name dtype &optional argvars)
  (if argvars
      (format nil "(~d ~d):~d?" name 
	      (output1-argvars argvars)
	      (output1-type-string dtype))
    (format nil "~d:~d?" name
	    (output1-type-string dtype))))

(defun output1-abbrev (name dtype defn &optional argvars)
  (if argvars
      (format nil "(~d ~d):~d=~d." name 
	      (output1-argvars argvars)
	      (output1-type-string dtype nil)
	      (output1-normal-string defn nil t))
    (format nil "~d:~d=~d." name (output1-type-string dtype nil)
	    (output1-normal-string defn nil t))))

(defun output1-abbrev-extr (name defn &optional argvars)
  (if argvars
      (format nil "(~d ~d)=~d." name 
	      (output1-argvars argvars)
	      (output1-normal-string defn nil t))
    (format nil "~d=~d." name
	    (output1-normal-string defn nil t))))

(defun output1-argvars (argvars)
  (if argvars
      (if (cdr argvars)
	  (format nil "~d ~d"
		  (car argvars) (output1-argvars (cdr argvars)))
	(format nil "~d" (car argvars)))
    ""))

(defun author-names (&optional (authl *authors*))
  (if authl
      (if (cdr authl)
	  (format nil "\"~d\", ~d" (car authl)
		  (author-names (cdr authl)))
	(format nil "\"~d\"" (car authl)))
    "\"\""))

(defun output1-type-string (dtype &optional names parens)
  (case (deptype-case dtype)
	(DPI
	 (let ((x (format nil "x~d" (length names))))
	   (format nil "~d{~d:~d}~d~d"
		   (if parens "(" "")
		   x
		   (output1-type-string (dpi-dom dtype) names nil)
		   (output1-type-string (dpi-cod dtype) (cons x names) nil)
		   (if parens ")" ""))))
	(OBJ "obj")
	(PROP "prop")
	(PF (format nil "|- ~d"
		    (output1-extraction-string (pf-prop dtype) names t)))
	(DCLASS
	 (if (lam-p (dclass-pred dtype))
	     (let ((x (format nil "x~d" (length names))))
	       (format nil "{~d|~d}"
		       x
		       (output1-extraction-string (lam-body (dclass-pred dtype)) (cons x names) nil)))
	   (output1-extraction-string (dclass-pred dtype) names t)))
	(t (format nil "% error"))))

(defun output1-extractionl-string (extrl names)
  (if extrl
      (if (cdr extrl)
	  (format nil "~d ~d"
		  (output1-extraction-string (car extrl) names t)
		  (output1-extractionl-string (car extrl) names))
	(output1-extraction-string (car extrl) names t))
    (fail "bug - called output1-extractionl-string with empty list")))

(defun output1-normall-string (nl names)
  (if nl
      (if (cdr nl)
	  (format nil "~d ~d"
		  (output1-normal-string (car nl) names t)
		  (output1-normall-string (car nl) names))
	(output1-normal-string (car nl) names t))
    (fail "bug - called output1-normall-string with empty list")))

(defun output1-extraction-string (extr names parens)
  (cond ((enumerated-set-p extr)
	 (enumerated-set-to-string extr names))
	((setconstr-p extr)
	 (setconstr-to-string extr names))
	((dall-p extr)
	 (quant-to-string extr names "forall"))
	((dex-p extr)
	 (quant-to-string extr names "exists"))
	((infix-op-p extr)
	 (infix-op-to-string extr names))
	(t
	 (case (term-case extr)
	       (APP (format nil "~d~d ~d~d"
			    (if parens "(" "")
			    (output1-extraction-string (app-func extr) names nil)
			    (output1-normal-string (app-arg extr) names t)
			    (if parens ")" "")))
	       (FST (output1-extraction-string (fst-arg extr) names parens))
	       (SND (output1-extraction-string (snd-arg extr) names parens))
	       (DEBRUIJN (nth extr names))
	       (t
		(if (symbolp extr)
		    (cond ((constname-p extr)
			   (yellow-on-black-output (format nil "~d" extr)))
			  ((abbrevname-p extr)
			   (green-on-black-output (format nil "~d" extr)))
			  ((claimname-p extr)
			   (black-on-red-output (format nil "~d" extr)))
			  ((get extr 'evar)
			   (white-on-red-output (format nil "~d" extr)))
			  (t
			   (format nil "~d" extr)))
		  (format nil "~d" extr)))))))

(defun output1-normal-string (norm &optional names (parens t))
  (case (term-case norm)
	(LAM 
	 (let ((x (format nil "x~d" (length names))))
	   (format nil "~d\\~d~d"
		   (if parens "(" "")
		   (output1-lambda-string (lam-body norm) (format nil "~d" x) (cons x names))
		   (if parens ")" ""))))
	(PAIR
	 (if *output1-skip-snd*
	     (output1-extraction-string (pair-fst norm) names t)
	   (format nil "<~d,~d>"
		   (output1-extraction-string (pair-fst norm) names t)
		   (output1-extraction-string (pair-snd norm) names nil)
		   )))
	(t (output1-extraction-string norm names parens))))

(defun output1-lambda-string (norm bvarsstr names)
  (case (term-case norm)
	(LAM 
	 (let ((x (format nil "x~d" (length names))))
	   (output1-lambda-string (lam-body norm)
				  (format nil "~d ~d" bvarsstr x)
				  (cons x names))))
	(PAIR
	 (if *output1-skip-snd*
	     (format nil "~d.~d"
		     bvarsstr
		     (output1-extraction-string (pair-fst norm) names t))
	   (format nil "~d.<~d,~d>"
		   bvarsstr
		   (output1-extraction-string (pair-fst norm) names t)
		   (output1-extraction-string (pair-snd norm) names nil)
		   )))
	(t (format nil "~d.~d"
		   bvarsstr
		   (output1-extraction-string norm names nil)))))
  
(defun output1-nctx-for-type (tp str &optional bvars)
  (if (dpi-p tp)
      (let ((bvar (output1-nctx-bvar (dpi-dom tp) str bvars)))
	(multiple-value-bind
	 (bvars2 tp2)
	 (output1-nctx-for-type (dbsubst-type-0 (dpi-cod tp) bvar) str (cons bvar bvars))
	 (values (cons bvar bvars2) tp2)))
    (values nil tp)))

(defun output1-nctx-for-type-and-term (tp trm str &optional bvars)
  (if (dpi-p tp)
      (let ((bvar (output1-nctx-bvar (dpi-dom tp) str bvars)))
	(multiple-value-bind
	 (bvars2 tp2 trm2)
	 (output1-nctx-for-type-and-term (dbsubst-type-0 (dpi-cod tp) bvar)
					 (dbsubst-0 (gen-lam-body trm) bvar)
					 str
					 (cons bvar bvars))
	 (values (cons bvar bvars2) tp2 trm2)))
    (values nil tp trm)))

(defun output1-nctx-bvar (tp str used)
  (let ((a (find-if #'(lambda (x)
			(and (heq tp (cadar (cadr x)))
			     (not (member (car x) used))))
		    (reverse *input1-ctx-info*))))
    (if a
	(car a)
      (let ((bvarname (output1-next-bvar-name tp)))
	(format str "[~d:~d]~%" bvarname
		(output1-type-string tp))
	(input1-add-var-to-ctx bvarname tp)
	bvarname))))

(defun output1-next-bvar-name (tp)
  (declare (special objvarnamenum propvarnamenum funcvarnamenum
		    predvarnamenum 
		    pfvarnamenum rulevarnamenum))
  (if (dpi-p tp)
      (cond ((or (dtype-returns-obj-p tp)
		 (dtype-returns-dclass-p tp))
	     (nth-bvar-name
	      (incf funcvarnamenum)
	      '("f" "g" "h")))
	    ((dtype-returns-prop-p tp)
	     (nth-bvar-name
	      (incf predvarnamenum)
	      '("phi" "psi" "xi")))
	    (t ; ow, returns pf
	     (nth-bvar-name
	      (incf rulevarnamenum)
	      '("hypprem")))
	    )
    (cond ((or (dtype-returns-obj-p tp)
	       (dtype-returns-dclass-p tp))
	   (nth-bvar-name
	    (incf objvarnamenum)
	    '("y" "z" "u" "v" "w")))
	  ((dtype-returns-prop-p tp)
	   (nth-bvar-name
	    (incf predvarnamenum)
	    '("M" "N" "P" "Q")))
	  (t ; ow, pf
	   (nth-bvar-name
	    (incf pfvarnamenum)
	    '("prem"))))))

(defun nth-bvar-name (n pl)
  (if (cdr pl)
      (if (< n (length pl))
	  (intern (nth n pl))
	(intern (format nil "~d~d" (nth (mod n (length pl)) pl) (floor (- (/ n (length pl)) 1)))))
    (intern (format nil "~d~d" (car pl) n))))

(defun output1-trm-tp (trm tp)
  (let ((objvarnamenum -1)
	(propvarnamenum -1)
	(funcvarnamenum -1)
	(predvarnamenum -1)
	(pfvarnamenum -1)
	(rulevarnamenum -1))
    (declare (special objvarnamenum propvarnamenum funcvarnamenum
		      predvarnamenum 
		      pfvarnamenum rulevarnamenum))
  (multiple-value-bind
   (bvars tp trm)
   (output1-nctx-for-type-and-term tp trm t)
   (format t "Term: ~d~%Type: ~d~%"
	   (output1-normal-string trm bvars)
	   (output1-type-string tp bvars)))))

(defun output1-tp (tp)
  (let ((objvarnamenum -1)
	(propvarnamenum -1)
	(funcvarnamenum -1)
	(predvarnamenum -1)
	(pfvarnamenum -1)
	(rulevarnamenum -1))
    (declare (special objvarnamenum propvarnamenum funcvarnamenum
		      predvarnamenum 
		      pfvarnamenum rulevarnamenum))
  (multiple-value-bind
   (bvars tp)
   (output1-nctx-for-type tp t)
   (format t "Type: ~d~%"
	   (output1-type-string tp bvars)))))

(defun enumerated-set-p (extr)
  (or (eq extr '|emptyset|)
      (and (app-p extr) (app-p (app-func extr))
	   (eq (app-func (app-func extr)) '|setadjoin|)
	   (enumerated-set-p (app-arg extr)))))

(defun enumerated-set-to-string (es names)
  (if (eq es '|emptyset|)
      "{}"
    (format nil "{~d~d}"
	    (output1-extraction-string (app-arg (app-func es)) names nil)
	    (enumerated-set-to-string-1 (app-arg es) names))))

(defun enumerated-set-to-string-1 (es names)
  (if (eq es '|emptyset|)
      ""
    (format nil ",~d~d"
	    (output1-extraction-string (app-arg (app-func es)) names nil)
	    (enumerated-set-to-string-1 (app-arg es) names))))

(defun setconstr-p (extr)
  (and (app-p extr)
       (app-p (app-func extr))
       (eq (app-func (app-func extr)) '|dsetconstr|)))

(defun setconstr-to-string (extr names)
  (let ((x (format nil "x~d" (length names))))
    (format nil "{~d:~d|~d}"
	    x
	    (output1-extraction-string (app-arg (app-func extr)) names nil)
	    (output1-extraction-string (gen-lam-body (app-arg extr)) (cons x names) nil))))

(defun dall-p (extr)
  (and (app-p extr)
       (app-p (app-func extr))
       (eq (app-func (app-func extr)) '|dall|)))

(defun dex-p (extr)
  (and (app-p extr)
       (app-p (app-func extr))
       (eq (app-func (app-func extr)) '|dex|)))

(defun quant-to-string (extr names binder)
  (let ((x (format nil "x~d" (length names))))
    (format nil "(~d ~d:~d . ~d)"
	    binder x
	    (output1-extraction-string (app-arg (app-func extr)) names t)
	    (output1-extraction-string (gen-lam-body (app-arg extr)) (cons x names) t))))

(defun infix-op-p (extr)
  (and (app-p extr)
       (app-p (app-func extr))
       (member (app-func (app-func extr)) '(|in| |eq| |setadjoin| |and| |or| |imp| |equiv| |binunion| |binintersect| |cartprod| |kpair| |subset|))))

(defun infix-op-to-string (extr names)
  (case (app-func (app-func extr))
	(|in|
	 (format nil "(~d::~d)"
		 (output1-extraction-string (app-arg extr) names t)
		 (output1-extraction-string (app-arg (app-func extr)) names t)))
	(|eq|
	 (format nil "(~d==~d)"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(|setadjoin|
	 (format nil "(~d;~d)"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(|subset|
	 (format nil "(~d<=~d)"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(|and|
	 (format nil "(~d & ~d)"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(|or|
	 (format nil "(~d | ~d)"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(|imp|
	 (format nil "(~d => ~d)"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(|equiv|
	 (format nil "(~d <=> ~d)"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(|binunion|
	 (format nil "(~d \\cup ~d)"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(|binintersect|
	 (format nil "(~d \\cap ~d)"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(|cartprod|
	 (format nil "(~d \\times ~d)"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(|kpair|
	 (format nil "<<~d,~d>>"
		 (output1-extraction-string (app-arg (app-func extr)) names t)
		 (output1-extraction-string (app-arg extr) names t)))
	(t "% infix op unhandled case")))

	    
