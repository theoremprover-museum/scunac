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
; October 02, 2005/Revised for Scunak December 5, 2005 (Jamaican code)

(defvar *direct-latex-separator* " ")
;(defvar *direct-latex-separator* " $ $ ")
(defun dtype-direct-latex (dtype &optional ctx parens)
  (case (deptype-case dtype)
	(OBJ "\\obj")
	(PROP "\\prop")
	(PF 
	 (format nil "~d\\pf ~d~d"
		 (if parens "(" "")
		 (term-direct-latex (pf-prop dtype) ctx t)
		 (if parens ")" "")
		 ))
	(DCLASS
	 (format nil "~d\\class ~d~d"
		 (if parens "(" "")
		 (term-direct-latex (dclass-pred dtype) ctx t)
		 (if parens ")" "")
		 ))
	(DPI
	 (let ((x (direct-latex-next-bvar-name (dpi-dom dtype) ctx
					       (dtype-n-used-as-set-p 0 (dpi-cod dtype))
					       )))
;	   (format nil "x~d" (length ctx))
	   (if (nintrm-type-p 0 (dpi-cod dtype))
	       (format nil "~d ~d\\Pi ~d:~d . ~d~d"
		       (if parens "(" "")
		       *direct-latex-separator*
		       x
		       (dtype-direct-latex (dpi-dom dtype) ctx t)
		       (dtype-direct-latex (dpi-cod dtype) (cons x ctx) nil)
		       (if parens ")" ""))
	       (format nil "~d ~d~d \\rightarrow ~d~d"
		       (if parens "(" "")
		       *direct-latex-separator*
		       (dtype-direct-latex (dpi-dom dtype) ctx t)
		       (dtype-direct-latex (dpi-cod dtype) (cons x ctx) nil)
		       (if parens ")" "")))))
	(t
;	 (fail "unknown dtype case making latex" dtype ctx)
	 (format nil "??~d??" dtype)
	 )))

(defun term-direct-latex (trm &optional ctx parens)
  (case (term-case trm)
	(LAM
	 (let ((x (format nil "x~d" (length ctx))))
	   (format nil "~d ~d\\lambda ~d ~d~d"
		   (if parens "(" "")
		   *direct-latex-separator*
		   x
		   (term-direct-latex (lam-body trm) (cons x ctx) nil)
		   (if parens ")" ""))))
	(APP
	 (format nil "~d~d ~d ~d~d"
		 (if parens "(" "")
		 (term-direct-latex (app-func trm) ctx nil)
		 *direct-latex-separator*
		 (term-direct-latex (app-arg trm) ctx t)
		 (if parens ")" "")))
	(FST (format nil "\\pi_1(~d)" (term-direct-latex (fst-arg trm) ctx nil)))
	(SND (format nil "\\pi_2(~d)" (term-direct-latex (snd-arg trm) ctx nil)))
	(PAIR (format nil "\\langle ~d, ~d\\rangle" 
		      (term-direct-latex (pair-fst trm) ctx nil)
		      (term-direct-latex (pair-snd trm) ctx nil)))
	(DEBRUIJN (nth trm ctx))
	(t
	 (if (symbolp trm)
	     (cond ((get trm 'const)
		    (format nil "{\\mbox{\\tt ~d}}"
			    (name-to-latex-string trm)))
		   ((get trm 'abbrev)
		    (format nil "{\\mbox{\\tt ~d}}" ; was bf
			    (name-to-latex-string trm)))
		   ((get trm 'claim)
		    (format nil "{\\mbox{\\tt ~d}}" ; was cal
			    (name-to-latex-string trm)))
		   (t
		    (format nil "{\\mbox{ ~d}}"
			    (name-to-latex-string trm))))
;	   (fail "Unknown trm case making latex" trm ctx)
	   (format nil "??~d??" trm)
	   ))))

(defun termlist-direct-latex (trml &optional ctx)
  (if (cdr trml)
      (format nil "~d,~d"
	      (term-direct-latex (car trml) ctx nil)
	      (termlist-direct-latex (cdr trml) ctx))
    (term-direct-latex (car trml) ctx nil)))

(defun name-to-latex-string (name)
  (let ((str (format nil "~d" name))
	(ret ""))
    (dotimes (i (length str) ret)
      (let ((c (aref str i)))
	(if (latex-char-needs-escape-p c)
	    (setq ret (format nil "~d\\~d" ret c))
	  (setq ret (format nil "~d~d" ret c)))))))

(defun nd-rule-dbtype-c (name)
  (let ((paramnames '("x" "y" "z"))
	(pfnames '("u" "v" "w"))
	(cobjnames '("a" "b" "c" "d"))
	(objnames '("A" "B" "C" "D"))
	(propnames '("P" "Q" "R"))
	(objfnnames '("F" "G" "H" "K"))
	(cobjfnnames '("f" "g" "h" "k"))
	(propfnnames '("\\phi" "\\psi" "\\chi")))
    (declare (special paramnames pfnames cobjnames objnames propnames objfnnames cobjfnnames propfnnames))
    (nd-rule-dbtype name (get name 'dbtype))))

(defun nd-rule-get-name (tp)
  (declare (special pfnames cobjnames objnames propnames objfnnames cobjfnnames propfnnames))
  (cond ((dtype-returns-pf-p tp)
	 (if pfnames
	     (pop pfnames)
	   (format nil "~d" (intern-gensym "PF"))))
	((obj-p tp)
	 (if objnames
	     (pop objnames)
	   (format nil "~d" (intern-gensym "A"))))
	((dtype-returns-obj-p tp)
	 (if objfnnames
	     (pop objfnnames)
	   (format nil "~d" (intern-gensym "F"))))
	((dclass-p tp)
	 (if cobjnames
	     (pop cobjnames)
	   (format nil "~d" (intern-gensym "a"))))
	((dtype-returns-dclass-p tp)
	 (if cobjfnnames
	     (pop cobjfnnames)
	   (format nil "~d" (intern-gensym "f"))))
	((prop-p tp)
	 (if propnames
	     (pop propnames)
	   (format nil "~d" (intern-gensym "P"))))
	((dtype-returns-prop-p tp)
	 (if propfnnames
	     (pop propfnnames)
	   (format nil "~d" (intern-gensym "\\phi"))))
	(t (format nil "~d" (intern-gensym "X")))))

(defun nd-rule-dbtype (name tp)
  (let ((prems nil)
	(ctx nil))
    (do ((tp1 tp (dpi-cod tp1)))
	((not (dpi-p tp1))
;	 (format t "***~%prems = ~d~%ctx = ~d~%" prems ctx) ; delete me
	 (setq prems (reverse prems))
	 (case (length prems)
	       (0
		(format nil "\\ianc{}{\\Gamma\\vdash ~d}{{\\mbox{\\tt ~d}}}"
			(nd-atp-direct-latex tp1 ctx)
			name))
	       (1
		(format nil "\\ianc{~d}{\\Gamma\\vdash ~d}{{\\mbox{\\tt ~d}}}"
			(car prems)
			(nd-atp-direct-latex tp1 ctx)
			name))
	       (2
		(format nil "\\ibnc{~d}{~d}{\\Gamma\\vdash ~d}{{\\mbox{\\tt ~d}}}"
			(car prems)
			(cadr prems)
			(nd-atp-direct-latex tp1 ctx)
			name))
	       (3
		(format nil "\\icnc{~d}{~d}{~d}{\\Gamma\\vdash ~d}{{\\mbox{\\tt ~d}}}"
			(car prems)
			(cadr prems)
			(caddr prems)
			(nd-atp-direct-latex tp1 ctx)
			name))
	       (4
		(format nil "\\idnc{~d}{~d}{~d}{~d}{\\Gamma\\vdash ~d}{{\\mbox{\\tt ~d}}}"
			(car prems)
			(cadr prems)
			(caddr prems)
			(cadddr prems)
			(nd-atp-direct-latex tp1 ctx)
			name))
	       (t
		(let ((premstr (car prems)))
		  (dolist (prem (cdr prems))
		    (setq premstr (format nil "~d\\hspace{2mm} ~d" premstr prem)))
		  (format nil "\\ianc{~d}{\\Gamma\\vdash ~d}{{\\mbox{\\tt ~d}}}"
			  premstr
			  (nd-atp-direct-latex tp1 ctx)
			  name)))))
;	(format t "prems = ~d~%ctx = ~d~%" prems ctx) ; delete me
	(let* ((dom (dpi-dom tp1))
	       (name (if (nintrm-type-p 0 (dpi-cod tp1))
			 (nd-rule-get-name dom)
		       nil)))
	  (multiple-value-bind
	   (newctxstr tpstr trmstr)
	   (nd-prem-direct-latex dom ctx name)
	   (if name
	       (push (format nil "\\Gamma~d\\vdash ~d:~d" newctxstr trmstr tpstr) prems)
	     (push (format nil "\\Gamma~d\\vdash ~d" newctxstr tpstr) prems)))
	  (push name ctx)))))

(defun nd-class-pred-direct-latex (trm ctx)
  (declare (special paramnames))
  (if (and (app-p trm) (eq (app-func trm) '|in|))
      (nd-term-direct-latex (app-arg trm) ctx)
    (if (numberp trm)
	(nth trm ctx)
      (if (symbolp trm)
	  (format nil "~d" trm)
	(let ((x (format nil "~d" (if paramnames (pop paramnames) (intern-gensym "x")))))
	  (format nil "\\{~d|~d\\}"
		  x
		  (nd-prop-direct-latex (gen-lam-body trm) (cons x ctx) nil)))))))

(defun nd-prop-direct-latex (trm ctx &optional parens)
  (case (term-app-head trm)
	(|in|
	 (format nil "~d\\in ~d"
		(nd-term-direct-latex (app-arg trm) ctx)
		(nd-term-direct-latex (app-arg (app-func trm)) ctx)))
	(|eq|
	 (format nil "~d=~d"
		(nd-term-direct-latex (app-arg (app-func trm)) ctx)
		(nd-term-direct-latex (app-arg trm) ctx)))
	(|not|
	 (format nil "\\lnot ~d"
		(nd-prop-direct-latex (app-arg trm) ctx)))
	(t (term-direct-latex trm ctx parens))))

(defun nd-term-direct-latex (trm ctx &optional parens)
  (declare (special paramnames))
  (if (or (lam-p trm) (pair-p trm))
      (term-direct-latex trm ctx parens)
    (if (fst-p trm)
	(format nil "\\pi_1(~d)"
		(nd-term-direct-latex (fst-arg trm) ctx parens))
      (if (snd-p trm)
	  (term-direct-latex trm ctx parens)
	(case (term-app-head trm)
	      (|emptyset| "\\emptyset")
	      (|setadjoin|
	       (format nil "\\{~d\\}\\cup ~d"
		       (nd-term-direct-latex (app-arg (app-func trm)) ctx parens)
		       (nd-term-direct-latex (app-arg trm) ctx parens)))
	      (|dsetconstr|
	       (let ((x (format nil "~d" (if paramnames (pop paramnames) (intern-gensym "x")))))
		 (format nil "\\{~d\\in ~d|~d\\}"
			 x
			 (nd-term-direct-latex (app-arg (app-func trm)) ctx parens)
			 (nd-prop-direct-latex (gen-lam-body (app-arg trm)) (cons x ctx) parens))))
	      (|setunion|
	       (format nil "\\bigcup ~d"
		       (nd-term-direct-latex (app-arg trm) ctx parens)))
	      (|powerset|
	       (format nil "\\powerset(~d)"
		       (nd-term-direct-latex (app-arg trm) ctx parens)))
	      (|univ|
	       (format nil "{\\mbox{\\tt univ}}(~d)"
		       (nd-term-direct-latex (app-arg trm) ctx parens)))
	      (t
	       (term-direct-latex trm ctx parens)))))))

(defun nd-prem-direct-latex (tp ctx &optional name)
  (if (dpi-p tp)
      (let* ((dom (dpi-dom tp))
	     (newname (if (or name (nintrm-type-p 0 (dpi-cod tp)))
			  (nd-rule-get-name dom)
			nil)))
	(multiple-value-bind
	 (newctxstr tpstr namestr)
	 (nd-prem-direct-latex (dpi-cod tp) (ctx-cons newname ctx)
			       (if name
				   (cons name newname)
				 nil))
	 (if newname
	     (if (or (obj-p dom) (prop-p dom))
		 (values (format nil ",~d~d" newname newctxstr) tpstr namestr)
	       (values (format nil ",~d:~d~d" newname (nd-atp-direct-latex dom ctx)
			       newctxstr)
		       tpstr namestr))
	   (values (format nil ",~d~d" 
			   (nd-atp-direct-latex dom ctx)
			   newctxstr)
		   tpstr namestr))))
    (values "" (nd-atp-direct-latex tp ctx)
	    (if name
		(if (consp name)
		    (format nil "(~d)"
			    (nd-fake-app-direct-latex name))
		  name)
	      nil)
	    )))

(defun nd-fake-app-direct-latex (f)
  (if (consp f)
      (format nil "~d ~d" (nd-fake-app-direct-latex (car f)) (cdr f))
    f))

(defun nd-atp-direct-latex (tp ctx)
  (cond ((pf-p tp)
	 (nd-prop-direct-latex (pf-prop tp) ctx nil))
	((dclass-p tp)
	 (nd-class-pred-direct-latex (dclass-pred tp) ctx))
	((obj-p tp) "\\obj")
	((prop-p tp) "\\prop")
	(t
;	 (fail "nd-atp-direct-latex called with nonatomic type" tp)
	 (format nil "??~d??" tp)
	 )))


(defun latex-char-needs-escape-p (c)
  (member c '(#\# #\_ #\^ #\% #\\)))

(defun direct-latex-next-bvar-name (dom ctxnames &optional usedasset)
  (let* ((potnames
	  (direct-latex-potential-names dom usedasset))
	 (l (length potnames))
	 (name nil)
	 (n 0))
    (loop until name do
	  (if (< n l)
	      (setq name (nth n potnames))
	    (setq name (format nil "~d_~d"
			       (nth (mod n l) potnames)
			       (- (floor (/ n l)) 1)
			       )))
	  (when (member name ctxnames :test #'string=)
	    (setq name nil)
	    (incf n)))
    name))

(defun direct-latex-potential-names (dom &optional usedasset)
  (cond ((obj-p dom) (if usedasset '("A" "B" "C") '("x" "y" "z")))
	((prop-p dom) '("M" "N" "P"))
	((equal dom *pred*) '("P" "Q"))
	((dclass-p dom)
	 (if usedasset
	     '("A" "B" "C")
	   '("a" "b" "c")))
	((dtype-returns-pf-p dom) '("D" "E"))
	((dtype-returns-obj-p dom) '("F" "G" "H"))
	((dtype-returns-dclass-p dom) '("f" "g" "h"))
	((dtype-returns-prop-p dom) '("R" "S"))))

(defun dtype-n-used-as-set-p (n tp)
  (cond ((dpi-p tp)
	 (or (dtype-n-used-as-set-p n (dpi-dom tp))
	     (dtype-n-used-as-set-p (1+ n) (dpi-cod tp))))
	((dclass-p tp)
	 (trm-n-used-as-set-p n (dclass-pred tp)))
	((pf-p tp)
	 (trm-n-used-as-set-p n (pf-prop tp)))
	(t nil)))

(defun trm-n-used-as-set-p (n trm)
  (cond ((and (app-p trm) (eq (app-func trm) '|in|)
	      (or (equal n (app-arg trm))
		  (equal (fst n) (app-arg trm))))
	 t)
	((app-p trm)
	 (or (trm-n-used-as-set-p n (app-func trm))
	     (trm-n-used-as-set-p n (app-arg trm))))
	((lam-p trm)
	 (trm-n-used-as-set-p (1+ n) (lam-body trm)))
	((pair-p trm)
	 (or (trm-n-used-as-set-p n (pair-fst trm))
	     (trm-n-used-as-set-p n (pair-snd trm))))
	((fst-p trm)
	 (trm-n-used-as-set-p n (fst-arg trm)))
	((snd-p trm)
	 (trm-n-used-as-set-p n (snd-arg trm)))
	(t nil)))



	 
