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

; Chad E Brown
; February 2006

(defvar *vampire-executable* "vampire-8.0")

; By removing any of these constants from the *vampire-props* list,
; we restrict which clauses are made.
(defvar *vampire-props* '(|not| |and| |or| |imp| |equiv| |dall| |dex| |eq|))
;(defvar *vampire-props* '(|not|))

(defvar *vampire-allow-second* t)

(defvar *vampire-timeout* 300)

(defun vampire-res-fill-claim (c &optional (usable *scip-usable*))
  (if (claimname-p c)
      (vampire-res-fill-gentp (get c 'dbtype) usable)
    (fail "not a claim" c)))

(defun vampire-res-fill-gentp (tp &optional (usable *scip-usable*) namedbdvars)
  (if (dpi-p tp)
      (let ((x (intern-gensym "u")))
	(setf (get x 'bvar) t)
	(setf (get x 'dbtype) (dpi-dom tp))
	(vampire-res-fill-gentp (dbsubst-type-0 (dpi-cod tp) x) usable (cons x namedbdvars)))
    (vampire-res-fill namedbdvars tp usable)))

(defun vampire-res-fill (namedbdvars tp &optional (usable *scip-usable*))
  (if (pf-p tp)
      (let ((s (open "vampire.in" :direction :output :if-exists :supersede)))
	(make-vampire-file (pf-prop tp) namedbdvars usable s)
	(close s)
	(call-system (format nil "~d ~d vampire.in > vampire.out"
			     *vampire-executable*
			     (if *vampire-timeout*
				 (format nil "-t ~d" *vampire-timeout*)
			       "")
			     ))
	(if (probe-file "vampire.out")
	    (let* ((so (open "vampire.out" :direction :input))
		   (pf (extract-vampire-proof-object so)))
	      (close so)
	      pf)
	  nil))
    nil))

(defun extract-vampire-proof-object (s)
  (do ((l (read-line s nil nil) (read-line s nil nil)))
      ((or (null l)
	   (or (string= l "Refutation found. Thanks to Tanya!")
	       (string= l "% Proof found. Thanks to Tanya!")))
       (if l
	   t
	 nil))))

(defun make-vampire-file (goalprop sos usable &optional (s *standard-output*))
  (format s "%--------------------------------------------------------------------------~%")
  (dolist (c (append (remove-duplicates usable) (remove-duplicates sos)))
    (when (seriously-type-vampire-fof-p (get c 'dbtype))
      (format s "input_formula(~d,axiom,~d).~%"
	      (vampirize-name c)
	      (type-vampire-fof-string (get c 'dbtype) c))))
  (when (seriously-vampire-prop-p goalprop *emptyctx*)
    (format s "input_formula(mainconj,conjecture,~d).~%"
	    (vampire-prop-string goalprop)))
  (format s "%--------------------------------------------------------------------------~%"))

(defun vampirize-name (c)
  (let ((str (format nil "~d" c))
	(ret ""))
    (dotimes (i (length str) ret)
      (let ((ch (aref str i)))
	(case ch
	      (#\#
	       (setq ret (format nil "~d__" ret)))
	      (#\+
	       (setq ret (format nil "~d___" ret)))
	      (t
	       (setq ret (format nil "~d~d" ret ch))))))))

(defun seriously-type-vampire-fof-p (tp &optional (ctx *emptyctx*))
  (if *vampire-allow-second*
      (seriously-type-vampire-fof-2-p tp ctx)
    (seriously-type-vampire-fof-1-p tp ctx)))

(defun seriously-type-vampire-fof-1-p (tp &optional (ctx *emptyctx*))
  (if (dpi-p tp)
      (and (or (obj-p (dpi-dom tp))
	       (and (dclass-p (dpi-dom tp))
		    (seriously-vampire-prop-p (gen-lam-body (dclass-pred (dpi-dom tp)))
					    (ctx-cons (obj) ctx)))
	       (and (pf-p (dpi-dom tp))
		    (seriously-vampire-prop-p (pf-prop (dpi-dom tp)) ctx)))
	   (seriously-type-vampire-fof-1-p (dpi-cod tp) (ctx-cons (dpi-dom tp) ctx)))
    (or
     (and (pf-p tp)
	  (seriously-vampire-prop-p (pf-prop tp) ctx))
     (and (dclass-p tp)
	  (seriously-vampire-prop-p (gen-lam-body (dclass-pred tp)) (ctx-cons (obj) ctx))))))

(defun seriously-type-vampire-fof-2-p (tp &optional (ctx *emptyctx*))
  (if (dpi-p tp)
      (let ((dom (dpi-dom tp))
	    (cod (dpi-cod tp)))
	(cond ((obj-p dom)
	       (seriously-type-vampire-fof-2-p cod (ctx-cons dom ctx)))
	      ((pf-p dom)
	       (and (seriously-vampire-prop-p (pf-prop dom) ctx)
		    (seriously-type-vampire-fof-2-p cod (ctx-cons dom ctx))))
	      ((dclass-p dom)
	       (and (seriously-vampire-prop-p (gen-lam-body (dclass-pred dom)) (ctx-cons (obj) ctx))
		    (seriously-type-vampire-fof-2-p cod (ctx-cons dom ctx))))
	      ((dpi-p dom)
	       (and (seriously-type-vampire-fof-3-p dom ctx)
		    (seriously-type-vampire-fof-2-p cod (ctx-cons dom ctx))))
	      (t nil)))
    (or (and (pf-p tp)
	     (seriously-vampire-prop-p (pf-prop tp) ctx))
	(and (dclass-p tp)
	     (seriously-vampire-prop-p (gen-lam-body (dclass-pred tp)) (ctx-cons (obj) ctx))))))

(defun seriously-type-vampire-fof-3-p (tp &optional (ctx *emptyctx*))
  (if (dpi-p tp)
      (let ((dom (dpi-dom tp))
	    (cod (dpi-cod tp)))
	(cond ((obj-p dom)
	       (seriously-type-vampire-fof-3-p cod (ctx-cons dom ctx)))
	      ((pf-p dom)
	       (and (seriously-vampire-prop-p (pf-prop dom) ctx)
		    (seriously-type-vampire-fof-3-p cod (ctx-cons dom ctx))))
	      ((dclass-p dom)
	       (and (seriously-vampire-prop-p (gen-lam-body (dclass-pred dom)) (ctx-cons (obj) ctx))
		    (seriously-type-vampire-fof-3-p cod (ctx-cons dom ctx))))
	      (t nil)))
    (and (pf-p tp)
	 (seriously-vampire-prop-p (pf-prop tp) ctx))))

(defun seriously-vampire-prop-p (trm ctx)
  (let ((h (term-extr-head trm))
	(args (term-extr-args trm)))
    (case h
	  (|not| 
	   (and (member h *vampire-props*)
		(seriously-vampire-prop-p (car args) ctx)))
	  ((|or| |and| |imp| |equiv|)
	   (and (member h *vampire-props*)
		(seriously-vampire-prop-p (car args) ctx)
		(seriously-vampire-prop-p (cadr args) ctx)))
	  ((|dall| |dex|)
	   (and (member h *vampire-props*)
		(seriously-vampire-term-p (car args) ctx)
		(seriously-vampire-prop-p (gen-lam-body (cadr args))
					  (ctx-cons (dclass (app '|in| (car args)))
						    ctx))))
	  (|eq|
	   (and (member h *vampire-props*)
		(seriously-vampire-term-p (car args) ctx)
		(seriously-vampire-term-p (cadr args) ctx)))
	  (t
	   (and (seriously-vampire-reln-p (ctx-extract-type ctx h))
		(not (find-if-not #'(lambda (x)
				      (seriously-vampire-term-p x ctx))
				  (term-extr-args trm))))))))

(defun seriously-vampire-reln-p (tp)
  (if (dpi-p tp)
      (and (or (obj-p (dpi-dom tp))
	       (dclass-p (dpi-dom tp)))
	   (seriously-vampire-reln-p (dpi-cod tp)))
    (prop-p tp)))

(defun seriously-vampire-func-p (tp)
  (if (dpi-p tp)
      (and (or (obj-p (dpi-dom tp))
	       (dclass-p (dpi-dom tp)))
	   (seriously-vampire-func-p (dpi-cod tp)))
    (or (obj-p tp)
	(dclass-p tp))))

(defun seriously-vampire-term-p (trm ctx)
  (if (lam-p trm)
      nil
    (if (pair-p trm)
	(seriously-vampire-term-p (pair-fst trm) ctx)
      (if (snd-p trm)
	  nil
	(let ((h (term-extr-head trm)))
	  (and (seriously-vampire-func-p (ctx-extract-type ctx h))
	       (not (find-if-not #'(lambda (x)
				     (seriously-vampire-term-p x ctx))
				 (term-extr-args trm)))))))))

(defun type-vampire-fof-string (tp trm)
  (if (dpi-p tp)
      (let ((dom (dpi-dom tp))
	    (cod (dpi-cod tp)))
	(cond ((obj-p dom)
	       (let ((x (intern-gensym "X")))
		 (setf (get x 'vvar) t)
		 (setf (get x 'bvar) t)
		 (setf (get x 'dbtype) (obj))
		 (format nil "(! [~d] : ~d)"
			 x
			 (type-vampire-fof-string (dbsubst-type-0 cod x) (app trm x)))))
	      ((pf-p dom)
	       (format nil "(~d => ~d)"
		       (vampire-prop-string (pf-prop dom))
		       (type-vampire-fof-string cod (gen-lam-body trm))))
	      ((dclass-p dom)
	       (let ((w (intern-gensym "W"))
		     (p (intern-gensym "P")))
		 (setf (get w 'vvar) t)
		 (setf (get p 'vvar) t)
		 (setf (get w 'bvar) t)
		 (setf (get w 'dbtype) (obj))
		 (setf (get p 'bvar) t)
		 (setf (get p 'dbtype) (pf (normalize (app (dclass-pred dom) w))))
		 (format nil "(! [~d] : (~d => ~d))"
			 w
			 (vampire-prop-string (normalize (app (dclass-pred dom) w)))
			 (type-vampire-fof-string (normalize-type (dbsubst-type-0 cod (pair w p)))
						(app trm (pair w p))
						))))
	      ((dpi-p dom)
	       (format nil "(~d => ~d)"
		       (type-vampire-fof-string dom 0)
		       (type-vampire-fof-string cod (gen-lam-body trm))))
	      ))
    (if (pf-p tp)
	(vampire-prop-string (pf-prop tp))
      (vampire-prop-string (normalize (app (dclass-pred tp) (fst trm)))))))

(defun vampire-prop-string (prop)
  (let ((h (term-extr-head prop))
	(args (term-extr-args prop)))
    (case h
	  (|not| (format nil "(~~ ~d)" (vampire-prop-string (car args))))
	  (|and| (format nil "(~d & ~d)"
			 (vampire-prop-string (car args))
			 (vampire-prop-string (cadr args))
			 ))
	  (|or|  (format nil "(~d | ~d)"
			 (vampire-prop-string (car args))
			 (vampire-prop-string (cadr args))
			 ))
	  (|imp|  (format nil "(~d => ~d)"
			 (vampire-prop-string (car args))
			 (vampire-prop-string (cadr args))
			 ))
	  (|equiv|  (format nil "(~d <=> ~d)"
			 (vampire-prop-string (car args))
			 (vampire-prop-string (cadr args))
			 ))
	  (|dex|
	   (let ((y (intern-gensym "Y")))
	     (setf (get y 'vvar) t)
	     (setf (get y 'bvar) t)
	     (setf (get y 'dbtype) (dclass (app '|in| (car args))))
	     (format nil "(? [~d] : (in(~d,~d) & ~d))"
		     y
		     (vampire-term-string (car args))
		     y
		     (vampire-prop-string (dbsubst-0 (gen-lam-body (cadr args)) y)))))
	  (|dall|
	   (let ((y (intern-gensym "Z")))
	     (setf (get y 'vvar) t)
	     (setf (get y 'bvar) t)
	     (setf (get y 'dbtype) (dclass (app '|in| (car args))))
	     (format nil "(! [~d] : (in(~d,~d) => ~d))"
		     y
		     (vampire-term-string (car args))
		     y
		     (vampire-prop-string (dbsubst-0 (gen-lam-body (cadr args)) y)))))
	  (|eq|
	   (format nil "(~d = ~d)"
		   (vampire-term-string (car args))
		   (vampire-term-string (cadr args))))
	  (t
	   (if args
	       (format nil "~d(~d)" h (vampire-termlist-string args))
	     (format nil "~d" h))))))

(defun vampire-termlist-string (tl)
  (if tl
      (if (cdr tl)
	  (format nil "~d,~d"
		  (vampire-term-string (car tl))
		  (vampire-termlist-string (cdr tl)))
	(vampire-term-string (car tl)))
    ""))

(defun vampire-term-string (trm)
  (if (pair-p trm)
      (vampire-term-string (pair-fst trm))
    (let ((h (term-extr-head trm))
	  (args (term-extr-args trm)))
      (if args
	  (format nil "~d(~d)" h (vampire-termlist-string args))
	(if (get h 'vvar)
	    (format nil "~d" h)
	  (format nil "c~d" h) ; prefix consts with lowercase c to avoid confusion with vars.
	  )))))

