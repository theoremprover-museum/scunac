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

; Authors: Chad E Brown
; File: scunakator.lisp
; March, 2006
; Modified from "The Plannotator" written in November 2005

; This file is the core of the scunakator.
; It contains the Scunakator Data Structure (PDS).
(defstruct scunakator~pds
  (plangraph nil)
  (queue nil)
  (ref-assoc nil)
  (nextfactkey nil)
  (lastfactkey nil)
  (maingcat nil)
  (outitems nil)
  (doc nil)
  (outstr nil))

; methods are stored based on post-conditions
(defvar scunakator~method-store nil)
  
(defvar scunakator~pds nil)

; Code for Scunakator core (using the Scunakator Data Structure)
(defun scunakate-proof (infile outfile)
  (let ((ppp (pre-scunakate-proof infile))
	(done nil))
    (declare (special scunakator~pds scunakator~method-store))
    (setq scunakator~pds (make-scunakator~pds :maingcat 'PROOF0))
    (setf (scunakator~pds-outstr scunakator~pds)
	  (open outfile :direction :output :if-exists :supersede))
    (loop until (or done (not ppp)) do
	  (let ((ret
		 (scunakator-plan (scunakator~pds-maingcat scunakator~pds)
				   ppp scunakator~method-store)))
	    (if ret
		(let ((possannl (mapcar #'post-scunakate-scunakation
					(cadr ret))))
		  (if possannl
		      (if (cdr possannl)
			  (let ((str (format nil "alts")))
			    (dolist (p possannl)
			      (setq str (format nil "~d [~d]" str p)))
			    (push-out (format nil "~d." str)))
			(push-out (car possannl)))
;		    (push-out (car ret))
		    nil
		    )
		  (setf (scunakator~pds-lastfactkey scunakator~pds)
			(scunakator~pds-nextfactkey scunakator~pds))
		  (setf (scunakator~pds-nextfactkey scunakator~pds) nil)
		  (setq ppp (caddr ret))
		  )
	      (let ((unpars (pop ppp)))
;		(push-out unpars)
		nil
		))))
    (push-out "qed.")
    (setf (scunakator~pds-outitems scunakator~pds)
	  (post-scunakate (reverse (scunakator~pds-outitems scunakator~pds))))
    (setf (scunakator~pds-doc scunakator~pds)
	  (scunakator~pds-outitems scunakator~pds))
;    (format (scunakator~pds-outstr scunakator~pds)
;	    "~S~%"
;	    (scunakator~pds-doc scunakator~pds))
    (close (scunakator~pds-outstr scunakator~pds))
    (scunakator~pds-doc scunakator~pds)))

(defun push-out (i)
  (declare (special scunakator~pds))
  (push i (scunakator~pds-outitems scunakator~pds))
  (format (scunakator~pds-outstr scunakator~pds) "~d~%" i)
  (force-output (scunakator~pds-outstr scunakator~pds)))

(defun pre-scunakate-proof (infile)
  (let ((s
	 (if (probe-file infile)
	     (open infile :direction :input)
	   (if (and *scunak-main-dir*
		    (probe-file (format nil "~d~d" *scunak-main-dir* infile)))
	       (open (format nil "~d~d" *scunak-main-dir* infile) :direction :input)
	     (fail "File does not exist"))))
	(outinfo nil))
    (do ((r (read-char s nil nil) (read-char s nil nil)))
	((null r)
	 (close s)
	 (reverse outinfo))
	(push r outinfo))))

(defun post-scunakate (outitems &optional (str ""))
  (if outitems
      (if (or (stringp (car outitems)) (characterp (car outitems)))
	  (post-scunakate (cdr outitems)
			   (format nil "~d~d" str (car outitems)))
	(if (consp (car outitems))
	    (if (or (consp (caar outitems))
		    (stringp (caar outitems)) (characterp (caar outitems)))
		(post-scunakate (append (car outitems) (cdr outitems)) str)
	      (if (equal str "")
		  (cons (post-scunakate-scunakation (car outitems))
			(post-scunakate (cdr outitems)))
		(cons str
		      (cons (post-scunakate-scunakation (car outitems))
			    (post-scunakate (cdr outitems))))))
	  (if (equal str "")
	      (cons (car outitems) (post-scunakate (cdr outitems)))
	    (cons str (cons (car outitems) (post-scunakate (cdr outitems)))))))
    (if (equal str "")
	nil
      (list str))))

(defun post-scunakate-scunakation (scunakation)
  scunakation)

(defun genkey ()
  (list (list 'PL-key (format nil "~d" (gensym "PL")))))

(defun genlabelkey (l)
  (declare (special scunakator~pds))
  (let ((k (format nil "~d" (gensym "PL"))))
    (push (cons l k) (scunakator~pds-ref-assoc scunakator~pds))
    (list (list 'PL-key k))))

(defun genfactkey ()
  (declare (special scunakator~pds))
  (unless (scunakator~pds-nextfactkey scunakator~pds)
    (setf (scunakator~pds-nextfactkey scunakator~pds)
	  (format nil "~d" (gensym "PL"))))
  (list (list 'PL-key (scunakator~pds-nextfactkey scunakator~pds))))

(defun ipos (n l)
  (cons (cons 'PL-POSITION n) l))

(defun lookup-ref (r)
  (declare (special scunakator~pds))
  (assoc r (scunakator~pds-ref-assoc scunakator~pds) :test #'equal))

; code for storing plethods in the method-store
(defmacro scunakator~defmethod (name &rest rst)
  `(scunakator~defmethod-real ',name ',rst))

(defun scunakator~defmethod-real (name rst)
  (let ((precond (assoc 'precondition rst))
	(postcond (assoc 'postcondition rst))
	(priority (assoc 'priority rst))
	(always-try (assoc 'always-try rst))
	(defn (assoc 'defn rst))
	(help-msg (assoc 'help-msg rst)))
    (if (and always-try (consp always-try) (consp (cdr always-try)))
	(setq always-try (cadr always-try))
      (setq always-try nil))
    (if (and priority (consp priority) (consp (cdr priority)))
	(setq priority (cadr priority))
      (setq priority 0))
    (if (and help-msg (consp help-msg) (consp (cdr help-msg)))
	(setq help-msg (cadr help-msg))
      (setq help-msg ""))
    (if precond
	(if (and (consp (cdr precond)) (consp (cadr precond))
		 (eq (caadr precond) 'text-fits)
		 (consp (cdadr precond)))
	    (progn
	      (setq precond (cadadr precond))
	      (if postcond
		  (if (and (consp (cdr postcond)) (consp (cadr postcond))
			   (eq (caadr postcond) 'text-is)
			   (consp (cdadr postcond)))
		      (progn
			(setq postcond (cadadr postcond))
			(if defn
			    (if (and (consp defn) (consp (cdr defn)))
				(progn
				  (setq defn (cadr defn))
				  (insert-into-method-store
				   name (characterize-precond precond)
				   postcond defn priority always-try help-msg)
				  )
			      (format t "Warning: Ill-formed defn for plethod ~d~%Skipping.~%" name))
			  (format t "Warning: Missing defn for plethod ~d~%Skipping.~%" name))
			)
		    (format t "Warning: Ill-defined postcondition for plethod ~d~%Skipping.~%" name))
		(format t "Warning: Missing postcondition for plethod ~d~%Skipping.~%" name)))
	  (format t "Warning: Ill-defined precondition for plethod ~d~%Skipping.~%" name))
      (format t "Warning: Missing precondition for plethod ~d~%Skipping.~%" name))))

(defun insert-into-method-store (name precond postcond defn priority always-try help-msg)
  (declare (special scunakator~method-store))
  (setq scunakator~method-store
	(insert-into-method-store-real
	 scunakator~method-store
	 name precond postcond defn priority always-try help-msg)))

(defun insert-into-method-store-real (ms name precond postcond defn priority always-try help-msg)
  (if ms
      (if (equal (caar ms) postcond)
	  (cons (cons (caar ms)
		      (insert-into-method-store-real-2 (cdar ms) name precond defn priority always-try help-msg))
		(cdr ms))
	(cons (car ms)
	      (insert-into-method-store-real (cdr ms) name precond postcond defn priority always-try help-msg)))
    (list (list postcond (list name precond defn priority always-try help-msg)))))

(defun insert-into-method-store-real-2 (ms1 name precond defn priority always-try help-msg)
  (if ms1
      (if (<= priority (nth 3 (car ms1)))
	  (cons (list name precond defn priority always-try help-msg)
		ms1)
	(cons (car ms1)
	      (insert-into-method-store-real-2 (cdr ms1) name precond
					       defn priority always-try help-msg)))
    (list (list name precond defn priority always-try help-msg))))


(defun characterize-precond (g)
  (if g
      (if (stringp (car g))
	  (let* ((r (characterize-precond (cdr g)))
		 (n (length (car g)))
		 (m n))
	    (dotimes (i n)
	      (decf m)
	      (push (aref (car g) m) r))
	    r)
	(cons (car g) (characterize-precond (cdr g))))
    nil))

; code for the Scunakator planner
(defun scunakator-predictor (state plethods k)
  (declare (special scunakator~pds))
  (let* ((postdot (caddr state))
	 (c (car postdot))
	 (new nil))
    (dolist (gr (cdr (assoc c plethods)))
      (let ((a (list c NIL (cadr gr) k 
		     )))
	(multiple-value-bind
	 (scunakator-plangraph new2)
	 (scunakator-enqueue a (scunakator~pds-plangraph scunakator~pds) k)
	 (setq new new2)
	 (setf (scunakator~pds-plangraph scunakator~pds) scunakator-plangraph))
	(when new
;	  (format t "Adding (predictor) ~d to queue~%" a) ; delete me
	  (if (scunakator~pds-queue scunakator~pds)
	      (nconc (scunakator~pds-queue scunakator~pds) (list a))
	    (setf (scunakator~pds-queue scunakator~pds)
		  (list a))))))))

(defun scunakator-scanner (state wk k)
  (declare (special scunakator~pds))
  (let* ((g (car state))
	 (predot (cadr state))
	 (postdot (caddr state))
	 (b (car postdot))
	 (j (nth 3 state)))
    (when (eq b wk)
      (setf (scunakator~pds-plangraph scunakator~pds)
	    (scunakator-enqueue
	     (list g
		   (append predot (list b)) (cdr postdot) j
		   )
	     (scunakator~pds-plangraph scunakator~pds) (1+ k))))))

(defun scunakator-completer (state k)
  (declare (special scunakator~pds))
  (let* ((g (car state))
	 (j (nth 3 state)))
    (dolist (state2 (nth j (scunakator~pds-plangraph scunakator~pds)))
      (let ((g2 (car state2))
	    (predot2 (cadr state2))
	    (postdot2 (caddr state2))
	    (i (nth 3 state2)))
	(when (and postdot2 (eq (car postdot2) g))
	  (let ((a (list g2 (append predot2 (list g)) (cdr postdot2) i))
		(new nil))
	    (multiple-value-bind
	     (scunakator-plangraph new2)
	     (scunakator-enqueue a (scunakator~pds-plangraph scunakator~pds) k)
	     (setq new new2)
	     (setf (scunakator~pds-plangraph scunakator~pds) scunakator-plangraph))
	    (when new
	      (if (scunakator~pds-queue scunakator~pds)
		  (nconc (scunakator~pds-queue scunakator~pds) (list a))
		(setf (scunakator~pds-queue scunakator~pds)
		      (list a))))))))))

(defun scunakator-enqueue (a plangraph k)
  (if (> k 0)
      (if plangraph
	  (multiple-value-bind
	   (plangraph2 new2)
	   (scunakator-enqueue a (cdr plangraph) (- k 1))
	   (values
	    (cons (car plangraph) plangraph2)
	    new2))
	(multiple-value-bind
	 (plangraph2 new2)
	 (scunakator-enqueue a nil (- k 1))
	 (values (cons nil plangraph2) new2)))
    (if plangraph
	(if (member a (car plangraph) :test
		    #'(lambda (x y)
			(and (eq (car x) (car y))
			     (equal (cadr x) (cadr y))
			     (equal (caddr x) (caddr y))
			     (= (cadddr x) (cadddr y)))))
	    (values plangraph nil)
	  (values (cons (cons a (car plangraph)) (cdr plangraph)) t))
      (values (list (list a)) t))))

(defun scunakator-plan (gcat toks plethods)
  (scunakator-plan-0 gcat toks plethods 0
		  (let ((a (list NIL NIL (list gcat) 0)))
		    (scunakator-enqueue a nil 0))
		  nil))

(defun scunakator-plan-0 (gcat toks plethods n plangraph back)
  (if toks
      (if (nth n plangraph)
	  (scunakator-plan-0 gcat (cdr toks)
			  plethods (1+ n)
			  (scunakator-plan-1 (car toks) n plethods plangraph)
			  (cons (car toks) back))
	(return-best-result gcat plethods n plangraph
			    back
			    toks
			    ))
    (return-best-result gcat plethods n (scunakator-plan-1 nil n plethods plangraph) back nil)))

(defun return-best-result (gcat plethods n plangraph back toks)
  (let ((words back)
	(redo toks)
	(m n)
	(ret nil))
    (loop while (and (> m 0) (not ret)) do
	  (let ((succ
		 (find-if
		  #'(lambda (state)
		      (and (null (car state))
			   (null (caddr state))))
		  (nth m plangraph))))
	    (if succ
		(progn
		  (setq ret (list (reverse words)
				  (plangraph-to-plan-trees (reverse words) 0 m gcat plethods plangraph 10 nil 1)
				  redo)))
	      (progn
		(decf m)
		(push (pop words) redo)
		))))
    ret))

(defun scunakator-plan-1 (w n plethods plangraph)
  (if (and scunakator~pds (scunakator~pds-p scunakator~pds))
      (progn
	(setf (scunakator~pds-plangraph scunakator~pds) plangraph)
	(setf (scunakator~pds-queue scunakator~pds) (copy-list (nth n plangraph))))
    (setq scunakator~pds (make-scunakator~pds :plangraph plangraph :queue (copy-list (nth n plangraph)))))
  (loop while (scunakator~pds-queue scunakator~pds) do
	(let ((state (pop (scunakator~pds-queue scunakator~pds))))
	  (if (caddr state)
	      (if (assoc (car (caddr state)) plethods)
		  (scunakator-predictor state plethods n)
		(scunakator-scanner state w n))
	    (scunakator-completer state n))))
  (scunakator~pds-plangraph scunakator~pds))

(defun plethod-arity (gr plethods)
  (if gr
      (if (assoc (car gr) plethods)
	  (1+ (plethod-arity (cdr gr) plethods))
	(plethod-arity (cdr gr) plethods))
    0))

; already defined in parser.lisp
;(defun pretty-print-polish (polish &optional (s *standard-output*))
;  (if polish
;      (if (> (cdar polish) 0)
;	  (let ((rst (cdr polish)))
;	    (format s "(~d" (caar polish))
;	    (dotimes (i (cdar polish))
;	      (format s " ")
;	      (setq rst (pretty-print-polish rst s)))
;	    (format s ")")
;	    rst)
;	(progn
;	  (format s "~d" (caar polish))
;	  (cdr polish)))
;    nil))

; order of plethods matters!
; return the first m possible plans
(defun plangraph-to-plan-trees (words start end gcat plethods plangraph &optional (m 3) (usename nil) (evalnum 1))
  (mapcar #'(lambda (x)
	      (if usename
		  (list 'quote (apptree-out-of-polish x))
		(scunakator~plan-evaluator
		 (fctree-out-of-polish x)
		 evalnum)))
	  (plangraph-to-plan-trees-polish words start end (list gcat) plethods plangraph m usename)))

; already defined in parser.lisp
;(defun fctree-out-of-polish (polish)
;  (if polish
;      (if (> (cdar polish) 0)
;	  (let ((f (if (caar polish)
;		       (list 'funcall (caar polish))
;		     (list 'list)))
;		(arg nil)
;		(rst (cdr polish)))
;	    (dotimes (i (cdar polish))
;	      (multiple-value-setq
;	       (arg rst)
;	       (fctree-out-of-polish rst))
;	      (nconc f (list arg)))
;	    (values f rst))
;	(values (caar polish) (cdr polish)))
;    nil))

; already defined in parser.lisp
;(defun apptree-out-of-polish (polish)
;  (if polish
;      (let ((f (caar polish))
;	    (arg nil)
;	    (rst (cdr polish)))
;	(dotimes (i (cdar polish))
;	  (multiple-value-setq
;	   (arg rst)
;	   (apptree-out-of-polish rst))
;	  (setq f (cons f arg)))
;	(values f rst))
;      nil))

(defun plangraph-to-plan-trees-polish (words start end rst plethods plangraph
					     &optional (m 3) (usename nil))
  (if (> m 0)
      (if rst
	  (let ((a (assoc (car rst) plethods)))
	    (if a
		(let ((ret nil))
		  (dolist (gr (cdr a))
		    (when (and (symbolp (car gr)) (nth 4 gr))
		      (setq m (max m (nth 4 gr))))
		    (when (> m 0)
		      (let* ((rule (cadr gr))
			     (rst2 (append rule (cdr rst))))
			(when (consistent-with-plan-plangraph words start end rst2 plethods plangraph)
			  (let ((new (plangraph-to-plan-trees-polish words start end rst2 plethods plangraph m usename))
				(ar (plethod-arity rule plethods)))
			    (setq m (- m (length new)))
			    (setq ret
				  (append ret
					  (mapcar #'(lambda (x)
						      (acons 
						       (if usename
							   (car gr)
							 (caddr gr))
						       ar x))
						  new)))))))
		    )
		  ret)
	      (plangraph-to-plan-trees-polish words (1+ start) end (cdr rst) plethods plangraph m usename)))
	(list nil))
    nil))

(defun consistent-with-plan-plangraph (words start end rst plethods plangraph)
    (progn
      (if rst
	  (let ((a (assoc (car rst) plethods)))
	    (if a
		(consistent-with-plan-plangraph-2 words start start end (car rst) (cdr rst) plethods plangraph)
	      (if (eq (nth start words) (car rst))
		  (consistent-with-plan-plangraph words (1+ start) end (cdr rst) plethods plangraph)
		nil)))
	(if (= start end)
	    t
	  nil))))

(defun consistent-with-plan-plangraph-2 (words start mid end gcat rst plethods plangraph)
  (if (> mid end)
      nil
    (or (consistent-with-plan-plangraph-2 words start (1+ mid) end gcat rst plethods plangraph)
	(and (find-if #'(lambda (state)
			  (and (eq (car state) gcat)
			       (null (caddr state))
			       (= (cadddr state) start)))
		      (nth mid plangraph))
	     (consistent-with-plan-plangraph words mid end rst plethods plangraph)))))

; Code for Scunakator Plan Evaluator
(defun scunakator~plan-evaluator (ret evalnum)
  (dotimes (i evalnum ret)
    (setq ret (eval ret))))

; Code to output scunakated text in a variety of formats
; assumes a proper scunakation
(defun scunakator~extract-scunakation-text (p)
  (scunakator~extract-scunakation-text-l (list p)))

(defun scunakator~extract-scunakation-text-l (pl)
  (if pl
      (if (stringp (car pl))
	  (format nil "~d~d" (car pl) (scunakator~extract-scunakation-text-l (cdr pl)))
	(if (and (consp (car pl)) (eq (caar pl) 'PL-ALTERNATIVE))
	    (format nil "~d~d"
		    (scunakator~extract-scunakation-text-l (list (caddar pl)))
		    (scunakator~extract-scunakation-text-l (cdr pl)))
	  (format nil "~d~d"
		  (scunakator~extract-scunakation-text-l (cddar pl))
		  (scunakator~extract-scunakation-text-l (cdr pl)))))
    ""))

(defun scunakator~to-html (doc outfile)
  (let ((outstr (open outfile :direction :output :if-exists :supersede)))
    (format outstr "<html><head><title>Scunakator, c 2005 Brown/Wolska</title></head><body><p>")
    (scunakator~to-html-real (list doc) outstr)
    (format outstr "</p></body></html>")
    (close outstr)))

(defun scunakator~to-html-real (pl outstr)
  (if pl
      (if (stringp (car pl))
	  (progn
	    (string-to-html (car pl) outstr)
	    (scunakator~to-html-real (cdr pl) outstr))
	(if (and (consp (car pl)) (eq (caar pl) 'PL-ALTERNATIVE))
	    (progn
	      (format outstr "<table bgcolor=~d border=5 cellpadding=10><br><tr><td><font color=#000000 SIZE=6><B><I>PL-ALTERNATIVE</I></B></font></td></tr></br> <font color=~d>"
		      (pl-bgcolor 'PL-ALTERNATIVE)
		      (pl-color 'PL-ALTERNATIVE))
	      (scunakator~to-html-alts (cddar pl) outstr)
	      (format outstr "</table>")
	      (scunakator~to-html-real (cdr pl) outstr))
	    (progn
	      (format outstr "<table bgcolor=~d border=4 cellpadding=10><td><font color=~d>"
		      (pl-bgcolor (caar pl))
		      (pl-color (caar pl)))
	      (scunakator~to-html-real (cddar pl) outstr)
	      (format outstr "</td></table>")
	      (scunakator~to-html-real (cdr pl) outstr))))
    nil))

(defun string-to-html (str outstr)
  (dotimes (i (length str))
    (let ((ch (aref str i)))
      (if (member ch '(#\newline #\return))
	  (format outstr "</p><p>")
	(format outstr "~d" ch)))))

(defun scunakator~to-html-alts (al outstr &optional (i 1))
  (if al
      (progn
	(format outstr "<br><tr><td><B>PL-ALTERNATIVE ~d</B></td></tr></br><br><tr><td>"
		i)
	(format outstr "<table bgcolor=~d border=5 cellpadding=10><font color=~d>"
		(pl-bgcolor 'PL-ALTERNATIVE-1)
		(pl-color 'PL-ALTERNATIVE-1))
	(scunakator~to-html-real (list (car al)) outstr)
;	(format outstr "</font></table></td></tr></br>")
	(format outstr "</font></td></tr></br>")
	(scunakator~to-html-alts (cdr al) outstr (1+ i)))
    nil))

(defun pl-color (a)
  (let ((n (pl-color-num a)))
    (0fill 6 (format nil "~X" n))))

(defun pl-bgcolor (a)
  (let ((n (pl-bgcolor-num a)))
    (0fill 6 (format nil "~X" n))))

(defun 0fill (n str)
  (loop while (< (length str) n) do
	(setq str (format nil "0~d" str)))
  str)

(defun pl-color-num (a)
  (multiple-value-bind
   (red green blue)
   (pl-color-nums a)
   (+ (* 65536 red) (* 256 green) blue)))

(defun pl-bgcolor-num (a)
  (multiple-value-bind
   (red green blue)
   (pl-bgcolor-nums a)
   (+ (* 65536 red) (* 256 green) blue)))

(defun pl-color-nums (a)
  (multiple-value-bind
   (red green blue)
   (pl-bgcolor-nums a)
   (if (and (< red 50) (< green 50) (< blue 50))
       (values 255 255 255)
     (values 0 0 0))))

(defun pl-bgcolor-nums (a)
  (case a
	(PL-DOCUMENT (values 20 99 10))
	(PL-THEORY (values 91 230 11))
	(PL-PROOF (values 255 20 20))
	(PL-ALTERNATIVE (values 255 0 0))
	(PL-ALTERNATIVE-1 (values 255 255 255))
	(PL-ASSUME (values 0 255 0))
	(PL-FACT (values 20 20 255))
	(PL-SUBGOAL (values 20 128 128))
	(PL-TRIVIAL (values 0 0 0))
	(PL-DECLARATION (VALUES 106 116 35))
	(PL-VARIABLE (VALUES 186 193 167))
	(PL-PROPOSITION (VALUES 15 210 186))
	(PL-FROM (VALUES 20 136 117))
	(PL-REF (VALUES 24 232 197))
	(PL-ATTRIBUTION (VALUES 20 10 173))
	(PL-APPLICATION (VALUES 249 148 163))
	(PL-OPERATOR (VALUES 1 1 1))
	(PL-ARGUMENT (VALUES 45 246 146))
	(PL-SYMBOL (VALUES 175 143 142))
	(t 
	 (format t "Warning: Default Colors for ~d~%" a)
	 (VALUES 5 32 101))))
