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
; September, 2005
; Earley parsing algorithm for cfg taken from book:
; Speech and Language Processing
; Daniel Jurafsky and James H. Martin
; pages 377-383
; though SCANNER is not correct in the book, so I got the
; correction on the web from Wikipedia
; http://en.wikipedia.org/wiki/Earley_parser
; In the end, I really followed the Wikipedia version

; J. Earley. An efficient context-free parsing algorithm.
; Communications of the Association for Computing Machinery,
; 13(2):94-102, 1970.

(defvar *linecomment-chars* nil)

(defun earley-predictor (state grammar k)
  (declare (special earley-chart earley-queue))
  (let* ((postdot (caddr state))
	 (c (car postdot))
	 (new nil))
    (dolist (gr (cdr (assoc c grammar)))
      (let ((a (list c NIL (cadr gr) k 
;		     (list (list (car gr)
;				 (grule-arity (cadr gr) grammar)
;				 (nth 3 gr)
;				 ))
		     )))
	(multiple-value-setq
	 (earley-chart new)
	 (earley-enqueue a earley-chart k))
	(when new
;	  (format t "Adding (predictor) ~d to queue~%" a) ; delete me
	  (if earley-queue
	      (nconc earley-queue (list a))
	    (setq earley-queue (list a))))))))

(defun earley-scanner (state wk k)
  (declare (special earley-chart))
  (let* ((g (car state))
	 (predot (cadr state))
	 (postdot (caddr state))
	 (b (car postdot))
;	 (trace (nth 4 state))
	 (j (nth 3 state)))
    (when (eq b wk)
      (setq earley-chart
	    (earley-enqueue
	     (list g
		   (append predot (list b)) (cdr postdot) j
;		   trace
		   )
	     earley-chart (1+ k))))))

(defun earley-completer (state k)
  (declare (special earley-chart earley-queue))
  (let* ((g (car state))
	 (j (nth 3 state))
;	 (trace (nth 4 state))
	 )
    (dolist (state2 (nth j earley-chart))
      (let ((g2 (car state2))
	    (predot2 (cadr state2))
	    (postdot2 (caddr state2))
	    (i (nth 3 state2))
;	    (trace2 (nth 4 state2))
	    )
	(when (and postdot2 (eq (car postdot2) g))
	  (let ((a (list g2 (append predot2 (list g)) (cdr postdot2) i
;			 (append trace2 trace)
			 )
		   )
		(new nil))
	    (multiple-value-setq
	     (earley-chart new)
	     (earley-enqueue a earley-chart k))
	    (when new
;	      (format t "Adding (completion) ~d to queue~%" a) ; delete me
	      (if earley-queue
		  (nconc earley-queue (list a))
		(setq earley-queue (list a))))))))))

; ignore traces when checking equality
(defun earley-enqueue (a chart k)
  (if (> k 0)
      (if chart
	  (multiple-value-bind
	   (chart2 new2)
	   (earley-enqueue a (cdr chart) (- k 1))
	   (values
	    (cons (car chart) chart2)
	    new2))
	(multiple-value-bind
	 (chart2 new2)
	 (earley-enqueue a nil (- k 1))
	 (values (cons nil chart2) new2)))
    (if chart
	(if (member a (car chart) :test
		    #'(lambda (x y)
			(and (eq (car x) (car y))
			     (equal (cadr x) (cadr y))
			     (equal (caddr x) (caddr y))
			     (= (cadddr x) (cadddr y)))))
	    (values chart nil)
	  (values (cons (cons a (car chart)) (cdr chart)) t))
      (values (list (list a)) t))))

(defun earley-parse-string (gcat str grammar)
  (earley-parse gcat (tokenize-str str) grammar))

(defun earley-parse-string-and-print (gcat str grammar)
  (print-parse-results str
		       (1+ (length str))
		       (earley-parse gcat (tokenize-str str) grammar)))

(defun print-parse-results (str n chart)
  (dotimes (i n chart)
    (let ((ch (nth i chart)))
      (dolist (state ch)
	(when (null (caddr state))
	  (format t "~d : ~d~%" (subseq str (cadddr state) i) (car state)))))))

(defun earley-parse (gcat toks grammar)
  (earley-parse-0 gcat toks grammar 0
		  (let ((a (list NIL NIL (list gcat) 0)))
		    (earley-enqueue a nil 0))))

(defun earley-parse-0 (gcat toks grammar n chart)
  (if toks
      (earley-parse-0 gcat (cdr toks)
		      grammar (1+ n)
		      (earley-parse-1 (car toks) n grammar chart))
    (earley-parse-1 nil n grammar chart)))

(defun earley-parse-1 (w n grammar chart)
  (let* ((earley-chart chart)
	 (earley-queue (copy-list (nth n chart))))
    (declare (special earley-chart earley-queue))
;    (format t "Starting ~d with queue ~d~%" n earley-queue) ; delete me
    (loop while earley-queue do
	  (let ((state (pop earley-queue)))
	    (if (caddr state)
		(if (assoc (car (caddr state)) grammar)
		    (earley-predictor state grammar n)
		  (earley-scanner state w n))
	      (earley-completer state n))))
    earley-chart))

(defun grules-to-grammar (grules)
  (let ((gram nil)
	(ccount nil))
    (dolist (gr grules gram)
      (let* ((c (cadr gr))
	     (cc (assoc c ccount))
	     (r (char-grule (caddr gr)))
	     (val (nth 3 gr)))
	(if cc
	    (progn
	      (incf (cdr cc)))
	  (progn
	    (push (cons c 1) ccount)))
	(let ((a (assoc c gram)))
	  (if a
	      (nconc a (list (list (car gr) r val)))
	    (push (list c (list (car gr) r val)) gram)))))))

(defun char-grule (g)
  (if g
      (if (stringp (car g))
	  (let* ((r (char-grule (cdr g)))
		 (n (length (car g)))
		 (m n))
	    (dotimes (i n)
	      (decf m)
	      (push (aref (car g) m) r))
	    r)
	(cons (car g) (char-grule (cdr g))))
    nil))

(defun parse-stream (s gcat grammar &optional (evalnum 1))
  (declare (special *last-char* *last-token* *position*))
  (let* ((words nil)
	 (n 0)
	 (chart (earley-enqueue (list NIL NIL (list gcat) 0) nil 0))
	 (ret nil))
    (when (eq *last-token* 'WH)
      (setq *last-token* (read-token s)))
    (loop while (and *last-token* (not ret)) do
	  (setq chart (earley-parse-1 *last-token* n grammar chart))
	  (let ((succ
		 (find-if
		  #'(lambda (state)
		      (and (null (car state))
			   (null (caddr state))))
		  (nth n chart))))
	    (if succ
		(setq ret (list words 
				(chart-to-parse-trees words 0 n gcat grammar chart 3 nil evalnum)))
	      (progn
		(incf n)
		(if (nth n chart)
		    (progn
		      (if words
			  (nconc words (list *last-token*))
			(setq words (list *last-token*)))
		      (setq *last-token* (read-token s)))
		  (progn
		    (setq *chart* chart)
		    (setq *n* n)
		    (fail (format nil "Parsing Problem at position ~d ~d" *position* words))))))))
    (if ret
	ret
      (progn ; otherwise out of stream, see if end parsed
	(setq chart (earley-parse-1 nil n grammar chart))
	(let ((succ
	       (find-if
		#'(lambda (state)
		    (and (null (car state))
			 (null (caddr state))))
		(nth n chart))))
	  (if succ
	      (list words 
		    (chart-to-parse-trees words 0 n gcat grammar chart 3 nil evalnum))
	    (if (find-if-not #'(lambda (x) (eq x 'WH)) words)
		(progn
		  (setq *chart* chart)
		  (setq *n* n)
		  (fail (format nil "Unexpected eof after ~d" words)))
	      nil)))))))

(defun interactive-parse (s gcat grammar &optional (evalnum 1) (prompt "> "))
  (let* ((words nil)
	 (n 0)
	 (chart (earley-enqueue (list NIL NIL (list gcat) 0) nil 0))
	 (ret nil))
    (format s prompt)
    (loop while (not ret) do
	  (let* ((l (read-line s))
		 (toks (tokenize-str l)))
	    (when (eq (car toks) 'WH)
	      (pop toks))
	    (if toks
		(unless (eq (car (last toks)) 'WH)
		  (nconc toks (list 'WH)))
	      (setq toks '(WH)))
	    (loop while (and toks (not ret)) do
		  (let ((tok (pop toks)))
		    (setq chart (earley-parse-1 tok n grammar chart))
		    (let ((succ (find-if
				 #'(lambda (state)
				     (and (null (car state))
					  (null (caddr state))))
				 (nth n chart))))
		      (if succ
			  (progn
			    (setq ret (list words
					    (chart-to-parse-trees words 0 n gcat grammar chart 3 nil evalnum)))
			    (when (and toks (> *verbose* 20))
			      (unless (eq tok 'WH)
				(push tok toks))
			      (format t "Ignoring ~d~%" toks)))
			(progn
			  (if words
			      (nconc words (list tok))
			    (setq words (list tok)))
			  (incf n)
			  (unless (nth n chart)
			    (setq ret (list words nil))))))))))
    ret))

(defun read-token (s)
  (declare (special *last-char* *position*))
  (if *last-char*
      (if (linecomment-char-p *last-char*)
	  (do ((ch (read-char s nil nil) (read-char s nil nil)))
	      ((newline-char-p ch)
	       (setq ch (read-char s nil nil))
	       (setq *last-char* ch)
	       (incf *position*)
	       (read-token s))
	      (incf *position*)
	      )
	(if (whitespace-p *last-char*)
	    (do ((ch (read-char s nil nil) (read-char s nil nil)))
		((not (or (whitespace-p ch) (linecomment-char-p ch)))
		 (setq *last-char* ch)
		 (incf *position*)
		 'WH)
		(when (linecomment-char-p ch)
		  (do ((ch2 (read-char s nil nil) (read-char s nil nil)))
		      ((newline-char-p ch2))
		      (incf *position*)))
		(incf *position*)
		)
	  (let ((ch *last-char*))
	    (setq *last-char* (read-char s nil nil))
	    (incf *position*)
	    ch)))
    nil))

(defun newline-char-p (ch)
  (member ch '(#\newline #\page #\return)))

(defun linecomment-char-p (ch)
  (member ch *linecomment-chars*))

(defun tokenize-str (str)
  (let ((n (length str))
	(tokens (list nil))
	(wh nil))
    (dotimes (i n (cdr tokens))
      (let ((ch (aref str i)))
	(if (whitespace-p ch)
	    (unless wh
	      (nconc tokens (list 'WH))
	      (setq wh t))
	  (progn
	    (setq wh nil)
	    (nconc tokens (list ch))))))))

(defun whitespace-p (ch)
  (member ch '(#\space #\newline #\return)))

(defun grule-arity (gr grammar)
  (if gr
      (if (assoc (car gr) grammar)
	  (1+ (grule-arity (cdr gr) grammar))
	(grule-arity (cdr gr) grammar))
    0))

(defun pretty-print-polish (polish &optional (s *standard-output*))
  (if polish
      (if (> (cdar polish) 0)
	  (let ((rst (cdr polish)))
	    (format s "(~d" (caar polish))
	    (dotimes (i (cdar polish))
	      (format s " ")
	      (setq rst (pretty-print-polish rst s)))
	    (format s ")")
	    rst)
	(progn
	  (format s "~d" (caar polish))
	  (cdr polish)))
    nil))

; order of rules in grammar matters!
; return the first m possible parse trees
(defun chart-to-parse-trees (words start end gcat grammar chart &optional (m 3) (usename nil) (evalnum 1))
  (when (> *verbose* 40)
    (format t "Parsed ~d~%" words))
  (when (> *verbose* 50)
    (let ((i 0))
      (dolist (x (chart-to-parse-trees-polish words start end (list gcat) grammar chart m t))
	(format t "~%Parse Tree ~d:~%" (incf i))
	(pretty-print-polish x)
	(terpri))))
  (mapcar #'(lambda (x)
	      (if usename
		  (list 'quote (apptree-out-of-polish x))
		(let ((ret (fctree-out-of-polish x)))
		  (dotimes (i evalnum ret)
		    (setq ret (eval ret))))))
	  (chart-to-parse-trees-polish words start end (list gcat) grammar chart m usename)))

(defun fctree-out-of-polish (polish)
  (if polish
      (if (> (cdar polish) 0)
	  (let ((f (if (caar polish)
		       (list 'funcall (caar polish))
		     (list 'list)))
		(arg nil)
		(rst (cdr polish)))
	    (dotimes (i (cdar polish))
	      (multiple-value-setq
	       (arg rst)
	       (fctree-out-of-polish rst))
	      (nconc f (list arg)))
	    (values f rst))
	(values (caar polish) (cdr polish)))
    nil))

(defun apptree-out-of-polish (polish)
  (if polish
      (let ((f (caar polish))
	    (arg nil)
	    (rst (cdr polish)))
	(dotimes (i (cdar polish))
	  (multiple-value-setq
	   (arg rst)
	   (apptree-out-of-polish rst))
	  (setq f (cons f arg)))
	(values f rst))
      nil))

(defun chart-to-parse-trees-polish (words start end rst grammar chart &optional (m 3) (usename nil))
  (if (> m 0)
      (if rst
	  (let ((a (assoc (car rst) grammar)))
	    (if a
		(let ((ret nil))
		  (dolist (gr (cdr a))
		    (when (> m 0)
		      (let* ((rule (cadr gr))
			     (rst2 (append rule (cdr rst))))
			(when (consistent-with-parse-chart words start end rst2 grammar chart)
			  (let ((new (chart-to-parse-trees-polish words start end rst2 grammar chart m usename))
				(ar (grule-arity rule grammar)))
			    (setq m (- m (length new)))
			    (setq ret
				  (append ret
					  (mapcar #'(lambda (x)
						      (acons 
						       (if usename
							   (car gr)
							 (caddr gr))
						       ar x))
						  new))))))))
		  ret)
	      (chart-to-parse-trees-polish words (1+ start) end (cdr rst) grammar chart m usename)))
	(list nil))
    nil))

(defun consistent-with-parse-chart (words start end rst grammar chart)
  (if rst
      (let ((a (assoc (car rst) grammar)))
	(if a
	    (consistent-with-parse-chart-2 words start start end (car rst) (cdr rst) grammar chart)
	  (if (eq (nth start words) (car rst))
	      (consistent-with-parse-chart words (1+ start) end (cdr rst) grammar chart)
	    nil)))
    (if (= start end)
	t
      nil)))

(defun consistent-with-parse-chart-2 (words start mid end gcat rst grammar chart)
  (if (> mid end)
      nil
    (or (consistent-with-parse-chart-2 words start (1+ mid) end gcat rst grammar chart)
	(and (find-if #'(lambda (state)
			  (and (eq (car state) gcat)
			       (null (caddr state))
			       (= (cadddr state) start)))
		      (nth mid chart))
	     (consistent-with-parse-chart words mid end rst grammar chart)))))

; evaluate each expression on i until one returns non-NIL
; basically a parsing is valid if it evaluates to non-NIL
; otherwise we take the next parsing
(defun process-parsed-input (i grammar)
  (declare (special grammar))
  (let ((done nil)
	(failinfo nil)
	(failinfo2 nil))
    (loop until (or done (null i)) do
	  (multiple-value-setq
	   (done failinfo)
	   (eval (car i)))
	  (when failinfo
	    (push failinfo failinfo2))
	  (pop i))
    (values grammar (not done) failinfo2)))

(defun add-to-grammar (gcat rule grammar)
  (logtex
   (format nil "Adding grammar rule\\~%~d :: ~d~2%" gcat (cadr rule))) ; delete me
  (when (> *verbose* 10)
    (format t "Adding grammar rule~%~d :: ~d~%" gcat rule)) ; delete me
  (add-to-grammar-rec gcat rule grammar))

(defun add-to-grammar-rec (gcat rule grammar)
  (if grammar
      (if (eq gcat (caar grammar))
	  (cons (cons gcat (cons rule (cdar grammar)))
		(cdr grammar))
	(cons (car grammar)
	      (add-to-grammar-rec gcat rule (cdr grammar))))
    (list (list gcat rule))))
