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
; December 2005
(defvar *sos-types* nil)
(defvar *usable-types* nil)
(defvar *sos-normals* nil)
(defvar *usable-normals* nil)
(defvar *sos-extractions* nil)
(defvar *usable-extractions* nil)
(defvar *goal-normals* nil)

(defvar *max-ctx-len* 3)

(defvar *enumeration-cycles* 0)
(defvar *max-cycles* 500)
(defvar *enumerate-throw-on-success* nil)


(defun initialize-enumeration ()
  (initialize-enumeration-0)
  (initialize-enumeration-1 *global-sigma*))

(defun initialize-enumeration-0 ()
  (setq *enumeration-cycles* 0)
  (setq *sos-types* (list (list *emptyctx* (obj) 0) (list *emptyctx* (prop) 0)))
  (setq *usable-types* nil)
  (setq *sos-normals* nil)
  (setq *usable-normals* nil)
  (setq *sos-extractions* nil)
  (setq *usable-extractions* nil)
  (setq *goal-normals* nil))

(defun initialize-enumeration-1 (sig)
  (dolist (c sig)
    (push (list *emptyctx* c (get c 'dbtype) (get c 'timestamp)) *sos-extractions*)
    (when (get c 'CLAIM)
      (setf (get c 'proposed-solns) nil)
      (push c *goal-normals*))))

(defun eiy ()
  (initialize-enumeration)
  (enumerate))

(defun enumerate ()
  (loop while (and (or *sos-types* *sos-normals* *sos-extractions*)
		   (or (not *max-cycles*) (< *enumeration-cycles* *max-cycles*))) do
	(incf *enumeration-cycles*)
	(when (> *verbose* 60)
	  (format t "Enumeration Cycle ~d~%" *enumeration-cycles*))
;#+:allegro
;        (when (= (mod *enumeration-cycles* 10000) 0)
;	  (excl:dumplisp :name (format nil "enum-~d.dxl" *enumeration-cycles*)))
	(when *sos-types*
	  (let ((ctp (pop *sos-types*)))
	    (let ((ctx (car ctp))
		  (tp (cadr ctp)))
	      (when (> *verbose* 60)
		(format t "Processing Type ~d | ~d~%" (enumerate-output-ctx-string ctx) (output-type-string tp)))
	      (when ctx
		(let* ((newctx (cdr ctx))
		       (newtp (dpi (car ctx) tp)))
		  (enumerate-newtype newctx newtp (caddr ctp))))
	      (when (and (deptype1-p tp ctx) (< (length ctx) *max-ctx-len*))
		(enumerate-newextr (ctx-cons tp ctx) 0 (dbshift-type-n 1 tp) (caddr ctp)))
	      (dolist (n *usable-extractions*)
		(enumerate-weaken-extraction ctp n))
	      (dolist (n *usable-normals*)
		(enumerate-weaken-normal ctp n))
	      (dolist (n *usable-types*)
		(enumerate-weaken-type ctp n))
	      (enumerate-weaken-type ctp ctp)
	      (when (dclass-p tp)
		(dolist (n *usable-normals*)
		  (when (obj-p (caddr n))
		    (dolist (n2 *usable-normals*)
		      (when (pf-p (caddr n2))
			(enumerate-pair n n2 ctp)))))))
	    (push ctp *usable-types*)))
	(when *sos-normals*
	  (let ((cnorm (pop *sos-normals*)))
	    (let ((ctx (car cnorm))
		  (trm (cadr cnorm))
		  (tp (caddr cnorm)))
	      (when (> *verbose* 55)
		(format t "Processing Normal ~d | ~d : ~d~%" (enumerate-output-ctx-string ctx) (output-term-string trm) (output-type-string tp)))
	      (when (eq tp (prop))
		(let ((newtp (pf trm)))
		  (enumerate-newtype ctx newtp (cadddr cnorm))))
	      (when (heq tp *pred*)
		(let ((newtp (dclass trm)))
		  (enumerate-newtype ctx newtp (cadddr cnorm))))
	      (dolist (ctp *usable-types*)
		(enumerate-weaken-normal ctp cnorm))
	      (dolist (e *usable-extractions*)
		(enumerate-app e cnorm))
	      (when (obj-p tp)
		(dolist (n *usable-normals*)
		  (when (pf-p (caddr n))
		    (dolist (ctp *usable-types*)
		      (when (dclass-p (cadr ctp))
			(enumerate-pair cnorm n ctp))))))
	      (when (pf-p tp)
		(dolist (n *usable-normals*)
		  (when (obj-p (caddr n))
		    (dolist (ctp *usable-types*)
		      (when (dclass-p (cadr ctp))
			(enumerate-pair n cnorm ctp))))))
	      (when ctx
		(let* ((newctx (cdr ctx))
		       (newtrm (lam trm))
		       (newtp (dpi (car ctx) tp)))
		  (enumerate-newnormal newctx newtrm newtp (cadddr cnorm))))
	      )
	    (push cnorm *usable-normals*)))
	(when *sos-extractions*
	  (let ((cextr (pop *sos-extractions*)))
	      (when (> *verbose* 55)
		(format t "Processing Extr ~d | ~d : ~d~%" (enumerate-output-ctx-string (car cextr)) (output-term-string (cadr cextr)) (output-type-string (caddr cextr))))
	    (if (dpi-p (caddr cextr))
		(dolist (n *usable-normals*)
		  (enumerate-app cextr n))
	      (if (dclass-p (caddr cextr))
		  (progn
		    (enumerate-newextr (car cextr) (fst (cadr cextr)) (obj) (cadddr cextr))
		    (enumerate-newextr (car cextr) (snd (cadr cextr))
				       (pf (pair-prop (caddr cextr) (fst (cadr cextr))))
				       (cadddr cextr)))
		(enumerate-newnormal (car cextr) (cadr cextr) (caddr cextr) (cadddr cextr)))) ; only enumerating eta-long forms
	    (dolist (ctp *usable-types*)
	      (enumerate-weaken-extraction ctp cextr))
	    (push cextr *usable-extractions*)))
	))

(defmacro aconc (a b)
  (list 'if b
	(list 'nconc b (list 'list a))
	(list 'push a b)))

(defun enumerate-newtype (ctx tp timestamp)
  (setq tp (normalize-type tp)) ; to make it eta short
    (unless (ctx-type-valid-p ctx tp)
      (format t "Bad Type ~d | ~d~%" (enumerate-output-ctx-string ctx) (output-type-string tp))
      (break))
  (when (deptype2-p tp ctx) ; make sure it's really order 2
    (unless (or (find-if #'(lambda (x)
			     (and (heq ctx (car x))
				  (ctx-types-eq ctx tp (cadr x))))
			 *sos-types*)
		(find-if #'(lambda (x)
			     (and (heq ctx (car x))
				  (ctx-types-eq ctx tp (cadr x))))
			 *usable-types*))
      (when (> *verbose* 50)
	(format t "New Type ~d | ~d~%" (enumerate-output-ctx-string ctx) (output-type-string tp)))
      (aconc (list ctx tp timestamp) *sos-types*)
      )))
  
(defun enumerate-newnormal (ctx trm tp timestamp)
  (setq tp (normalize-type tp)) ; to make it eta short
  (setq trm (normalize trm)) ; to make it eta short
    (unless (ctx-term-type-p ctx trm tp)
      (format t "Bad Normal ~d | ~d : ~d~%" (enumerate-output-ctx-string ctx) (output-term-string trm) (output-type-string tp))
      (break))
  (when (deptype2-p tp ctx) ; make sure it's really order 2
    (unless (or (find-if #'(lambda (x)
			     (and (heq ctx (car x))
				  (ctx-types-eq ctx tp (caddr x))
				  (ctx-terms-eq-type ctx trm (cadr x) tp)))
			 *sos-normals*)
		(find-if #'(lambda (x)
			     (and (heq ctx (car x))
				  (ctx-types-eq ctx tp (caddr x))
				  (ctx-terms-eq-type ctx trm (cadr x) tp)))
			 *usable-normals*))
      (when (> *verbose* 45)
	(format t "New Normal ~d | ~d : ~d~%" (enumerate-output-ctx-string ctx) (output-term-string trm) (output-type-string tp)))
      (aconc (list ctx trm tp timestamp) *sos-normals*)
      (when (eq ctx *emptyctx*)
					; check if this satisfies a goal:
	(dolist (x *goal-normals*)
	  (unless (>= timestamp (get x 'timestamp))
	    (when (ctx-types-eq ctx (get x 'dbtype) tp)
	      (format t "*** Solved ~d~%~d~%"
		      x
		      (output1-normal-string trm))
	      (push trm (get x 'proposed-solns))
	      (when *enumerate-throw-on-success*
		(when (> *verbose* 10)
		  (format t "Solution For ~d Found By Enumeration!~%~S~%~d~%~d~%~d~%"
			  x trm (output-term-string trm) (output1-normal-string trm)
			  (term-direct-latex trm)))
		(throw 'success trm)
		))))))))

(defun enumerate-app (e n)
  (when (and (heq (car e) (car n))
	     (dpi-p (caddr e))
	     (heq (dpi-dom (caddr e)) (caddr n)))
    (enumerate-newextr (car e)
		       (app (cadr e) (cadr n))
		       (dbsubst-type-0 (dpi-cod (caddr e)) (cadr n))
		       (max (cadddr e) (cadddr n)))))

(defun enumerate-newextr (ctx trm tp timestamp)
  (setq tp (normalize-type tp)) ; to make it eta short
  (setq trm (normalize trm)) ; to make it eta short
  (unless (heq (ctx-extract-type ctx trm) tp)
    (format t "Invalid Extraction ~d | ~d : ~d~%" (enumerate-output-ctx-string ctx) (output-term-string trm) (output-type-string tp))
    (break))
  (when (deptype2-p tp ctx) ; make sure it's really order 2
    (unless (or (find-if #'(lambda (x)
			     (and (heq ctx (car x))
				  (ctx-extract-eq-type ctx trm (cadr x))))
			 *sos-extractions*)
		(find-if #'(lambda (x)
			     (and (heq ctx (car x))
				  (ctx-types-eq ctx tp (caddr x))
				  (ctx-extract-eq-type ctx trm (cadr x))))
			 *usable-extractions*))
      (when (> *verbose* 45)
	(format t "New Extraction ~d | ~d : ~d~%" (enumerate-output-ctx-string ctx) (output-term-string trm) (output-type-string tp)))
      (aconc (list ctx trm tp timestamp) *sos-extractions*))))

; assumes n1 is obj and n2 is pf and ctp is dclass
(defun enumerate-pair (n1 n2 ctp)
  (when (and (heq (car n1) (car n2))
	     (heq (car n1) (car ctp))
	     (heq (pair-prop (cadr ctp) (cadr n1))
		  (pf-prop (caddr n2))))
    (enumerate-newnormal (car n1)
			 (pair (cadr n1) (cadr n2))
			 (cadr ctp)
			 (max (cadddr n1) (cadddr n2) (caddr ctp)))))

(defun enumerate-weaken-type (ctp ctp2)
  (when (and (heq (car ctp) (car ctp2))
	     (deptype1-p (cadr ctp) (car ctp))
	     (< (length (car ctp)) *max-ctx-len*))
    (enumerate-newtype (ctx-cons (cadr ctp) (car ctp))
		       (dbshift-type-n 1 (cadr ctp2))
		       (max (caddr ctp) (caddr ctp2)))))

(defun enumerate-weaken-normal (ctp n)
  (when (and (heq (car ctp) (car n))
	     (deptype1-p (cadr ctp) (car ctp))
	     (< (length (car ctp)) *max-ctx-len*))
    (enumerate-newnormal (ctx-cons (cadr ctp) (car ctp))
			 (dbshift-n 1 (cadr n))
			 (dbshift-type-n 1 (caddr n))
			 (max (caddr ctp) (cadddr n)))))

(defun enumerate-weaken-extraction (ctp n)
  (when (and (heq (car ctp) (car n))
	     (deptype1-p (cadr ctp) (car ctp))
	     (< (length (car ctp)) *max-ctx-len*))
    (enumerate-newextr (ctx-cons (cadr ctp) (car ctp))
		       (dbshift-n 1 (cadr n))
		       (dbshift-type-n 1 (caddr n))
		       (max (caddr ctp) (cadddr n)))))

; this is only for convenience
(defun enumerate-output-ctx-string (ctx)
  (if (consp ctx)
      (if (consp (cdr ctx))
	  (format nil "~d,~d"
		  (output-type-string (car ctx))
		  (enumerate-output-ctx-string (cdr ctx)))
	(output-type-string (car ctx)))
    (format nil ".")))

(defun examine-proposed-solns ()
  (dolist (g *goal-normals*)
    (let ((ps (get g 'proposed-solns)))
      (loop while ps do
	    (format t "Proposed Solution for ~d~%~d~%Accept?"
		    g (output1-normal-string (car ps)))
	    (when (read)
	      (setq ps nil)
	      (setf (get g 'claim) nil)
	      (setf (get g 'abbrev) t)
	      (setf (get g 'defn) (car ps)))
	    (when ps (pop ps))))))

; do it by enumeration
;(defun dibe (goal &optional sos usable ctx)
;  (if (and (symbolp goal) (get goal 'claim))
;      (progn
;	(setq *enumeration-cycles* 0)
;	(setq *sos-types* nil)
;	(setq *usable-types* (list (list *emptyctx* (obj) 0) (list *emptyctx* (prop) 0)))
;	(setq *sos-normals* nil)
;	(setq *usable-normals* nil)
;	(setq *sos-extractions* nil)
;	(setq *usable-extractions* nil)
;	(dolist (c *global-sigma*)
;	  (unless (or (member c sos) (member c usable)
;		      (>= (get c 'timestamp) (get goal 'timestamp)))
;	    (push (list ctx c (get c 'dbtype) (get c 'timestamp)) *usable-extractions*)))
;	(dolist (c usable)
;	  (push (list ctx c (get c 'dbtype) (get c 'timestamp)) *usable-extractions*))
;	(dolist (c sos)
;	  (push (list ctx c (get c 'dbtype) (get c 'timestamp)) *sos-extractions*))
;	(setf (get goal 'proposed-solns) nil)
;	(setq *goal-normals* (list goal))
;	(setq *enumerate-throw-on-success* t)
;	(let ((trm (catch 'success (enumerate))))
;	  trm))
;    (fail "Not a valid goal for dibe" goal sos)))
    
