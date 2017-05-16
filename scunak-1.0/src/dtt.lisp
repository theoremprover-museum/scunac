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
; November 2005
; new version of dep type theory code
; which uses explicit contexts, hash tables,
; etc.  This does not explicitly build on simply typed terms.

(defvar *check-simple-type-premisses* nil)
; ; *checking-style*
; ; A - Use dependent types to determine equality of terms up to pf irrelevance (possibly checking simply typed premisses, see *check-simple-type-premisses*) - this is the original typing algorithm (when *check-simple-type-premisses* is nil)
; ; B - Use simple types to determine equality of terms up to pf irrelevance
; ; C - Use dependent types, but only referencing what corresponds to the simply typed erasure (acts like 2, but without erasing)
; ; D - Reduce to checking equality with strong type checking
; ; E - Reduce to checking equality with strong type checking (version reported at IJCAR2006)
; ; E2 - Same as E but only splits checking dclass types if one of the terms is explicitly a pair
; ; F - use explicit substitutions (experimental)
(defvar *checking-style* 'E)

; A - substitute using recursive algorithm and normalize using redexes (strategy?)
; B - special algorithm for second order types and terms?
(defvar *normalization-style* 'A)

(defvar *proof-irrelevance-used* nil)

(defvar *use-eta* t)
(defvar *use-sp* t)

(defvar *num-betas* 0)
(defvar *num-etas* 0)
(defvar *num-pi1s* 0)
(defvar *num-pi2s* 0)
(defvar *num-sps* 0)

(defvar *use-hash* nil)
(defvar *obj* 'OBJ)
(defvar *prop* 'PROP)
(defvar *pf-hash* (make-hash-table :test #'eq))
(defvar *class-hash* (make-hash-table :test #'eq))

(defvar *pi-hash* (make-hash-table :test #'eq))

(defvar *lam-hash* (make-hash-table :test #'eq))
(defvar *app-hash* (make-hash-table :test #'eq))
(defvar *pair-hash* (make-hash-table :test #'eq))
(defvar *fst-hash* (make-hash-table :test #'eq))
(defvar *snd-hash* (make-hash-table :test #'eq))

(defvar *emptyctx* NIL)
(defvar *ctx-hash* (make-hash-table :test #'eq))

(setq *timing* nil)
(setq *timing-stack* nil)

;(defvar *term-second-order-hash* (make-hash-table :test #'eq))
;(defvar *type-second-order-hash* (make-hash-table :test #'eq))

; for judgments:
;(defvar *ctx-valid-hash* (make-hash-table :test #'eq))
(defvar *ctx-type-valid-hash* (make-hash-table :test #'eq))
(defvar *ctx-term-type-hash* (make-hash-table :test #'eq))
(defvar *ctx-extract-type-hash* (make-hash-table :test #'eq))
(defvar *ctx-terms-eq-type-hash* (make-hash-table :test #'eq))
(defvar *ctx-extractions-eq-type-hash* (make-hash-table :test #'eq))
(defvar *ctx-types-eq-hash* (make-hash-table :test #'eq))

(defvar *term-normal-hash* (make-hash-table :test #'eq))
(defvar *nin-term-hash* (make-hash-table :test #'eq))

(defun getsinglehash (key1 h)
  (when *use-hash*
    (gethash key1 h)))

(defun setsinglehash (key1 val h)
  (when *use-hash*
    (setf (gethash key1 h) val)))

(defun getdoublehash (key1 key2 h)
  (when *use-hash*
    (let ((h2 (gethash key1 h)))
      (if h2
	  (gethash key2 h2)
	nil))))

(defun setdoublehash (key1 key2 val h)
  (when *use-hash*
    (let ((h2 (gethash key1 h)))
      (if h2
	  (setf (gethash key2 h2) val)
	(let ((h21 (make-hash-table :test #'eq)))
	  (setf (gethash key2 h21) val)
	  (setf (gethash key1 h) h21))))))

(defun gettriplehash (key1 key2 key3 h)
  (when *use-hash*
    (let ((h2 (gethash key1 h)))
      (if h2
	  (let ((h3 (gethash key2 h2)))
	    (if h3
		(gethash key3 h3)
	      nil))
	nil))))

(defun settriplehash (key1 key2 key3 val h)
  (when *use-hash*
    (let ((h2 (gethash key1 h)))
      (if h2
	  (let ((h3 (gethash key2 h2)))
	    (if h3
		(setf (gethash key3 h3) val)
	      (let ((h31 (make-hash-table :test #'eq)))
		(setf (gethash key2 h2) h31)
		(setf (gethash key3 h31) val))))
	(let ((h21 (make-hash-table :test #'eq))
	      (h31 (make-hash-table :test #'eq)))
	  (setf (gethash key3 h31) val)
	  (setf (gethash key2 h21) h31)
	  (setf (gethash key1 h) h21))))))

(defun get4hash (key1 key2 key3 key4 h)
  (when *use-hash*
    (let ((h2 (gethash key1 h)))
      (if h2
	  (let ((h3 (gethash key2 h2)))
	    (if h3
		(let ((h4 (gethash key3 h3)))
		  (if h4
		      (gethash key4 h4)
		    nil))
	      nil))
	nil))))

(defun set4hash (key1 key2 key3 key4 val h)
  (when *use-hash*
    (let ((h2 (gethash key1 h)))
      (if h2
	  (let ((h3 (gethash key2 h2)))
	    (if h3
		(let ((h4 (gethash key3 h3)))
		  (if h4
		      (setf (gethash key4 h4) val)
		    (let ((h41 (make-hash-table :test #'eq)))
		      (setf (gethash key3 h3) h41)
		      (setf (gethash key4 h41) val))))
	      (let ((h31 (make-hash-table :test #'eq))
		    (h41 (make-hash-table :test #'eq)))
		(setf (gethash key2 h2) h31)
		(setf (gethash key3 h31) h41)
		(setf (gethash key4 h41) val))))
	(let ((h21 (make-hash-table :test #'eq))
	      (h31 (make-hash-table :test #'eq))
	      (h41 (make-hash-table :test #'eq)))
	  (setf (gethash key4 h41) val)
	  (setf (gethash key3 h31) h41)
	  (setf (gethash key2 h21) h31)
	  (setf (gethash key1 h) h21))))))

(defun initialize-hashtables ()
  (when *use-hash*
    (setq *pf-hash* (make-hash-table :test #'eq))
    (setq *class-hash* (make-hash-table :test #'eq))
    (setq *pi-hash* (make-hash-table :test #'eq))
    (setq *lam-hash* (make-hash-table :test #'eq))
    (setq *app-hash* (make-hash-table :test #'eq))
    (setq *pair-hash* (make-hash-table :test #'eq))
    (setq *fst-hash* (make-hash-table :test #'eq))
    (setq *snd-hash* (make-hash-table :test #'eq))
    (setq *ctx-hash* (make-hash-table :test #'eq))
;  (setq *ctx-valid-hash* (make-hash-table :test #'eq))
    (setq *ctx-type-valid-hash* (make-hash-table :test #'eq))
    (setq *ctx-term-type-hash* (make-hash-table :test #'eq))
    (setq *ctx-extract-type-hash* (make-hash-table :test #'eq))
    (setq *ctx-terms-eq-type-hash* (make-hash-table :test #'eq))
    (setq *ctx-extractions-eq-type-hash* (make-hash-table :test #'eq))
    (setq *ctx-types-eq-hash* (make-hash-table :test #'eq))
    (setq *term-normal-hash* (make-hash-table :test #'eq))
    (setq *nin-term-hash* (make-hash-table :test #'eq)))
  (setq *pred* (dpi (obj) (prop)))
  (setq *breln* (dpi (obj) *pred*))
  )

; pretypes
(defun obj ()
  *obj*)

(defun prop ()
  *prop*)

(defun pf (trm)
  (let ((h (getsinglehash trm *pf-hash*)))
    (or h
	(let ((a (cons 'PF trm)))
	  (setsinglehash trm *pf-hash* a)
	  a))))
      
(defun dclass (trm)
  (let ((h (getsinglehash trm *class-hash*)))
    (or h
	(let ((a (cons 'DCLASS TRM)))
	  (setsinglehash trm *class-hash* a)
	  a))))

(defun dpi (dom cod)
  (let ((h (getdoublehash dom cod *pi-hash*)))
    (or h
	(let ((a (cons 'DPI (cons dom cod))))
	  (setdoublehash dom cod a *pi-hash*)
	  a))))

(defun dpi-p (n)
  (and (consp n) (eq (car n) 'dpi)))

(defun dpi-dom (n)
  (cadr n))

(defun dpi-cod (n)
  (cddr n))

(defun dclass-p (n)
  (and (consp n) (eq (car n) 'dclass)))

(defun dclass-pred (n)
  (cdr n))

(defun pf-p (n)
  (and (consp n) (eq (car n) 'pf)))

(defun pf-prop (n)
  (cdr n))

(defun prop-p (n)
  (eq n *prop*))

(defun obj-p (n)
  (eq n *obj*))

(defun deptype-case (dtp)
  (cond ((dpi-p dtp) 'DPI)
	((dclass-p dtp) 'DCLASS)
	((pf-p dtp) 'PF)
	((obj-p dtp) 'OBJ)
	((prop-p dtp) 'PROP)
	(t nil)))

(defvar *pred* (dpi (obj) (prop)))
(defvar *breln* (dpi (obj) *pred*))

(defun pred-p (n)
  (eq n *pred*))

; preterms
(defun app (f x)
  (let ((h (getdoublehash f x *app-hash*)))
    (or h
	(let ((a (cons 'APP (cons f x))))
	  (setdoublehash f x a *app-hash*)
	  a))))

(defun lam (m)
  (let ((h (getsinglehash m *lam-hash*)))
    (or h
	(let ((a (cons 'LAM m)))
	  (setsinglehash m *lam-hash* a)
	  a))))

(defun pair (x p)
  (let ((h (getdoublehash x p *pair-hash*)))
    (or h
	(let ((a (cons 'PAIR (cons x p))))
	  (setdoublehash x p a *pair-hash*)
	  a))))

(defun fst (u)
  (let ((h (getsinglehash u *fst-hash*)))
    (or h
	(let ((a (cons 'FST u)))
	  (setsinglehash u *fst-hash* a)
	  a))))

(defun snd (u)
  (let ((h (getsinglehash u *snd-hash*)))
    (or h
	(let ((a (cons 'SND u)))
	  (setsinglehash u *snd-hash* a)
	  a))))

(defun app-n (f l)
  (if l
      (app-n (app f (car l)) (cdr l))
    f))

(defun app-l (f &rest l)
  (app-n f l))

(defun app-p (trm)
  (and (consp trm) (eq (car trm) 'APP)))

(defun app-func (trm)
  (cadr trm))

(defun app-arg (trm)
  (cddr trm))

(defun lam-p (trm)
  (and (consp trm) (eq (car trm) 'LAM)))

(defun lam-body (trm)
  (cdr trm))

(defun pair-p (trm)
  (and (consp trm) (eq (car trm) 'PAIR)))

(defun fst-p (trm)
  (and (consp trm) (eq (car trm) 'FST)))

(defun snd-p (trm)
  (and (consp trm) (eq (car trm) 'SND)))

(defun evar-p (trm)
  (and (symbolp trm) (get trm 'evar)))

(defun bvar-p (trm)
  (and (symbolp trm) (get trm 'bvar)))

(defun const-p (trm)
  (and (symbolp trm) (get trm 'const)))

(defun abbrev-p (trm)
  (and (symbolp trm) (get trm 'abbrev)))

(defun pair-fst (trm)
  (cadr trm))

(defun pair-snd (trm)
  (cddr trm))

(defun fst-arg (trm)
  (cdr trm))

(defun snd-arg (trm)
  (cdr trm))

(defun term-case (dtp)
  (cond ((app-p dtp) 'APP)
	((lam-p dtp) 'LAM)
	((pair-p dtp) 'PAIR)
	((fst-p dtp) 'FST)
	((snd-p dtp) 'SND)
	((numberp dtp) 'DEBRUIJN)
	(t 'BASIC)))

; prectx's
(defun ctx-nil ()
  *emptyctx*)

(defun ctx-cons (tp ctx)
  (let ((h (getdoublehash tp ctx *ctx-hash*)))
    (if h
	h
      (let ((ctx2 (cons tp ctx)))
	(setdoublehash tp ctx ctx2 *ctx-hash*)
	ctx2))))

(defun emptyctx-p (x)
  (eq x *emptyctx*))

(defun heq (x y)
  (if *use-hash*
      (eq x y)
    (equal x y)))

; normalization, assumes normalization of term will terminate
;(defun normalize (trm)
;  (timing-on 'NORMALIZE)
;  (let ((inittime (get-internal-run-time)))
;    (let ((ntrm (normalize-real trm)))
;      (timing-off 'NORMALIZE)
;      ntrm)))

(defun normalize (trm)
  (let ((h (getsinglehash trm *term-normal-hash*)))
    (or h
	(let ((ntrm (normalize-1 trm)))
	  (setsinglehash trm *term-normal-hash* ntrm)
	  ntrm))))

(defun normalize-1 (trm)
  (cond ((app-p trm)
	 (let ((m (normalize (app-func trm)))
	       (n (normalize (app-arg trm))))
	   (if (lam-p m)
	       (progn
		 (incf *num-betas*)
		 (normalize (dbsubst-0 (lam-body m) n))
		 )
	     (app m n))))
	((lam-p trm)
	 (let ((l (normalize (lam-body trm))))
	   (if (and (app-p l) (eq (app-arg l) 0)
		    (not (nintrm-p 0 (app-func l)))
		    *use-eta*)
	       (progn
		 (incf *num-etas*)
		 (dbshift-n -1 (app-func l))
		 )
	     (lam l))))
	((pair-p trm)
	 (let ((x (normalize (pair-fst trm)))
	       (p (normalize (pair-snd trm))))
	   (if (and (fst-p x) (snd-p p) (heq (fst-arg x) (snd-arg p))
		    *use-sp*)
	       (progn
		 (incf *num-sps*)
		 (fst-arg x))
	     (pair x p))))
	((fst-p trm)
	 (let ((u (normalize (fst-arg trm))))
	   (if (pair-p u)
	       (progn
		 (incf *num-pi1s*)
		 (pair-fst u))
	     (fst u))))
	((snd-p trm)
	 (let ((u (normalize (snd-arg trm))))
	   (if (pair-p u)
	       (progn
		 (incf *num-pi2s*)
		 (pair-snd u))
	     (snd u))))
	(t trm)))

(defun normalize-type (tp)
  (cond ((dpi-p tp)
	 (dpi (normalize-type (dpi-dom tp)) (normalize-type (dpi-cod tp))))
	((dclass-p tp)
	 (dclass (normalize (dclass-pred tp))))
	((pf-p tp)
	 (pf (normalize (pf-prop tp))))
	(t tp)))

(defun nintrm-p (n trm)
  (let ((h (getdoublehash n trm *nin-term-hash*)))
    (if h
	(eq h t)
      (let ((z (nintrm-1-p n trm)))
	(setdoublehash n trm (if z t 'f) *nin-term-hash*)
	z))))

(defun nintrm-1-p (n trm)
  (if (consp trm)
      (case (car trm)
	    (APP (or (nintrm-p n (app-func trm)) (nintrm-p n (app-arg trm))))
	    (PAIR (or (nintrm-p n (pair-fst trm)) (nintrm-p n (pair-snd trm))))
	    (LAM (nintrm-p (1+ n) (lam-body trm)))
	    (FST (nintrm-p n (fst-arg trm)))
	    (SND (nintrm-p n (snd-arg trm)))
	    (t nil))
    (eq trm n)))

(defun nintrm-type-p (n tp)
  (cond ((dpi-p tp)
	 (or (nintrm-type-p n (dpi-dom tp))
	     (nintrm-type-p (1+ n) (dpi-cod tp))))
	((dclass-p tp)
	 (nintrm-p n (dclass-pred tp)))
	((pf-p tp)
	 (nintrm-p n (pf-prop tp)))
	(t nil)))

;(defun dbsubst (m f sig)
;  (timing-on 'DBSUBST)
;  (let ((inittime (get-internal-run-time)))
;    (let ((r (dbsubst-real m f sig)))
;      (timing-off 'DBSUBST)
;      r)))

(defun dbsubst (m f sig)
  (dbsubst-real m f sig))

(defun dbsubst-real (m f sig)
  (cond ((app-p m)
	 (app (dbsubst-real (app-func m) f sig)
	      (dbsubst-real (app-arg m) f sig)))
	((lam-p m)
	 (lam (dbsubst-real (lam-body m) #'IDENTITY (cons 0 (cons #'(lambda (x) (1+ (funcall f x))) sig)))))
	((pair-p m)
	 (pair (dbsubst-real (pair-fst m) f sig)
	       (dbsubst-real (pair-snd m) f sig)))
	((fst-p m)
	 (fst (dbsubst-real (fst-arg m) f sig)))
	((snd-p m)
	 (snd (dbsubst-real (snd-arg m) f sig)))
	((numberp m)
	 (if (eq sig 'ID)
	     (funcall f m)
	   (if (= m 0)
	       (dbsubst-real (car sig) f 'ID)
	     (dbsubst-real (- m 1) #'(lambda (x) (funcall f (funcall (cadr sig) x))) (cddr sig)))))
	(t m)))

(defun dbsubst-type (m f sig)
  (cond ((dpi-p m)
	 (dpi (dbsubst-type (dpi-dom m) f sig)
	      (dbsubst-type (dpi-cod m)
			    #'IDENTITY (cons 0 (cons #'(lambda (x) (1+ (funcall f x))) sig)))))
	((dclass-p m)
	 (dclass (dbsubst (dclass-pred m) f sig)))
	((pf-p m)
	 (pf (dbsubst (pf-prop m) f sig)))
	(t m)))

(defun dbsubst-type-0 (dtp a)
  (dbsubst-type dtp #'identity (cons a (cons #'identity 'ID))))

(defun dbsubst-0 (trm a)
  (dbsubst trm #'identity (cons a (cons #'identity 'ID))))

(defun dbshift-type-n (n trm)
  (dbsubst-type trm #'(lambda (i) (+ i n)) 'ID))

(defun dbshift-n (n trm)
  (dbsubst trm #'(lambda (i) (+ i n)) 'ID))

(defun dbsubst-normalize (m f sig)
  (case *normalization-style*
	(A (normalize (dbsubst m f sig)))
	(t (normalize (dbsubst m f sig))) ; default to A
	))

(defun dbsubst-normalize-type (m f sig)
  (case *normalization-style*
	(A (normalize-type (dbsubst-type m f sig)))
	(t (normalize-type (dbsubst-type m f sig))) ; default to A
	))

(defun dbsubst-normalize-0 (m a)
  (case *normalization-style*
	(A (normalize (dbsubst-0 m a)))
	(t (normalize (dbsubst-0 m a))) ; default to A
	))

(defun dbsubst-normalize-type-0 (m a)
  (case *normalization-style*
	(A (normalize-type (dbsubst-type-0 m a)))
	(t (normalize-type (dbsubst-type-0 m a))) ; default to A
	))

;(defun ctx-valid-p (ctx)
;  (let ((h (getsinglehash ctx *ctx-valid-hash*)))
;    (if h
;	(eq h T)
;      (let ((z (ctx-valid-1-p ctx)))
;	(setsinglehash ctx *ctx-valid-hash* (if z t 'f))
;	z))))
;
;(defun ctx-valid-1-p (ctx)
;  (if (emptyctx-p ctx)
;      t
;    (ctx-type-valid-p (cdr ctx) (car ctx)) ; Lemma: If this says T, then (ctx-valid-1-p (cdr ctx)) would return T
;    ))

; assumes tp is beta normal
(defun ctx-type-valid-p (ctx tp)
  (let ((h (getdoublehash ctx tp *ctx-type-valid-hash*)))
    (if h
	(eq h T)
      (let ((z (ctx-type-valid-1-p ctx tp)))
	(setdoublehash ctx tp (if z t 'f) *ctx-type-valid-hash*)
	z))))

(defun ctx-type-valid-1-p (ctx tp)
  (cond ((dpi-p tp)
	 (and (ctx-type-valid-p ctx (dpi-dom tp))
	      (ctx-type-valid-p (ctx-cons (dpi-dom tp) ctx) (dpi-cod tp))))
	((dclass-p tp)
	 (ctx-term-type-p ctx (dclass-pred tp) *pred*))
	((pf-p tp)
	 (ctx-term-type-p ctx (pf-prop tp) *prop*))
	((prop-p tp) t)
	((obj-p tp) t)
	(t nil)))

; assumes trm and tp are beta normal
(defun ctx-term-type-p (ctx trm tp)
  (let ((h (gettriplehash ctx trm tp *ctx-term-type-hash*)))
    (if h
	(eq h t)
      (let ((z (ctx-term-type-1-p ctx trm tp)))
	(settriplehash ctx trm tp
		       (if z t 'F)
		       *ctx-term-type-hash*)
	z))))

(defun ctx-term-type-1-p (ctx trm tp)
;  (timing-on 'ctx-term-type-p-1)
  (prog1
      (if (eq *checking-style* 'D)
	  (ctx-normal-eq-in-type-D ctx trm trm tp)
	(if (member *checking-style* '(E E2))
	    (ctx-normal-eq-in-type-E ctx trm trm tp)
	  (if (eq *checking-style* 'F)
	      (let ((ptrm (precook-term trm)))
		(ctx-normal-eq-in-type-F (precook-ctx ctx) ptrm ptrm (precook-type tp)))
	    (ctx-term-type-2-p ctx trm tp))))
;    (timing-off 'ctx-term-type-p-1)
    ))

(defun ctx-term-type-2-p (ctx trm tp)
  (cond ((dpi-p tp)
	 (ctx-term-type-p (ctx-cons (dpi-dom tp) ctx) (gen-lam-body trm) (dpi-cod tp)))
	((dclass-p tp)
	 (let ((phi (dclass-pred tp))
	       (f (gen-pair-fst trm)))
	   (and (ctx-term-type-p ctx f (obj))
		(or (not *check-simple-type-premisses*) (has-simple-type (typeerase-ctx ctx) (app phi f) 'O))
		(ctx-term-type-p ctx (gen-pair-snd trm) (pf (normalize (app phi f)))))))
	((pf-p tp)
	 (let ((etp
		(ctx-extract-type ctx trm)))
	   (if (and etp (pf-p etp))
	       (case *checking-style*
		     (A (ctx-terms-eq-type ctx (pf-prop tp) (pf-prop etp) *prop*))
		     (C (ctx-terms-eq-type-C ctx (pf-prop tp) (pf-prop etp) *prop*))
		     (t (ctx-terms-eq-stype (typeerase-ctx ctx) (pf-prop tp) (pf-prop etp) 'O)))
	     (progn
	       (when (> *verbose* 20)
		 (format t "Context:~%")
		 (dotimes (i (length ctx))
		   (format t "~d ~d~%" i (output-type-string (nth i ctx))))
		 (if etp
		     (if (pf-p etp)
			 (format t "Term: ~d~%Extracted proof of ~d~%Expected proof of ~d~%"
				 (output-term-string trm)
				 (output-term-string (pf-prop etp))
				 (output-term-string (pf-prop tp)))
		       (format t "Term: ~d~%Expected proof, but extracted ~d~%"
			       (output-term-string trm)
			       (output-type-string etp)
			       ))
		   (format t "Term Ill-typed: ~d~%"
			   (output-term-string trm))))
	       nil))))
	(t ; otherwise obj or prop
	 (let ((etp
		(ctx-extract-type ctx trm)))
	   (if etp
	       (equal tp etp)
	     (progn
	       (when (> *verbose* 20)
		 (format t "Context:~%")
		 (dotimes (i (length ctx))
		   (format t "~d ~d~%" i (output-type-string (nth i ctx))))
		 (format t "Term Ill-typed: ~d~%"
			 (output-term-string trm)))
	       nil))))))

(defun ctx-extract-type (ctx trm)
  (let ((h (getdoublehash ctx trm *ctx-extract-type-hash*)))
    (or h
	(let ((z (ctx-extract-type-1 ctx trm)))
	  (setdoublehash ctx trm z
			 *ctx-extract-type-hash*)
	  z))))

(defun ctx-extract-type-1 (ctx trm)
;  (timing-on 'ctx-extract-type-1)
  (prog1
      (if (eq *checking-style* 'D)
	  (ctx-extr-eq-in-type-D ctx trm trm)
	(if (member *checking-style* '(E E2))
	    (ctx-extr-eq-in-type-E ctx trm trm)
	  (if (eq *checking-style* 'F)
	      (let ((ptrm (precook-term trm)))
		(postcook-type (ctx-extr-eq-in-type-F (precook-ctx ctx) ptrm ptrm)))
	    (ctx-extract-type-2 ctx trm))))
;    (timing-off 'ctx-extract-type-1)
    ))

(defun ctx-extract-type-2 (ctx trm)
  (cond ((app-p trm)
	 (let ((ftp (ctx-extract-type ctx (app-func trm))))
	   (if (and ftp (dpi-p ftp))
	       (let ((dom (dpi-dom ftp))
		     (a (app-arg trm)))
		 (if (and (ctx-term-type-p ctx a dom)
			  (or (not *check-simple-type-premisses*) (simply-valid-p (typeerase-ctx ctx) (dbsubst-type-0 (dpi-cod ftp) a))))
		     (normalize-type (dbsubst-type-0 (dpi-cod ftp) a))
		   nil))
	     nil)))
	((fst-p trm)
	 (let ((etp (ctx-extract-type-1 ctx (fst-arg trm))))
	   (if (and etp (dclass-p etp))
	       (obj)
	     nil)))
	((snd-p trm)
	 (let ((etp (ctx-extract-type-1 ctx (snd-arg trm))))
	   (if (and (dclass-p etp)
		    (or (not *check-simple-type-premisses*) (has-simple-type (typeerase-ctx ctx) (app (dclass-pred etp) (fst (snd-arg trm))) 'O)))
	       (pf (normalize (app (dclass-pred etp) (fst (snd-arg trm)))))
	     nil)))
	((numberp trm)
	 (dbshift-type-n (1+ trm) (nth trm ctx)))
	((symbolp trm)
	 (get trm 'dbtype))
	(t nil)))

(defun ctx-types-eq (ctx tp1 tp2)
  (let ((h (gettriplehash ctx tp1 tp2 *ctx-types-eq-hash*)))
    (if h
	(eq h T)
      (let ((z (ctx-types-eq-1 ctx tp1 tp2)))
	(settriplehash ctx tp1 tp2
		       (if z t 'f)
		       *ctx-types-eq-hash*)
	z))))

(defun ctx-types-eq-1 (ctx tp1 tp2)
  (cond ((dpi-p tp1)
	 (if (dpi-p tp2) ; never really gets used
	     (progn
	       (when (> *verbose* 80)
		 (format t "Called ctx-types-eq-1 with Pi's~%~d~%~d~%" tp1 tp2)
		 )
	       (and (ctx-types-eq ctx (dpi-dom tp1) (dpi-dom tp2))
		    (ctx-types-eq (ctx-cons (dpi-dom tp1) ctx) (dpi-cod tp1) (dpi-cod tp2)))
	       )
	   nil))
	((dclass-p tp1)
	 (if (dclass-p tp2) ; never really gets used
	     (progn
	       (when (> *verbose* 80)
		 (format t "Called ctx-types-eq-1 with class's~%~d~%~d~%" tp1 tp2)
		 )
		 (case *checking-style*
		       (A
			(ctx-terms-eq-type ctx (dclass-pred tp1) (dclass-pred tp2) *pred*))
		       (C
			(ctx-terms-eq-type-C ctx (dclass-pred tp1) (dclass-pred tp2) *pred*))
		       (t
			(ctx-terms-eq-stype (typeerase-ctx ctx) (dclass-pred tp1) (dclass-pred tp2) '(ARROW I O)))))
	   nil))
	((pf-p tp1)
	 (if (pf-p tp2)
	     (case *checking-style*
		   (A (ctx-terms-eq-type ctx (pf-prop tp1) (pf-prop tp2) *prop*))
		   (C (ctx-terms-eq-type-C ctx (pf-prop tp1) (pf-prop tp2) *prop*))
		   (D (ctx-normal-eq-in-type-D ctx (pf-prop tp1) (pf-prop tp2) *prop*))
		   (E (ctx-normal-eq-in-type-E ctx (pf-prop tp1) (pf-prop tp2) *prop*))
		   (t (ctx-terms-eq-stype (typeerase-ctx ctx) (pf-prop tp1) (pf-prop tp2) 'O)))
	   nil))
	(t (eq tp1 tp2)))) ; ow, tp1 is obj or prop

(defun ctx-terms-eq-type (ctx trm1 trm2 tp)
  (let ((h (get4hash ctx trm1 trm2 tp *ctx-terms-eq-type-hash*)))
    (if h
	(eq h t)
      (let ((z (ctx-terms-eq-type-1 ctx trm1 trm2 tp)))
	(set4hash ctx trm1 trm2 tp
		  (if z t 'f)
		  *ctx-terms-eq-type-hash*)
	z))))

(defun ctx-terms-eq-type-1 (ctx trm1 trm2 tp)
  (timing-on 'ctx-terms-eq-type-1)
  (prog1
      (if (eq *checking-style* 'D)
	  (ctx-normal-eq-in-type-D ctx trm1 trm2 tp)
	(if (member *checking-style* '(E E2))
	    (ctx-normal-eq-in-type-E ctx trm1 trm2 tp)
	  (if (eq *checking-style* 'F)
	      (ctx-normal-eq-in-type-E (precook-ctx ctx) (precook-term trm1) (precook-term trm2) (precook-type tp))
	    (ctx-terms-eq-type-1 ctx trm1 trm2 tp))))
    (timing-off 'ctx-terms-eq-type-1)))


(defun ctx-terms-eq-type-2 (ctx trm1 trm2 tp)
  (cond ((dpi-p tp)
	 (ctx-terms-eq-type-1
	  (ctx-cons (dpi-dom tp) ctx)
	  (gen-lam-body trm1)
	  (gen-lam-body trm2)
	  (dpi-cod tp)))
	((dclass-p tp) ; only check first pair since second is proof
	 (ctx-terms-eq-type-1 ctx (gen-pair-fst trm1) (gen-pair-fst trm2) (obj)))
	((pf-p tp) t) ; proof irrelevance
	(t
	 (ctx-extract-eq-type ctx trm1 trm2))))
	       
(defun ctx-extract-eq-type (ctx trm1 trm2)
  (let ((h (gettriplehash ctx trm1 trm2 *ctx-extractions-eq-type-hash*)))
    (if h
	h
      (let ((z (ctx-extract-eq-type-1 ctx trm1 trm2))) 
	(settriplehash ctx trm1 trm2
		       z
		       *ctx-extractions-eq-type-hash*)
	z))))

(defun ctx-extract-eq-type-1 (ctx trm1 trm2)
  (timing-on 'ctx-extract-eq-type-1)
  (prog1
      (if (eq *checking-style* 'D)
	  (ctx-extr-eq-in-type-D ctx trm1 trm2)
	(if (member *checking-style* '(E E2))
	    (ctx-extr-eq-in-type-E ctx trm1 trm2)
	  (if (eq *checking-style* 'F)
	      (postcook-type (ctx-extr-eq-in-type-F (precook-ctx ctx) (precook-term trm1) (precook-term trm2)))
	    (ctx-extract-eq-type-1 ctx trm1 trm2))))
    (timing-off 'ctx-extract-eq-type-1)))

(defun ctx-extract-eq-type-2 (ctx trm1 trm2)
  (cond ((app-p trm1)
	 (if (app-p trm2)
	     (let ((ftp (ctx-extract-eq-type ctx (app-func trm1) (app-func trm2))))
	       (if (and ftp (dpi-p ftp))
		   (let ((dom (dpi-dom ftp))
			 (a (app-arg trm1)))
		     (if (and (ctx-terms-eq-type ctx a (app-arg trm2) dom)
			      (or (not *check-simple-type-premisses*) (simply-valid-p (typeerase-ctx ctx) (dbsubst-type-0 (dpi-cod ftp) a))))
			 (normalize-type (dbsubst-type-0 (dpi-cod ftp) a))
		       nil))
		 nil))
	   nil))
	((fst-p trm1)
	 (if (fst-p trm2)
	     (let ((etp (ctx-extract-eq-type ctx (fst-arg trm1) (fst-arg trm2))))
	       (if (and etp (dclass-p etp))
		   (obj)
		 nil))
	   nil))
	((snd-p trm1)
	 (if (snd-p trm2)
	     (let ((etp (ctx-extract-eq-type ctx (snd-arg trm1) (snd-arg trm2))))
	       (if (and etp (dclass-p etp)
			(or (not *check-simple-type-premisses*) (has-simple-type (typeerase-ctx ctx) (app (dclass-pred etp) (fst (snd-arg trm1))) 'O)))
		   (pf (normalize (app (dclass-pred etp) (fst (snd-arg trm1)))))
		 nil))
	   nil))
	((numberp trm1)
	 (if (eql trm1 trm2)
	     (ctx-extract-type-1 ctx trm1)
	   nil))
	((and (symbolp trm1)
	      (eq trm1 trm2))
	 (get trm1 'dbtype))
	(t nil)))

(defun ctx-terms-eq-type-C (ctx trm1 trm2 tp)
  (cond ((dpi-p tp)
	 (ctx-terms-eq-type-C
	  (ctx-cons (dpi-dom tp) ctx)
	  (gen-lam-body trm1)
	  (gen-lam-body trm2)
	  (dpi-cod tp)))
	((dclass-p tp) ; only check first pair since second is proof
	 (ctx-terms-eq-type-C ctx (gen-pair-fst trm1) (gen-pair-fst trm2) (obj)))
	((pf-p tp) t) ; proof irrelevance
	(t
	 (ctx-extract-eq-type-C ctx trm1 trm2))))
	       
(defun ctx-extract-eq-type-C (ctx trm1 trm2)
  (cond ((app-p trm1)
	 (if (app-p trm2)
	     (let ((ftp (ctx-extract-eq-type-C ctx (app-func trm1) (app-func trm2))))
	       (if (and ftp (dpi-p ftp))
		   (let ((dom (dpi-dom ftp))
			 (a (app-arg trm1)))
		     (if (ctx-terms-eq-type-C ctx a (app-arg trm2) dom)
			 (dpi-cod ftp) ; this only needs to have the right type erasure
		       nil))
		 nil))
	   nil))
	((fst-p trm1)
	 (if (fst-p trm2)
	     (let ((etp (ctx-extract-eq-type-C ctx (fst-arg trm1) (fst-arg trm2))))
	       (if (and etp (dclass-p etp))
		   (obj)
		 nil))
	   nil))
	((snd-p trm1)
	 (if (snd-p trm2)
	     (let ((etp (ctx-extract-eq-type-C ctx (snd-arg trm1) (snd-arg trm2))))
	       (if (and etp (dclass-p etp))
		   (pf (app (dclass-pred etp) (fst (snd-arg trm1)))) ; this could really be pf of anything
		 nil))
	   nil))
	((numberp trm1)
	 (if (eql trm1 trm2)
	     (nth trm1 ctx) ; ignore db shifting here since we never look inside pf's and dclass's
	   nil))
	((and (symbolp trm1)
	      (eq trm1 trm2))
	 (get trm1 'dbtype))
	(t nil)))

; simply typed alternative
; note that ctx is a simply typed ctx and stp is a simple type
(defun ctx-terms-eq-stype (ctx trm1 trm2 stp)
  (cond ((and (consp stp) (eq (car stp) 'ARROW))
	 (ctx-terms-eq-stype
	  (ctx-cons (cadr stp) ctx)
	  (gen-lam-body trm1)
	  (gen-lam-body trm2)
	  (caddr stp)))
	((and (consp stp) (eq (car stp) 'TIMES))
	 (ctx-terms-eq-stype ctx (gen-pair-fst trm1) (gen-pair-fst trm2) 'I))
	((eq stp 'R) t) ; proof irrelevance
	(t
	 (ctx-extract-eq-stype ctx trm1 trm2))))
	       
; simply typed alternative
; note that ctx is a simply typed ctx
(defun ctx-extract-eq-stype (ctx trm1 trm2)
  (cond ((app-p trm1)
	 (if (app-p trm2)
	     (let ((ftp (ctx-extract-eq-stype ctx (app-func trm1) (app-func trm2))))
	       (if (and ftp (consp ftp) (eq (car ftp) 'ARROW))
		   (let ((dom (cadr ftp))
			 (a (app-arg trm1)))
		     (if (ctx-terms-eq-stype ctx a (app-arg trm2) dom)
			 (caddr ftp)
		       nil))
		 nil))
	   nil))
	((fst-p trm1)
	 (if (fst-p trm2)
	     (let ((etp (ctx-extract-eq-stype ctx (fst-arg trm1) (fst-arg trm2))))
	       (if (and etp (equal etp '(TIMES I R)))
		   'I
		 nil))
	   nil))
	((snd-p trm1)
	 (if (snd-p trm2)
	     (let ((etp (ctx-extract-eq-stype ctx (fst-arg trm1) (fst-arg trm2))))
	       (if (and etp (equal etp '(TIMES I R)))
		   'R
		 nil))
	   nil))
	((numberp trm1)
	 (if (eql trm1 trm2)
	     (nth trm1 ctx) ; no need to dbshift because it's a simple type
	   nil))
	((and (symbolp trm1)
	      (eq trm1 trm2))
	 (typeerase (get trm1 'dbtype)))
	(t nil)))

(defun ctx-normal-eq-in-type-D (ctx trm1 trm2 tp)
  (cond ((dpi-p tp)
	 (ctx-normal-eq-in-type-D
	  (ctx-cons (dpi-dom tp) ctx)
	  (gen-lam-body trm1)
	  (gen-lam-body trm2)
	  (dpi-cod tp)))
	((dclass-p tp)
	 (let ((phi (dclass-pred tp))
	       (f (gen-pair-fst trm1)))
	   (and
	    (ctx-normal-eq-in-type-D ctx f (gen-pair-fst trm2) (obj))
	    (or (not *check-simple-type-premisses*) (has-simple-type (typeerase-ctx ctx) (app phi f) 'O))
	    (ctx-normal-eq-in-type-D ctx (gen-pair-snd trm1) (gen-pair-snd trm2)
				     (pf (normalize (app phi f)))))))
	((pf-p tp)
	 (if (equal trm1 trm2) ; short cut if already equal (to prevent duplicating computation) -- makes a huge difference on leftInvOfInjProp
	     (let ((tp1 (ctx-extr-eq-in-type-D ctx trm1 trm1)))
	       (if (and tp1 (pf-p tp1))
		   (ctx-normal-eq-in-type-D ctx (pf-prop tp1) (pf-prop tp) (prop))
		 nil))
	   (let ((tp1 (ctx-extr-eq-in-type-D ctx trm1 trm1)))
	     (if (and tp1 (pf-p tp1))
		 (let ((tp2 (ctx-extr-eq-in-type-D ctx trm2 trm2)))
		   (if (and tp2 (pf-p tp2))
		       (and (ctx-normal-eq-in-type-D ctx (pf-prop tp1) (pf-prop tp) (prop))
			    (ctx-normal-eq-in-type-D ctx (pf-prop tp2) (pf-prop tp) (prop)))
		     nil))
	       nil))))
	((or (obj-p tp) (prop-p tp)) ; obj or prop
	 (let ((tp1 (ctx-extr-eq-in-type-D ctx trm1 trm2)))
	   (and tp1 (equal tp1 tp))))
	(t nil))) ; should not happen

(defun ctx-extr-eq-in-type-D (ctx trm1 trm2)
  (cond ((app-p trm1)
	 (if (app-p trm2)
	     (let ((ftp (ctx-extr-eq-in-type-D ctx (app-func trm1) (app-func trm2))))
	       (if (and ftp (dpi-p ftp))
		   (let ((dom (dpi-dom ftp))
			 (a (app-arg trm1)))
		     (if (ctx-normal-eq-in-type-D ctx a (app-arg trm2) dom)
			 (if (or (not *check-simple-type-premisses*)
				 (simply-valid-p (typeerase-ctx ctx)
						 (dbsubst-type-0 (dpi-cod ftp) a)))
			     (normalize-type (dbsubst-type-0 (dpi-cod ftp) a))
			   nil)
		       nil))
		 nil))
	   nil))
	((fst-p trm1)
	 (if (fst-p trm2)
	     (let ((tp (ctx-extr-eq-in-type-D ctx (fst-arg trm1) (fst-arg trm2))))
	       (if (and tp (dclass-p tp))
		   (obj)
		 nil))
	   nil))
	((snd-p trm1)
	 (if (snd-p trm2)
	     (let ((tp (ctx-extr-eq-in-type-D ctx (snd-arg trm1) (snd-arg trm2))))
	       (if (and tp (dclass-p tp))
		   (if (or (not *check-simple-type-premisses*) (has-simple-type (typeerase-ctx ctx) (app (dclass-pred tp) (fst (snd-arg trm1))) 'O))
		       (pf (normalize (app (dclass-pred tp) (fst (snd-arg trm1)))))
		     nil)
		 nil))
	   nil))
	((numberp trm1)
	 (if (equal trm1 trm2)
	     (dbshift-type-n (1+ trm1) (nth trm1 ctx))
	   nil))
	((symbolp trm1)
	 (if (eq trm1 trm2)
	     (get trm1 'dbtype)
	   nil))
	(t nil)))

(defun ctx-normal-eq-in-type-E (ctx trm1 trm2 tp)
  (timing-on 'ctx-normal-eq-in-type-E)
  (prog1
  (cond ((dpi-p tp)
	 (ctx-normal-eq-in-type-E
	  (ctx-cons (dpi-dom tp) ctx)
	  (gen-lam-body trm1)
	  (gen-lam-body trm2)
	  (dpi-cod tp)))
	((dclass-p tp)
	 (if (or (eq *checking-style* 'E) ; always do the split with E,
		 (pair-p trm1) (pair-p trm2)) ; or if at least one term is explicitly a pair
	     (let ((phi (dclass-pred tp))
		   (f (gen-pair-fst trm1)))
	       (and
		(ctx-normal-eq-in-type-E ctx f (gen-pair-fst trm2) (obj))
		(ctx-normal-eq-in-type-E ctx (gen-pair-snd trm1) (gen-pair-snd trm2)
					 (pf (app phi f)))))
	   ; otherwise, both are extractions
	   (let ((tp1 (ctx-extr-eq-in-type-E ctx trm1 trm2)))
	     (and tp1
		  (dclass-p tp1)
		  (ctx-normal-eq-in-type-E ctx (dclass-pred tp1) (dclass-pred tp) *pred*)))))
	((pf-p tp)
	 (if (equal trm1 trm2) ; short cut if already equal (to prevent duplicating computation) -- makes a huge difference on leftInvOfInjProp
	     (let ((tp1 (ctx-extr-eq-in-type-E ctx trm1 trm1)))
	       (if (and tp1 (pf-p tp1))
		   (if (or (not *check-simple-type-premisses*)
			   (and (has-simple-type (typeerase-ctx ctx) (pf-prop tp) 'O)
				(has-simple-type (typeerase-ctx ctx) (pf-prop tp1) 'O)))
		       (ctx-normal-eq-in-type-E ctx (normalize (pf-prop tp1)) (normalize (pf-prop tp)) (prop))
		     nil)
		 nil))
	   (let ((tp1 (ctx-extr-eq-in-type-E ctx trm1 trm1)))
	     (if (and tp1 (pf-p tp1))
		 (let ((tp2 (ctx-extr-eq-in-type-E ctx trm2 trm2)))
		   (if (and tp2 (pf-p tp2))
		       (if (or (not *check-simple-type-premisses*)
			       (and (has-simple-type (typeerase-ctx ctx) (pf-prop tp) 'O)
				    (has-simple-type (typeerase-ctx ctx) (pf-prop tp1) 'O)
				    (has-simple-type (typeerase-ctx ctx) (pf-prop tp2) 'O)
				    ))
			   (let ((ntp (normalize (pf-prop tp))))
			     (let ((res
				    (and (ctx-normal-eq-in-type-E ctx (normalize (pf-prop tp1)) ntp (prop))
					 (ctx-normal-eq-in-type-E ctx (normalize (pf-prop tp2)) ntp (prop)))))
			       (if res
				   (progn
				     (when (> *verbose* 30)
				       (format t "Proof Irrelevance Used~%"))
				     (setq *proof-irrelevance-used* t)
				     res)
				 nil)))
			 nil)
		     nil))
	       nil))))
	((or (obj-p tp) (prop-p tp)) ; obj or prop
	 (let ((tp1 (ctx-extr-eq-in-type-E ctx trm1 trm2)))
	   (and tp1 (equal tp1 tp))))
	(t nil)) ; should not happen
  (timing-off 'ctx-normal-eq-in-type-E)))

(defun ctx-extr-eq-in-type-E (ctx trm1 trm2)
  (timing-on 'ctx-extr-eq-in-type-E)
  (prog1
  (cond ((app-p trm1)
	 (if (app-p trm2)
	     (let ((ftp (ctx-extr-eq-in-type-E ctx (app-func trm1) (app-func trm2))))
	       (if (and ftp (dpi-p ftp))
		   (let ((dom (dpi-dom ftp))
			 (a (app-arg trm1)))
		     (if (ctx-normal-eq-in-type-E ctx a (app-arg trm2) dom)
			 (if (or (not *check-simple-type-premisses*)
				 (simply-valid-p (typeerase-ctx ctx)
						 (dbsubst-type-0 (dpi-cod ftp) a)))
			     (normalize-type (dbsubst-type-0 (dpi-cod ftp) a))
			   nil)
		       nil))
		 nil))
	   nil))
	((fst-p trm1)
	 (if (fst-p trm2)
	     (let ((tp (ctx-extr-eq-in-type-E ctx (fst-arg trm1) (fst-arg trm2))))
	       (if (and tp (dclass-p tp))
		   (obj)
		 nil))
	   nil))
	((snd-p trm1)
	 (if (snd-p trm2)
	     (let ((tp (ctx-extr-eq-in-type-E ctx (snd-arg trm1) (snd-arg trm2))))
	       (if (and tp (dclass-p tp))
		   (if (or (not *check-simple-type-premisses*) (has-simple-type (typeerase-ctx ctx) (app (dclass-pred tp) (fst (snd-arg trm1))) 'O))
		       (pf (normalize (app (dclass-pred tp) (fst (snd-arg trm1)))))
		     nil)
		 nil))
	   nil))
	((numberp trm1)
	 (if (equal trm1 trm2)
	     (dbshift-type-n (1+ trm1) (nth trm1 ctx))
	   nil))
	((symbolp trm1)
	 (if (eq trm1 trm2)
	     (get trm1 'dbtype)
	   nil))
	(t nil))
  (timing-off 'ctx-extr-eq-in-type-E)))

(defun gen-lam-body (trm)
  (if (lam-p trm)
      (lam-body trm)
    (app (dbsubst trm #'1+ 'ID) 0)))

(defun gen-pair-fst (trm)
  (if (pair-p trm)
      (pair-fst trm)
    (fst trm)))

(defun gen-pair-snd (trm)
  (if (pair-p trm)
      (pair-snd trm)
    (snd trm)))

(defun deptype2-p (tp &optional (ctx *emptyctx*))
  (if (dpi-p tp)
      (and (deptype1-p (dpi-dom tp) ctx)
	   (deptype2-p (dpi-cod tp) (ctx-cons (dpi-dom tp) ctx)))
    (ctx-type-valid-p ctx tp)))

(defun deptype1-p (tp &optional (ctx *emptyctx*))
  (if (dpi-p tp)
      (and (deptype0-p (dpi-dom tp) ctx)
	   (deptype1-p (dpi-cod tp) (ctx-cons (dpi-dom tp) ctx)))
    (ctx-type-valid-p ctx tp)))

(defun deptype0-p (tp &optional (ctx *emptyctx*))
  (if (dpi-p tp)
      nil
    (ctx-type-valid-p ctx tp)))

(defun normal-term-p (trm &optional checked)
  (if (member trm checked)
      checked
    (if (or (beta-redex-p trm)
	    (eta-redex-p trm)
	    (fst-redex-p trm)
	    (snd-redex-p trm)
	    (pair-redex-p trm))
	nil
      (cond ((app-p trm)
	     (let* ((f (app-func trm))
		    (a (app-arg trm))
		    (z (normal-term-p f checked)))
	       (if z
		   (let ((y (normal-term-p a z)))
		     (if y
			 (cons trm y)
		       nil))
		 nil)))
	    ((pair-p trm)
	     (let* ((a (pair-fst trm))
		    (b (pair-snd trm))
		    (z (normal-term-p a checked)))
	       (if z
		   (let ((y (normal-term-p b z)))
		     (if y
			 (cons trm y)
		       nil))
		 nil)))
	    ((lam-p trm)
	     (let ((z (normal-term-p (lam-body trm))))
	       (if z
		   (cons trm z)
		 nil)))
	    ((fst-p trm)
	     (let ((z (normal-term-p (fst-arg trm))))
	       (if z
		   (cons trm z)
		 nil)))
	    ((snd-p trm)
	     (let ((z (normal-term-p (snd-arg trm))))
	       (if z
		   (cons trm z)
		 nil)))
	    (t (list trm))))))

(defun normal-type-p (tp)
  (cond ((dpi-p tp)
	 (and (normal-type-p (dpi-dom tp)) (normal-type-p (dpi-cod tp))))
	((dclass-p tp)
	 (normal-term-p (dclass-pred tp)))
	((pf-p tp)
	 (normal-term-p (pf-prop tp)))
	(t t)))

(defun beta-normal-term-p (trm &optional checked)
  (if (member trm checked)
      checked
    (if (or (beta-redex-p trm)
	    (fst-redex-p trm)
	    (snd-redex-p trm))
	nil
      (cond ((app-p trm)
	     (let* ((f (app-func trm))
		    (a (app-arg trm))
		    (z (beta-normal-term-p f checked)))
	       (if z
		   (let ((y (beta-normal-term-p a z)))
		     (if y
			 (cons trm y)
		       nil))
		 nil)))
	    ((pair-p trm)
	     (let* ((a (pair-fst trm))
		    (b (pair-snd trm))
		    (z (beta-normal-term-p a checked)))
	       (if z
		   (let ((y (beta-normal-term-p b z)))
		     (if y
			 (cons trm y)
		       nil))
		 nil)))
	    ((lam-p trm)
	     (let ((z (beta-normal-term-p (lam-body trm))))
	       (if z
		   (cons trm z)
		 nil)))
	    ((fst-p trm)
	     (let ((z (beta-normal-term-p (fst-arg trm))))
	       (if z
		   (cons trm z)
		 nil)))
	    ((snd-p trm)
	     (let ((z (beta-normal-term-p (snd-arg trm))))
	       (if z
		   (cons trm z)
		 nil)))
	    (t (list trm))))))

(defun beta-normal-type-p (tp)
  (cond ((dpi-p tp)
	 (and (beta-normal-type-p (dpi-dom tp)) (beta-normal-type-p (dpi-cod tp))))
	((dclass-p tp)
	 (beta-normal-term-p (dclass-pred tp)))
	((pf-p tp)
	 (beta-normal-term-p (pf-prop tp)))
	(t t)))

(defun beta-redex-p (trm)
  (and (app-p trm) (lam-p (app-func trm))))

(defun eta-redex-p (trm)
  (and (lam-p trm) (app-p (lam-body trm)) (eql (app-arg (lam-body trm)) 0)
       (not (nintrm-p 0 (app-func (lam-body trm))))))

(defun fst-redex-p (trm)
  (and (fst-p trm) (pair-p (fst-arg trm))))

(defun snd-redex-p (trm)
  (and (snd-p trm) (pair-p (snd-arg trm))))

(defun pair-redex-p (trm)
  (and (pair-p trm) (fst-p (pair-fst trm)) (snd-p (pair-snd trm))
       (heq (fst-arg (pair-fst trm)) (snd-arg (pair-snd trm)))))

(defun classify-type (tp)
  (if (dpi-p tp)
      (classify-type (dpi-cod tp))
    (cond ((dclass-p tp) 'TFUNC)
	  ((obj-p tp) 'FUNC)
	  ((prop-p tp) 'RELN)
	  ((pf-p tp) 'RULE))))

; get named bvars
(defun dtype-free-bvars (tp &optional (h (make-hash-table :test #'eq)))
  (cond ((dpi-p tp)
	 (append (dtype-free-bvars (dpi-dom tp) h) (dtype-free-bvars (dpi-cod tp) h)))
	((dclass-p tp)
	 (free-bvars (dclass-pred tp) h))
	((pf-p tp)
	 (free-bvars (pf-prop tp) h))
	(t nil)))

(defun free-bvars (trm &optional (h (make-hash-table :test #'eq)))
  (let ((a (getsinglehash trm h)))
    (if a
	(if (eq a 'none)
	    nil
	  a)
      (let ((bl (free-bvars-1 trm h)))
	(setsinglehash trm h (or bl 'none))
	bl))))

(defun free-bvars-1 (trm &optional (h (make-hash-table :test #'eq)))
  (cond ((app-p trm)
	 (union (free-bvars (app-func trm) h)
		(free-bvars (app-arg trm) h)))
	((pair-p trm)
	 (union (free-bvars (pair-fst trm) h)
		(free-bvars (pair-snd trm) h)))
	((lam-p trm)
	 (free-bvars (lam-body trm) h))
	((fst-p trm)
	 (free-bvars (fst-arg trm) h))
	((snd-p trm)
	 (free-bvars (snd-arg trm) h))
	((numberp trm) nil)
	((get trm 'bvar) (list trm))
	(t nil)))

(defun dtype-free-evars (tp &optional (h (make-hash-table :test #'eq)))
  (cond ((dpi-p tp)
	 (append (dtype-free-evars (dpi-dom tp) h) (dtype-free-evars (dpi-cod tp) h)))
	((dclass-p tp)
	 (free-evars (dclass-pred tp) h))
	((pf-p tp)
	 (free-evars (pf-prop tp) h))
	(t nil)))

(defun free-evars (trm &optional (h (make-hash-table :test #'eq)))
  (let ((a (getsinglehash trm h)))
    (if a
	(if (eq a 'none)
	    nil
	  a)
      (let ((bl (free-evars-1 trm h)))
	(setsinglehash trm h (or bl 'none))
	bl))))

(defun free-evars-1 (trm &optional (h (make-hash-table :test #'eq)))
  (cond ((app-p trm)
	 (union (free-evars (app-func trm) h)
		(free-evars (app-arg trm) h)))
	((pair-p trm)
	 (union (free-evars (pair-fst trm) h)
		(free-evars (pair-snd trm) h)))
	((lam-p trm)
	 (free-evars (lam-body trm) h))
	((fst-p trm)
	 (free-evars (fst-arg trm) h))
	((snd-p trm)
	 (free-evars (snd-arg trm) h))
	((numberp trm) nil)
	((get trm 'evar) (list trm))
	(t nil)))

(defun dtype-free-claims (tp &optional (h (make-hash-table :test #'eq)))
  (cond ((dpi-p tp)
	 (append (dtype-free-claims (dpi-dom tp) h) (dtype-free-claims (dpi-cod tp) h)))
	((dclass-p tp)
	 (free-claims (dclass-pred tp) h))
	((pf-p tp)
	 (free-claims (pf-prop tp) h))
	(t nil)))

(defun free-claims (trm &optional (h (make-hash-table :test #'eq)))
  (let ((a (getsinglehash trm h)))
    (if a
	(if (eq a 'none)
	    nil
	  a)
      (let ((bl (free-claims-1 trm h)))
	(setsinglehash trm h (or bl 'none))
	bl))))

(defun free-claims-1 (trm &optional (h (make-hash-table :test #'eq)))
  (cond ((app-p trm)
	 (union (free-claims (app-func trm) h)
		(free-claims (app-arg trm) h)))
	((pair-p trm)
	 (union (free-claims (pair-fst trm) h)
		(free-claims (pair-snd trm) h)))
	((lam-p trm)
	 (free-claims (lam-body trm) h))
	((fst-p trm)
	 (free-claims (fst-arg trm) h))
	((snd-p trm)
	 (free-claims (snd-arg trm) h))
	((numberp trm) nil)
	((get trm 'claim) (list trm))
	(t nil)))

(defun dtype-sig-elts (tp &optional (h (make-hash-table :test #'eq)))
  (cond ((dpi-p tp)
	 (append (dtype-sig-elts (dpi-dom tp) h) (dtype-sig-elts (dpi-cod tp) h)))
	((dclass-p tp)
	 (sig-elts (dclass-pred tp) h))
	((pf-p tp)
	 (sig-elts (pf-prop tp) h))
	(t nil)))

(defun sig-elts (trm &optional (h (make-hash-table :test #'eq)))
  (let ((a (getsinglehash trm h)))
    (if a
	(if (eq a 'none)
	    nil
	  a)
      (let ((bl (sig-elts-1 trm h)))
	(setsinglehash trm h (or bl 'none))
	bl))))

(defun sig-elts-1 (trm &optional (h (make-hash-table :test #'eq)))
  (cond ((app-p trm)
	 (union (sig-elts (app-func trm) h)
		(sig-elts (app-arg trm) h)))
	((pair-p trm)
	 (union (sig-elts (pair-fst trm) h)
		(sig-elts (pair-snd trm) h)))
	((lam-p trm)
	 (sig-elts (lam-body trm) h))
	((fst-p trm)
	 (sig-elts (fst-arg trm) h))
	((snd-p trm)
	 (sig-elts (snd-arg trm) h))
	((numberp trm) nil)
	((symbolp trm)
	 (when (or (constname-p trm) (abbrevname-p trm) (claimname-p trm))
	   (list trm)))
	(t nil)))

(defun dtype-sig-elts-rec (tp &optional done)
  (let ((new (dtype-sig-elts tp)))
    (dolist (n new)
      (unless (member n done)
	(push n done)
	(let ((new2 (dtype-sig-elts-rec (get n 'dbtype) done)))
	  (setq done (union new2 done)))
	(when (abbrevname-p n)
	  (let ((new2 (sig-elts-rec (get n 'defn) done)))
	    (setq done (union new2 done))))))
    done))
    
(defun sig-elts-rec (trm &optional done)
  (let ((new (sig-elts trm)))
    (dolist (n new)
      (unless (member n done)
	(push n done)
	(let ((new2 (dtype-sig-elts-rec (get n 'dbtype) done)))
	  (setq done (union new2 done)))
	(when (abbrevname-p n)
	  (let ((new2 (sig-elts-rec (get n 'defn) done)))
	    (setq done (union new2 done))))))
    done))

(defun pair-prop (classtp obj)
  (normalize (app (dclass-pred classtp) obj)))

(defun dtype-returns-dclass-p (dtp)
  (loop while (dpi-p dtp) do
	(setq dtp (dpi-cod dtp)))
  (dclass-p dtp))

(defun dtype-returns-pf-p (dtp)
  (loop while (dpi-p dtp) do
	(setq dtp (dpi-cod dtp)))
  (pf-p dtp))

(defun dtype-returns-obj-p (dtp)
  (loop while (dpi-p dtp) do
	(setq dtp (dpi-cod dtp)))
  (obj-p dtp))

(defun dtype-returns-prop-p (dtp)
  (loop while (dpi-p dtp) do
	(setq dtp (dpi-cod dtp)))
  (prop-p dtp))

(defun term-head (trm)
  (cond ((lam-p trm) (term-head (lam-body trm)))
	((app-p trm) (term-head (app-func trm)))
	((pair-p trm) (term-head (pair-fst trm))) ; obj head, not pf head
	((fst-p trm) (term-head (fst-arg trm)))
	((snd-p trm) (term-head (snd-arg trm)))
	(t trm)))

(defun term-arg1 (trm)
  (cond ((lam-p trm) (term-arg1 (lam-body trm)))
	((app-p trm)
	 (if (or (numberp (app-func trm)) (symbolp (app-func trm)))
	     (app-arg trm)
	   (term-arg1 (app-func trm))))
	((pair-p trm) (term-arg1 (pair-fst trm)))
	((fst-p trm) (term-arg1 (fst-arg trm)))
	((snd-p trm) (term-arg1 (snd-arg trm)))
	(t nil)))

(defun term-app-head (trm)
  (loop while (app-p trm) do
	(setq trm (app-func trm)))
  trm)

(defun lam-app-head (trm)
  (loop while (or (app-p trm) (lam-p trm)) do
	(if (app-p trm)
	    (setq trm (app-func trm))
	  (setq trm (lam-body trm))))
  trm)

(defun term-extr-head (trm)
  (if (fst-p trm)
      (setq trm (fst-arg trm))
    (when (snd-p trm)
      (setq trm (snd-arg trm))))
  (loop while (app-p trm) do
	(setq trm (app-func trm)))
  trm)

(defun term-extr-args (trm)
  (if (fst-p trm)
      (setq trm (fst-arg trm))
    (when (snd-p trm)
      (setq trm (snd-arg trm))))
  (let ((args nil))
    (loop while (app-p trm) do
	  (push (app-arg trm) args)
	  (setq trm (app-func trm)))
    args))

(defun rigid-p (h)
  (or (numberp h)
      (and (symbolp h) (not (get h 'evar)))))

; substitute for evars...
(defun subst-type-1 (x a tp)
  (simul-subst-type (acons x a nil) tp))

(defun subst-1 (x a trm)
  (simul-subst (acons x a nil) trm))

(defun simul-subst-type (theta tp)
  (cond ((dpi-p tp) (dpi (simul-subst-type theta (dpi-dom tp))
			 (simul-subst-type theta (dpi-cod tp))))
	((dclass-p tp) (dclass (simul-subst theta (dclass-pred tp))))
	((pf-p tp) (pf (simul-subst theta (pf-prop tp))))
	(t tp)))

(defun simul-subst (theta trm)
  (cond ((lam-p trm) (lam (simul-subst theta (lam-body trm))))
	((app-p trm) (app (simul-subst theta (app-func trm))
			  (simul-subst theta (app-arg trm))))
	((pair-p trm) (pair (simul-subst theta (pair-fst trm))
			    (simul-subst theta (pair-snd trm))))
	((fst-p trm) (fst (simul-subst theta (fst-arg trm))))
	((snd-p trm) (snd (simul-subst theta (snd-arg trm))))
	((numberp trm) trm)
	(t
	 (let ((z (assoc trm theta)))
	   (if z
	       (cdr z)
	     trm)))))

; this one normalizes
(defun subst-ctx-1 (x a ctx)
  (simul-subst-ctx (acons x a nil) ctx))

(defun simul-subst-ctx (theta ctx)
  (if (eq ctx *emptyctx*)
      *emptyctx*
    (ctx-cons (normalize-type (simul-subst-type theta (car ctx)))
	      (simul-subst-ctx theta (cdr ctx)))))

; assumes theta is a renaming, so no need to normalize
(defun rename-ctx (theta ctx)
  (if (eq ctx *emptyctx*)
      *emptyctx*
    (ctx-cons (simul-subst-type theta (car ctx))
	      (rename-ctx theta (cdr ctx)))))

(defun termsize (trm)
  (cond ((lam-p trm) (1+ (termsize (lam-body trm))))
	((fst-p trm) (1+ (termsize (fst-arg trm))))
	((snd-p trm) (1+ (termsize (snd-arg trm))))
	((app-p trm) (+ (termsize (app-func trm)) (termsize (app-arg trm)) 1))
	((pair-p trm) (+ (termsize (pair-fst trm)) (termsize (pair-snd trm)) 1))
	(t 1)))

(defun typesize (tp)
  (cond ((dpi-p tp) (+ (typesize (dpi-dom tp)) (typesize (dpi-cod tp)) 1))
	((dclass-p tp) (+ (termsize (dclass-pred tp)) 1))
	((pf-p tp) (+ (termsize (pf-prop tp)) 1))
	(t 1)))

(defun dpi-ctx (ctx tp)
  (if ctx
      (dpi-ctx (cdr ctx) (dpi (car ctx) tp))
    tp))

(defun lam-ctx (ctx trm)
  (dotimes (i (length ctx) trm)
    (setq trm (lam trm))))

(defun app-n-1-to-0 (n trm)
  (let ((i n))
    (dotimes (j n)
      (setq trm (app trm (decf i))))
    trm))

; type erasure and simple type checking - February 26, 2006
(defun typeerase (A)
  (cond ((pf-p A) 'R)
	((obj-p A) 'I)
	((prop-p A) 'O)
	((dclass-p A) '(TIMES I R))
	((dpi-p A) (list 'ARROW (typeerase (dpi-dom A)) (typeerase (dpi-cod A))))
	(t (fail "no type erasure of " A))))

(defun typeerase-ctx (gamma)
  (if gamma
      (cons (typeerase (car gamma)) (typeerase-ctx (cdr gamma)))
    nil))

(defun genstvar ()
  (let ((tvar (gensym)))
    (setf (get tvar 'stvar) t)
    (setf (get tvar 'stval) nil)  
    tvar))

(defun stvar-p (x)
  (and (symbolp x) (get x 'stvar)))

(defun has-simple-type (delta M stp)
  (loop while (and (symbolp stp) (get stp 'stvar) (get stp 'stval)) do
	(setq stp (get stp 'stval)))
  (cond ((app-p M)
	 (let ((tvar (genstvar)))
	   (let ((ftp (has-simple-type delta (app-func M) (list 'ARROW tvar stp))))
	     (if (and ftp (has-simple-type delta (app-arg M) tvar))
		 stp
	       nil))))
	((lam-p M)
	 (when (and (symbolp stp) (get stp 'stvar))
	   (let ((a (genstvar))
		 (b (genstvar)))
	     (setf (get stp 'stval) (list 'ARROW a b))
	     (setq stp (list 'ARROW a b))))
	 (if (and (consp stp) (eq (car stp) 'ARROW)
		  (has-simple-type (cons (cadr stp) delta) (lam-body M) (caddr stp)))
	     stp
	   nil))
	((pair-p M)
	 (if (and (stunify stp '(TIMES I R))
		  (has-simple-type delta (pair-fst M) 'I)
		  (has-simple-type delta (pair-snd M) 'R))
	     '(TIMES I R)
	   nil))
	((fst-p M)
	 (if (and (stunify stp 'I)
		  (has-simple-type delta (fst-arg M) '(TIMES I R)))
	     'I
	   nil))
	((snd-p M)
	 (if (and (stunify stp 'R)
		  (has-simple-type delta (snd-arg M) '(TIMES I R)))
	     'R
	   nil))
	((numberp M)
	 (let ((a (nth M delta)))
	   (if a
	       (if (stunify a stp)
		   stp
		 nil)
	     nil)))
	((and (symbolp M) (get M 'dbtype))
	 (typeerase (get M 'dbtype)))
	(t nil)))

(defun stunify (a b)
  (if (equal a b)
      a
    (if (stvar-p a)
	(if (get a 'stval)
	    (stunify (get a 'stval) b)
	  (if (st-occ-check-p a b)
	      nil
	    (progn
	      (setf (get a 'stval) b)
	      b)))
      (if (stvar-p b)
	  (stunify b a)
	(if (and (consp a) (consp b) (equal (car a) (car b)))
	    (let ((a1 (stunify (cadr a) (cadr b))))
	      (if a1
		  (let ((a2 (stunify (caddr a) (caddr b))))
		    (if a2
			(list (car a) a1 a2)
		      nil))
		nil))
	  nil)))))

(defun st-occ-check-p (a b)
  (if (equal a b)
      t
    (if (consp b)
	(or (st-occ-check-p a (cadr b))
	    (st-occ-check-p a (caddr b)))
      nil)))

(defun simply-valid-p (delta A)
  (cond ((pf-p A) (has-simple-type delta (pf-prop A) 'O))
	((obj-p A) t)
	((prop-p A) t)
	((dclass-p A) (has-simple-type delta (pf-prop A) '(ARROW I O)))
	((dpi-p A)
	 (and (simply-valid-p delta (dpi-dom A))
	      (simply-valid-p (cons (typeerase (dpi-dom A)) delta) (dpi-cod A))))
	(t nil)))

; timing
;(defun timing-on (a)
;  (let ((z (assoc a *timing-stack*)))
;    (unless z
;      (push (cons a (get-internal-run-time)) *timing-stack*))))
;
;(defun timing-off (a)
;  (let ((b (get-internal-run-time)))
;    (setq *timing-stack* (timing-off-2 *timing-stack* a b))))
;
;(defun timing-off-2 (s a b)
;  (if s
;      (if (eq (caar s) a)
;	  (let ((z (assoc (caar s) *timing*)))
;	    (if z
;		(rplacd z
;			(+ (cdr z) (- b (cdar s))))
;	      (push (cons (caar s) (- b (cdar s))) *timing*))
;	    (mapcar #'(lambda (x)
;			(cons (car x) (+ (cdr x) (- b (cdar s)))))
;		    (cdr s)))
;	(let ((z (assoc (caar s) *timing*)))
;	  (if z
;	      (rplacd z
;		      (+ (cdr z) (- b (cdar s))))
;	    (push (cons (caar s) (- b (cdar s))) *timing*))
;	  (timing-off-2 (cdr s) a b)))
;    nil))

(defun timing-on (a)
  nil)

(defun timing-off (a)
  nil)

(defun proof-irrelevance-used-tp-p (ctx tp)
  (setq *proof-irrelevance-used* nil)
  (ctx-type-valid-p ctx tp)
  *proof-irrelevance-used*)

(defun proof-irrelevance-used-trm-p (ctx trm tp)
  (setq *proof-irrelevance-used* nil)
  (ctx-term-type-p ctx trm tp)
  *proof-irrelevance-used*)
