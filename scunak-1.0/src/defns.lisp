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

(defun delta-head-reduce (trm)
  (cond ((app-p trm)
	 (normalize (app (delta-head-reduce (app-func trm))
			 (app-arg trm))))
	((lam-p trm)
	 (normalize (lam (delta-head-reduce (lam-body trm)))))
	((pair-p trm)
	 (normalize (pair (delta-head-reduce (pair-fst trm)) ; reduce the first one, not the second
			  (pair-snd trm))))
	((fst-p trm)
	 (normalize (fst (delta-head-reduce (fst-arg trm)))))
	((snd-p trm)
	 (normalize (snd (delta-head-reduce (snd-arg trm)))))
	((numberp trm) trm)
	((get trm 'abbrev) (get trm 'defn)) ; assume normal
	(t trm)))

; assumes trm2 is normal
(defun head-unfolds-to (trm1 trm2 tp)
  (ctx-terms-eq-type *emptyctx* (delta-head-reduce trm1) trm2 tp))

(defun delta-autogen-head-reduce (trm)
  (cond ((app-p trm)
	 (normalize (app (delta-autogen-head-reduce (app-func trm))
			 (app-arg trm))))
	((lam-p trm)
	 (normalize (lam (delta-autogen-head-reduce (lam-body trm)))))
	((pair-p trm)
	 (normalize (pair (delta-autogen-head-reduce (pair-fst trm)) ; reduce the first one, not the second
			  (pair-snd trm))))
	((fst-p trm)
	 (normalize (fst (delta-autogen-head-reduce (fst-arg trm)))))
	((snd-p trm)
	 (normalize (snd (delta-autogen-head-reduce (snd-arg trm)))))
	((numberp trm) trm)
	((get trm 'auto-gen)
	 (or (get trm 'defn)
	     (get trm 'auto-defn)))
	(t trm)))

;(defun delta-reduce-first (trm)
;  (normalize (delta-reduce-first-1 trm)))
;
;(defun delta-reduce-first-1 (trm)
;  (cond ((app-p trm)
;	 (let ((trm1 (delta-reduce-first-1 (app-func trm))))
;	   (if (heq trm1 (app-func trm))
;	       (app trm1
;		    (delta-reduce-first-1 (app-arg trm)))
;	     (app trm1 (app-arg trm)))))
;	((lam-p trm)
;	 (lam (delta-reduce-first-1 (lam-body trm)))))
;	((pair-p trm)
;	 (pair trm1
;	       (delta-reduce-first-1 (pair-snd trm))))
;	((fst-p trm)
;	 (normalize (fst (delta-reduce-first (fst-arg trm)))))
;	((snd-p trm)
;	 (normalize (snd (delta-reduce-first (snd-arg trm)))))
;	((numberp trm) trm)
;	((get trm 'abbrev)
;	 (get trm 'defn)) ; assume normal
;	(t trm)))

(defun delta-reduce-abbrevs (ctx trm tp abbrevs)
  (catch 'delta-fail
    (normalize 
     (delta-reduce-abbrevs-norm ctx trm tp abbrevs))))

(defun delta-reduce-abbrevs-norm (ctx trm tp abbrevs)
  (cond ((dpi-p tp)
	 (lam
	  (delta-reduce-abbrevs-norm (ctx-cons (dpi-dom tp) ctx)
				     (gen-lam-body trm)
				     (dpi-cod tp)
				     abbrevs)))
	((dclass-p tp)
	 (let* ((a (delta-reduce-abbrevs-norm ctx (gen-pair-fst trm) (obj) abbrevs))
		(phi (dclass-pred tp))
		(oldprop (normalize (app phi (gen-pair-fst trm))))
		(newprop (normalize (app phi a))))
	   (if (heq oldprop newprop)
	       (pair a (gen-pair-snd trm))
	     (let ((z (congruence-make-equation-pf ctx oldprop newprop (prop))))
	       (if z
		   (pair a (app-n '|equivEimp1| (list oldprop newprop z (gen-pair-snd trm))))
		 (throw 'delta-fail nil))))))
	((member (term-extr-head trm) abbrevs)
	 (delta-reduce-abbrevs-extr-h ctx trm abbrevs))
	(t
	 (delta-reduce-abbrevs-extr ctx trm abbrevs))))

(defun delta-reduce-abbrevs-extr (ctx trm abbrevs)
  (cond ((app-p trm)
	 (let ((f (delta-reduce-abbrevs-extr ctx (app-func trm) abbrevs)))
	   (let ((ftp (ctx-extract-type ctx (app-func trm))))
	     (if (dpi-p ftp)
		 (app f
		      (delta-reduce-abbrevs-norm ctx (app-arg trm) (dpi-dom ftp) abbrevs))
	       (throw 'delta-fail nil)))))
	((fst-p trm)
	 (fst (delta-reduce-abbrevs-extr ctx (fst-arg trm) abbrevs)))
	((snd-p trm) trm) ; no point in delta expanding in a proof term
	(t trm)))

(defun delta-reduce-abbrevs-extr-h (ctx trm abbrevs)
  (cond ((app-p trm)
	 (let ((f (delta-reduce-abbrevs-extr-h ctx (app-func trm) abbrevs)))
	   (app f (app-arg trm))))
	((fst-p trm)
	 (fst (delta-reduce-abbrevs-extr-h ctx (fst-arg trm) abbrevs)))
	((snd-p trm) trm) ; no point in delta expanding in a proof term
	((numberp trm) trm)
	((and (get trm 'abbrev) (member trm abbrevs))
	 (get trm 'defn))
	(t trm)))


