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
; January 2006
(defun extend-ctx (ctx m a)
  (extend-ectx ctx ctx 'ID m a))

(defun extend-ectx (ctx ectx theta m a)
  (values
   (ctx-cons a ectx)
   (cons (normalize (term-to-original-ctx theta m)) (cons #'identity theta))))

(defun term-to-original-ctx (theta m)
  (dbsubst m #'identity theta))

(defun type-to-original-ctx (theta a)
  (dbsubst-type a #'identity theta))

; A is a type in the extended ctx ectx
(defun ectx-cons (A ctx ectx theta)
  (values (ctx-cons (normalize-type (type-to-original-ctx theta A)) ctx)
	  (ctx-cons A ectx)
	  (cons 0 (cons #'1+ theta))))

; this is a more 'internalized' way of extending ctx's,
; without carrying more info around.  probably better.
; ctx is old ctx [length n]
; h is something (probably evar) of type Pi ctx Pi New tp+
; trm is a term of type New in ctx
; returns (lam^n (h n-1 ... 0 trm)) : Pi ctx tp
(defun term-for-extending-ctx (ctx h trm)
  (let* ((ret h)
	 (n (length ctx))
	 (i n))
    (dotimes (j n)
      (setq ret (app ret (decf i))))
    (setq ret (app ret trm))
    (dotimes (j n)
      (setq ret (lam ret)))
    ret))

  
