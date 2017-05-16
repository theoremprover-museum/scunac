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
; December 6 2005

; Outputs a signature in a format readable by lisp

(defun output-sig (names &optional (str t))
  (dolist (z names)
    (unless (get z 'auto-gen)
      (output-sig-1 z str))))

(defun output-sig-1 (z &optional (str t))
  (cond ((get z 'abbrev)
	 (format str "~d~%" (output-abbrev z (get z 'dbtype) (get z 'defn))))
	((get z 'const)
	 (format str "~d~%" (output-const z (get z 'dbtype))))
	((get z 'claim)
	 (format str "~d~%" (output-claim z (get z 'dbtype))))
	(t (format str "% Skipping ~d~%" z))))

(defun output-const (name dtype)
  (format nil "(newconst '~S ~d '~S)~%" name
	  (output-type-string dtype)
	  (get name 'const-authors)
	  ))

(defun output-claim (name dtype &optional argvars)
  (format nil "(newclaim '~S ~d '~S)~%" name
	  (output-type-string dtype)
	  (get name 'claim-authors)))

(defun output-abbrev (name dtype defn &optional argvars)
  (format nil "(newabbrev '~S ~d ~d '~S '~S)~%" name
	  (output-type-string dtype)
	  (output-term-string defn)
	  (get name 'abbrev-type-authors)
	  (get name 'abbrev-defn-authors)
	  ))

(defun output-type-string (dtype)
  (case (deptype-case dtype)
	(DPI
	 (format nil "(dpi ~d ~d)"
		 (output-type-string (dpi-dom dtype))
		 (output-type-string (dpi-cod dtype))))
	(OBJ "(obj)")
	(PROP "(prop)")
	(PF (format nil "(pf ~d)"
		    (output-term-string (pf-prop dtype))))
	(DCLASS 
	 (format nil "(dclass ~d)" (output-term-string (dclass-pred dtype))))
	(t (format nil "; error"))))

(defun output-term-string (term)
  (case (term-case term)
	(APP (format nil "(app ~d ~d)"
		     (output-term-string (app-func term))
		     (output-term-string (app-arg term))))
	(LAM (format nil "(lam ~d)"
		     (output-term-string (lam-body term))))
	(FST (format nil "(fst ~d)" (output-term-string (fst-arg term))))
	(SND (format nil "(snd ~d)" (output-term-string (snd-arg term))))
	(PAIR (format nil "(pair ~d ~d)"
		      (output-term-string (pair-fst term))
		      (output-term-string (pair-snd term))))
	(t (format nil "'~S" term))))


