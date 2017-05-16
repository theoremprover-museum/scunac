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
; June 2006
; If you are making Scunak using Allegro or clisp, then 
; edit the parameters below, start lisp, and load this file.
; This should create image files in *dxldir* and executable scripts in *execdir*.
; You may need to edit the executable scripts.

#+:allegro
(load "src/loadc")
#+:clisp
(load "src/loadcl")
#-(or :allegro :clisp)
(load "src/load")

; parameters
(setq *dxldir* "~/scunak/")
(setq *execdir* "~/bin/")
(setq *datadir* "~/scunak/data/")

; saving image
(save-scunak-image)

; creating an executable script
#+:allegro
(unless (probe-file (format nil "~dscunak-acl" *execdir*))
  (let ((f (open (format nil "~dscunak-acl" *execdir*) :direction :output :if-does-not-exist :create)))
    (format f "#! /bin/tcsh~2%")
    (format f "setenv LD_ASSUME_KERNEL 2.4.0~2%")
    (format f "~d -I ~dscunak-allegro.dxl -- -d ~d $*~%"
	    (car (sys:command-line-arguments)) ; Allegro Lisp executable
	    *dxldir*
	    *datadir*)
    (close f)
    (excl:run-shell-command (format nil "chmod a+x ~dscunak-acl" *execdir*))
    ))
#+:clisp
(unless (probe-file (format nil "~dscunak-clisp" *execdir*))
  (let ((f (open (format nil "~dscunak-clisp" *execdir*) :direction :output :if-does-not-exist :create)))
    (format f "clisp -M ~dscunak-clisp.mem -- -d ~d $*~%"
	    *dxldir*
	    *datadir*)
    (close f)
    (ext:run-shell-command (format nil "chmod a+x ~dscunak-clisp" *execdir*))
    ))
(exit)
