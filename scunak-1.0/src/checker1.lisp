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

; January 2006
; Chad E Brown

(defun checker1-initfn ()
  (let ((prefilenames (command-line-arg-several "-p"))
	(filenames (command-line-arg-several "-f"))
	(outfilename (command-line-arg "-o"))
	(lispfilename (command-line-arg "-lo"))
	(color (command-line-switch "-C"))
	(verb (command-line-switch "-v"))
	(verb2 (command-line-switch "-V"))
	(time 0))
    (when verb
      (setq *verbose* 20))
    (when verb2
      (setq *verbose* 99))
    (unless color
      (setq *style* 'ascii))
    (setq *allow-constants* nil)
    (scunak-header "Welcome to the Scunak Set Theory Checker.")
    (dolist (prefilename prefilenames)
      (unless (probe-file prefilename)
	(setq prefilename (format nil "~d.lisp" prefilename))
	(unless (probe-file prefilename)
	  (fail (format nil "No file named ~d." prefilename))))
      (load prefilename))
    (if filenames
	(dolist (filename filenames)
	  (unless (probe-file filename)
	    (fail (format nil "No file named ~d." filename))))
      (fail "A file to be checked must be given."))
    (setq time (get-universal-time))
    (let ((saved *global-sigma*))
      (dolist (filename filenames)
	(readinput1 filename))
      (setq *pre-input1-global-sigma* saved))
    (setq time (- (get-universal-time) time))
    (format t "~d successfully checked!~%~d seconds~%" filenames time)
    (setq *style* 'ascii)
    (when outfilename
      (format t "Writing new version to ~d.~%" outfilename)
      (let ((str (open outfilename :direction :output :if-exists :supersede :if-does-not-exist :create)))
	(output1-sig (input1-sigma) str)
	(close str)))
    (when lispfilename
      (format t "Writing lisp version to ~d.~%" lispfilename)
      (let ((str (open lispfilename :direction :output :if-exists :supersede :if-does-not-exist :create)))
	(output-sig (input1-sigma) str)
	(close str)))))

(defun checker0-initfn ()
  (let ((prefilenames (command-line-arg-several "-p"))
	(filenames (command-line-arg-several "-f"))
	(outfilename (command-line-arg "-o"))
	(lispfilename (command-line-arg "-lo"))
	(color (command-line-switch "-C"))
	(verb (command-line-switch "-v"))
	(verb2 (command-line-switch "-V"))
	(time 0))
    (when verb
      (setq *verbose* 20))
    (when verb2
      (setq *verbose* 99))
    (unless color
      (setq *style* 'ascii))
    (scunak-header "Welcome to the Scunak Basic Type Checker.")
    (dolist (prefilename prefilenames)
      (unless (probe-file prefilename)
	(setq prefilename (format nil "~d.lisp" prefilename))
	(unless (probe-file prefilename)
	  (fail (format nil "No file named ~d." prefilename))))
      (load prefilename))
    (if filenames
	(dolist (filename filenames)
	  (unless (probe-file filename)
	    (fail (format nil "No file named ~d." filename))))
      (fail "A file to be checked must be given."))
    (setq time (get-universal-time))
    (let ((saved *global-sigma*))
      (dolist (filename filenames)
	(load filename))
      (setq *pre-input1-global-sigma* saved)
      )
    (setq time (- (get-universal-time) time))
    (format t "~d successfully checked!~%~d seconds~%" filenames time)
    (setq *style* 'ascii)
    (when outfilename
      (format t "Writing new version to ~d.~%" outfilename)
      (let ((str (open outfilename :direction :output :if-exists :supersede :if-does-not-exist :create)))
	(output1-sig (input1-sigma) str)
	(close str)))
    (when lispfilename
      (format t "Writing lisp version to ~d.~%" lispfilename)
      (let ((str (open lispfilename :direction :output :if-exists :supersede :if-does-not-exist :create)))
	(output-sig (input1-sigma) str)
	(close str)))))

#+:allegro
(defun save-set-checker-image ()
  (set-fail-to-seriously-fail)
  (setq excl:*restart-app-function* 'checker1-initfn)
  (excl:dumplisp :name (format nil "~d/allegro-scunak-set-checker.dxl" *dxldir*)))

#+:clisp
(defun save-set-checker-image ()
  (set-fail-to-seriously-fail)
  (setq system::*driver* #'checker1-initfn)
  (ext:saveinitmem (format nil "~d/clisp-scunak-set-checker.mem" *dxldir*) :quiet t :init-function 'checker1-initfn))

#+:cmu
(defun save-set-checker-image ()
  (set-fail-to-seriously-fail)
  (extensions:savelisp (format nil "~d/cmucl-scunak-set-checker" *dxldir*) :init-function 'checker1-initfn
		       :print-herald nil))


#+:allegro
(defun save-checker-image ()
  (set-fail-to-seriously-fail)
  (setq excl:*restart-app-function* 'checker0-initfn)
  (excl:dumplisp :name (format nil "~d/allegro-scunak-checker.dxl" *dxldir*)))

#+:clisp
(defun save-checker-image ()
  (set-fail-to-seriously-fail)
  (setq system::*driver* #'checker1-initfn)
  (ext:saveinitmem (format nil "~d/clisp-scunak-checker.mem" *dxldir*) :quiet t :init-function 'checker0-initfn))

#+:cmu
(defun save-checker-image ()
  (set-fail-to-seriously-fail)
  (extensions:savelisp (format nil "~d/cmucl-scunak-checker" *dxldir*) :init-function 'checker0-initfn
		       :print-herald nil))


    
    
  
