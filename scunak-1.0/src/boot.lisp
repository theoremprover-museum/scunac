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
; October/December 2005

(defvar *dxldir* ".")

;(defvar *style* 'ansi-color)
(defvar *style* 'ascii) ; colors slow things down a lot!

(defun intern-gensym (&optional nameroot)
  (if nameroot
      (intern (format nil "~d" (gensym nameroot)))
    (intern (format nil "~d" (gensym)))))

(defun fail (msg &rest vals)
  (setq *failvals* vals)
  (error (format nil "~d~%~S~%" msg vals)))

; for official releases, exit on fail
(defun seriously-fail (msg vals)
  (if vals
      (format t "FATAL ERROR: ~d~%~S~%" msg vals)
    (format t "FATAL ERROR: ~d~%" msg))
  (format t "Bye.")
  (exit))

(defun set-fail-to-seriously-fail ()
  (defun fail (msg &rest vals)
    (seriously-fail msg vals)))

(defun set-fail-to-throw-fail ()
  (defun fail (msg &rest vals)
    (when (> *verbose* 1)
      (format t "~d~%" msg))
    (throw 'fail nil)))

(defun 2+ (n)
  (1+ (1+ n)))

(defun command-line-args ()
  #+(or :allegro :excl)(sys:command-line-arguments)
  #+:clisp ext::*args*
  #+:cmu extensionions:*command-line-strings*)

(defun command-line-arg (name)
  (cadr (command-line-switch name)))

(defun command-line-arg-several (name)
  (let ((sw (command-line-switch name))
	(ret nil))
    (when sw
      (do ((args2 (cdr sw) (cdr args2)))
	  ((or (null args2)
	       (and (> (length (car args2)) 0)
		    (eq (aref (car args2) 0) #\-)))
	   (reverse ret))
	  (push (car args2) ret)))))

(defun command-line-switch (name)
  (do ((args (command-line-args) (cdr args)))
      ((or (null args) (string= name (car args)))
       args)))

;(defun scunak-logo ()
;  (format t "  O O    XXXXXXXXXXXXXXXXXXXXXXXXXX~%")
;  (format t " O   O                             ~%")
;  (format t "      O  XXXXXXXXXXXXXXXXXXXXXXXXXX~%")
;  (format t "O                                  ~%")
;  (format t "      O  XXXXXXXXXXXXXXXXXXXXXXXXXX~%")
;  (format t " O   O                             ~%")
;  (format t "  O O    XXXXXXXXXXXXXXXXXXXXXXXXXX~%")
;  (format t "                                   ~%")
;  (format t "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX~%")
;  (format t "                                   ~%")
;  (format t "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX~%")
;  (format t "                                   ~%")
;  (format t "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX~%")
;  )

;(defun scunak-logo ()
;  (format t "   * * *    XXXXXXXXXXXXXXXXXXXXXXXXXX      SS                                ~%")
;  (format t "  *     *   @@@@@@@@@@@@@@@@@@@@@@@@@@     S  S                               ~%")
;  (format t "         *  XXXXXXXXXXXXXXXXXXXXXXXXXX     S                                  ~%")
;  (format t " *          @@@@@@@@@@@@@@@@@@@@@@@@@@     S                             k    ~%")
;  (format t "         *  XXXXXXXXXXXXXXXXXXXXXXXXXX     S                             k    ~%")
;  (format t "  *     *   @@@@@@@@@@@@@@@@@@@@@@@@@@     S                             k    ~%")
;  (format t "   * * *    XXXXXXXXXXXXXXXXXXXXXXXXXX      SS    cc   u  u  nnn    aa   k   k~%")
;  (format t "            @@@@@@@@@@@@@@@@@@@@@@@@@@        S  c  c  u  u  n  n     a  k  k ~%")
;  (format t "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX        S  c     u  u  n  n     a  k k  ~%")
;  (format t "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@        S  c     u  u  n  n   aaa  kk   ~%")
;  (format t "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX     S  S  c     u  u  n  n  a  a  k k  ~%")
;  (format t "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@     S  S  c  c  u  u  n  n  a  a  k  k ~%")
;  (format t "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX      SS    cc    uuu  n  n   aa a k   k~%")
;  )

; the ansi-color works in emacs if in the .emacs is
; (autoload 'ansi-color-for-comint-mode-on "ansi-color" nil t)
; (add-hook 'shell-mode-hook 'ansi-color-for-comint-mode-on)
; or if one does the following (from http://www.emacswiki.org/cgi-bin/wiki/ansi-color.el):
;; 2. load this file: M-x load-library RET ansi-color RET
;; 3. activate ansi-color: M-x ansi-color-for-comint-mode-on

(defun ansi-begin ()
  (when (eq *style* 'ansi-color)
    (write-char (code-char 27))
    (write-char (code-char 91))
    ))

(defun ansi-end ()
  (when (eq *style* 'ansi-color)
    (write-char (code-char 109))
    ))

(defun ansi-normal ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 48))
    (ansi-end)))

(defun ansi-fg-blue ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 51)) (write-char (code-char 52))
    (ansi-end)))

(defun ansi-bg-blue-fg-white ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 51)) (write-char (code-char 55))
    (write-char (code-char 59))
    (write-char (code-char 52)) (write-char (code-char 52))
    (ansi-end)))

(defun ansi-bg-red ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 52)) (write-char (code-char 49))
    (ansi-end)))

(defun ansi-bg-red-fg-red ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 51)) (write-char (code-char 49))
    (write-char (code-char 59))
    (write-char (code-char 52)) (write-char (code-char 49))
    (ansi-end)))

(defun ansi-bg-white ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 52)) (write-char (code-char 55))
    (ansi-end)))

(defun ansi-bg-white-fg-white ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 51)) (write-char (code-char 55))
    (write-char (code-char 59))
    (write-char (code-char 52)) (write-char (code-char 55))
    (ansi-end)))

(defun ansi-bold-fg-white-bg-black ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 49))
    (write-char (code-char 59))
    (write-char (code-char 51)) (write-char (code-char 55))
    (write-char (code-char 59))
    (write-char (code-char 52)) (write-char (code-char 48))
    (ansi-end)))

(defun ansi-bold-fg-yellow-bg-black ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 49))
    (write-char (code-char 59))
    (write-char (code-char 51)) (write-char (code-char 51))
    (write-char (code-char 59))
    (write-char (code-char 52)) (write-char (code-char 48))
    (ansi-end)))

(defun ansi-bold-fg-green-bg-black ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 49))
    (write-char (code-char 59))
    (write-char (code-char 51)) (write-char (code-char 50))
    (write-char (code-char 59))
    (write-char (code-char 52)) (write-char (code-char 48))
    (ansi-end)))

(defun ansi-bold-fg-red-bg-black ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 49))
    (write-char (code-char 59))
    (write-char (code-char 51)) (write-char (code-char 49))
    (write-char (code-char 59))
    (write-char (code-char 52)) (write-char (code-char 48))
    (ansi-end)))

(defun ansi-bold-fg-black-bg-red ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 49))
    (write-char (code-char 59))
    (write-char (code-char 51)) (write-char (code-char 48))
    (write-char (code-char 59))
    (write-char (code-char 52)) (write-char (code-char 49))
    (ansi-end)))

(defun ansi-bold-fg-white-bg-red ()
  (when (eq *style* 'ansi-color)
    (ansi-begin)
    (write-char (code-char 49))
    (write-char (code-char 59))
    (write-char (code-char 51)) (write-char (code-char 55))
    (write-char (code-char 59))
    (write-char (code-char 52)) (write-char (code-char 49))
    (ansi-end)))

; betsy ross flag
;(defun scunak-logo ()
;  (ansi-bg-blue-fg-white)
;  (format t "   * * *    ")
;  (ansi-bg-red)
;  (format t "                          ")
;  (ansi-normal)
;  (format t "      SS                                ~%")
;  (ansi-bg-blue-fg-white)
;  (format t "  *     *   ")
;  (ansi-bg-white)
;  (format t "                          ")
;  (ansi-normal)
;  (format t "     S  S                               ~%")
;  (ansi-bg-blue-fg-white)
;  (format t "         *  ")
;  (ansi-bg-red)
;  (format t "                          ")
;  (ansi-normal)
;  (format t "     S                                  ~%")
;  (ansi-bg-blue-fg-white)
;  (format t " *          ")
;  (ansi-bg-white)
;  (format t "                          ")
;  (ansi-normal)
;  (format t "     S                             k    ~%")
;  (ansi-bg-blue-fg-white)
;  (format t "         *  ")
;  (ansi-bg-red)
;  (format t "                          ")
;  (ansi-normal)
;  (format t "     S                             k    ~%")
;  (ansi-bg-blue-fg-white)
;  (format t "  *     *   ")
;  (ansi-bg-white)
;  (format t "                          ")
;  (ansi-normal)
;  (format t "     S                             k    ~%")
;  (ansi-bg-blue-fg-white)
;  (format t "   * * *    ")
;  (ansi-bg-red)
;  (format t "                          ")
;  (ansi-normal)
;  (format t "      SS    cc   u  u  nnn    aa   k   k~%")
;  (ansi-bg-white)
;  (format t "                                      ")
;  (ansi-normal)
;  (format t "        S  c  c  u  u  n  n     a  k  k ~%")
;  (ansi-bg-red)
;  (format t "                                      ")
;  (ansi-normal)
;  (format t "        S  c     u  u  n  n     a  k k  ~%")
;  (ansi-bg-white)
;  (format t "                                      ")
;  (ansi-normal)
;  (format t "        S  c     u  u  n  n   aaa  kk   ~%")
;  (ansi-bg-red)
;  (format t "                                      ")
;  (ansi-normal)
;  (format t "     S  S  c     u  u  n  n  a  a  k k  ~%")
;  (ansi-bg-white)
;  (format t "                                      ")
;  (ansi-normal)
;  (format t "     S  S  c  c  u  u  n  n  a  a  k  k ~%")
;  (ansi-bg-red)
;  (format t "                                      ")
;  (ansi-normal)
;  (format t "      SS    cc    uuu  n  n   aa a k   k~%")
;  )

; 13 star flag
(defun scunak-logo-flag ()
  (ansi-bg-blue-fg-white)
  (format t "             ")
  (ansi-bg-red-fg-red)
  (format t "--------------------------")
  (ansi-normal)
  (format t "      SS                                ~%")
  (ansi-bg-blue-fg-white)
  (format t "  *   *   *  ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "     S  S                               ~%")
  (ansi-bg-blue-fg-white)
  (format t "    *   *    ")
  (ansi-bg-red-fg-red)
  (format t "--------------------------")
  (ansi-normal)
  (format t "     S                                  ~%")
  (ansi-bg-blue-fg-white)
  (format t "  *   *   *  ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "     S                             k    ~%")
  (ansi-bg-blue-fg-white)
  (format t "    *   *    ")
  (ansi-bg-red-fg-red)
  (format t "--------------------------")
  (ansi-normal)
  (format t "     S                             k    ~%")
  (ansi-bg-blue-fg-white)
  (format t "  *   *   *  ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "     S                             k    ~%")
  (ansi-bg-blue-fg-white)
  (format t "             ")
  (ansi-bg-red-fg-red)
  (format t "--------------------------")
  (ansi-normal)
  (format t "      SS    cc   u  u  nnn    aa   k   k~%")
  (ansi-bg-white-fg-white)
  (format t "             ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "        S  c  c  u  u  n  n     a  k  k ~%")
  (ansi-bg-red-fg-red)
  (format t "-------------")
  (ansi-bg-red-fg-red)
  (format t "--------------------------")
  (ansi-normal)
  (format t "        S  c     u  u  n  n     a  k k  ~%")
  (ansi-bg-white-fg-white)
  (format t "             ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "        S  c     u  u  n  n   aaa  kk   ~%")
  (ansi-bg-red-fg-red)
  (format t "-------------")
  (ansi-bg-red-fg-red)
  (format t "--------------------------")
  (ansi-normal)
  (format t "     S  S  c     u  u  n  n  a  a  k k  ~%")
  (ansi-bg-white-fg-white)
  (format t "             ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "     S  S  c  c  u  u  n  n  a  a  k  k ~%")
  (ansi-bg-red-fg-red)
  (format t "-------------")
  (ansi-bg-red-fg-red)
  (format t "--------------------------")
  (ansi-normal)
  (format t "      SS    cc    uuu  n  n   aa a k   k~%")
  )

; invisible flag logo
(defun scunak-logo-bw-inv-flag ()
  (ansi-bg-blue-fg-white)
  (format t "             ")
  (ansi-bg-red-fg-red)
  (format t "                          ")
  (ansi-normal)
  (format t "      SS                                ~%")
  (ansi-bg-blue-fg-white)
  (format t "             ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "     S  S                               ~%")
  (ansi-bg-blue-fg-white)
  (format t "             ")
  (ansi-bg-red-fg-red)
  (format t "                          ")
  (ansi-normal)
  (format t "     S                                  ~%")
  (ansi-bg-blue-fg-white)
  (format t "             ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "     S                             k    ~%")
  (ansi-bg-blue-fg-white)
  (format t "             ")
  (ansi-bg-red-fg-red)
  (format t "                          ")
  (ansi-normal)
  (format t "     S                             k    ~%")
  (ansi-bg-blue-fg-white)
  (format t "             ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "     S                             k    ~%")
  (ansi-bg-blue-fg-white)
  (format t "             ")
  (ansi-bg-red-fg-red)
  (format t "                          ")
  (ansi-normal)
  (format t "      SS    cc   u  u  nnn    aa   k   k~%")
  (ansi-bg-white-fg-white)
  (format t "             ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "        S  c  c  u  u  n  n     a  k  k ~%")
  (ansi-bg-red-fg-red)
  (format t "             ")
  (ansi-bg-red-fg-red)
  (format t "                          ")
  (ansi-normal)
  (format t "        S  c     u  u  n  n     a  k k  ~%")
  (ansi-bg-white-fg-white)
  (format t "             ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "        S  c     u  u  n  n   aaa  kk   ~%")
  (ansi-bg-red-fg-red)
  (format t "             ")
  (ansi-bg-red-fg-red)
  (format t "                          ")
  (ansi-normal)
  (format t "     S  S  c     u  u  n  n  a  a  k k  ~%")
  (ansi-bg-white-fg-white)
  (format t "             ")
  (ansi-bg-white-fg-white)
  (format t "                          ")
  (ansi-normal)
  (format t "     S  S  c  c  u  u  n  n  a  a  k  k ~%")
  (ansi-bg-red-fg-red)
  (format t "             ")
  (ansi-bg-red-fg-red)
  (format t "                          ")
  (ansi-normal)
  (format t "      SS    cc    uuu  n  n   aa a k   k~%")
  )

(defun scunak-header (extra)
  (if *flag-logo*
      (scunak-logo-flag)
    (scunak-logo-bw-inv-flag))
  (if extra
      (format t "~d~%" extra)
    (format t "Welcome to Scunak~%"))
  (format t "Copyright (C) 2006, Chad E Brown.~%")
  (format t "Scunak comes with ABSOLUTELY NO WARRANTY.~%")
  (format t "This is free software, and you are welcome to redistribute it~%")
  (format t "under certain conditions; see the file LICENSE for details.~%")
  )

(defun yellow-on-black-output (s)
  (let ((*standard-output* (make-string-output-stream)))
    (ansi-bold-fg-yellow-bg-black)
    (format t "~d" s)
    (ansi-normal)
    (get-output-stream-string *standard-output*)))

(defun green-on-black-output (s)
  (let ((*standard-output* (make-string-output-stream)))
    (ansi-bold-fg-green-bg-black)
    (format t "~d" s)
    (ansi-normal)
    (get-output-stream-string *standard-output*)))

(defun red-on-black-output (s)
  (let ((*standard-output* (make-string-output-stream)))
    (ansi-bold-fg-red-bg-black)
    (format t "~d" s)
    (ansi-normal)
    (get-output-stream-string *standard-output*)))

(defun white-on-black-output (s)
  (let ((*standard-output* (make-string-output-stream)))
    (ansi-bold-fg-white-bg-black)
    (format t "~d" s)
    (ansi-normal)
    (get-output-stream-string *standard-output*)))

(defun black-on-red-output (s)
  (let ((*standard-output* (make-string-output-stream)))
    (ansi-bold-fg-black-bg-red)
    (format t "~d" s)
    (ansi-normal)
    (get-output-stream-string *standard-output*)))

(defun white-on-red-output (s)
  (let ((*standard-output* (make-string-output-stream)))
    (ansi-bold-fg-white-bg-red)
    (format t "~d" s)
    (ansi-normal)
    (get-output-stream-string *standard-output*)))

#+:allegro
(defun call-system (str)
  (excl:run-shell-command str))

#+:clisp
(defun call-system (str)
  (ext:shell str))

#-(or :clisp :allegro)
(defun call-system (str)
  (format t "Ignoring call to ~d in this lisp" str))

#+:allegro
(defun create-socket (mach port)
  (if (stringp mach)
      (if (numberp port)
	  (acl-socket:make-socket :remote-host mach :remote-port port)
	(fail (format nil "~d is not a port" port)))
    (fail (format nil "~d is not a host" mach))))

#+:clisp
(defun create-socket (mach port)
  (if (stringp mach)
      (if (numberp port)
	  (socket:socket-connect port mach :external-format :dos)
	(fail (format nil "~d is not a port" port)))
    (fail (format nil "~d is not a host" mach))))

#-(or :clisp :allegro)
(defun create-socket (mach sock)
  (format t "Ignoring request to create a socket in this lisp" str))

(defun read-scunak-socket-line ()
  (when (and (streamp *scunak-socket*)
	     (open-stream-p *scunak-socket*))
    (let ((r (read *scunak-socket* nil nil)))
      (if (and (consp r) (eq (car r) 'LINE))
	  (cadr r)
	(progn
	  (format t "WARNING: Expected a Line.  Received ~S~%" r)
	  "")))))
