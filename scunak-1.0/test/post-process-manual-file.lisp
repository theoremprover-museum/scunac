(defun ppmf (f)
  (let ((s (open f :direction :input))
	(diagnosis nil)
	(fstline t)
	(extralines nil))
    (do ((r (read-line s nil nil) (read-line s nil nil)))
	((null r)
	 (close s))
	(cond ((string-equal r "\\end{tabular}\\")
	       (format t "\\end{tabular}\\\\~%"))
	      ((string-equal r "\\begin{tabular}{ll}")
	       (format t "\\begin{tabular}{ll}~%")
	       (setq fstline t))
	      (fstline
	       (if (and (> (length r) 4)
			(string-equal r "+ \\\\" :start1 (- (length r) 4)))
		   (unless (and (> (length r) 32)
				(string-equal r "{\\bf A} sends & \\verb+(DIAGNOSIS" :start1 0 :end1 32)
				(> (random 200) 0))
		     (format t "~d~%" r))
		 (if (and (>= (length r) 32)
			  (string-equal r "{\\bf A} sends & \\verb+(DIAGNOSIS" :start1 0 :end1 32)
			  (> (random 200) 0))
		     (setq diagnosis t fstline nil)
		   (progn
		     (setq fstline nil extralines t)
		     (format t "~d+\\\\~%" r)))))
	      (diagnosis
	       (when (and (> (length r) 4)
			(string-equal r "+ \\\\" :start1 (- (length r) 4)))
		 (setq diagnosis nil fstline t)))
	      (extralines
	       (if (and (> (length r) 4)
			(string-equal r "+ \\\\" :start1 (- (length r) 4)))
		   (progn
		     (setq extralines nil fstline t)
		     (format t "& \\verb+~d~%" r))
		 (progn
		   (format t "& \\verb+~d+ \\\\~%" r))))
	      (t
	       (format t "~d~%" r))))))

