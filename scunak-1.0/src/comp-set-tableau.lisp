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
; based on Tableaux calculus in catania-2002.pdf - thesis of Calogero G. Zarba page 10
; from the work of Cantone, etc.

(defun prop-comp-set-fragment-p (prop)
  (or (and (or (ieq-p prop) (isubset-p prop) (isetsmeet-p prop) (idisjoint-p prop))
	   (utset-comp-set-fragment-p (app-arg (app-func prop)))
	   (utset-comp-set-fragment-p (app-arg prop)))
      (and (iin-p prop)
	   (if (fpowersetT-p (app-arg (app-func prop)))
	       (and (utset-comp-set-fragment-p (app-arg (app-func prop)))
		    (utset-comp-set-fragment-p (app-arg prop)))
	     (and (utset-comp-set-fragment-p (app-arg (app-func prop)))
		  (utelt-comp-set-fragment-p (app-arg prop)))))
      (and (inot-p prop)
	   (prop-comp-set-fragment-p (app-arg prop)))
      (and (or (iforall-p prop) (iexists-p prop))
	   (utset-comp-set-fragment-p (app-arg (app-func prop)))
	   (comp-set-quantifier-body-p (gen-lam-body (app-arg prop))))
      ))

(defun comp-set-quantifier-body-p (body)
  (or (comp-set-quantifier-in-body-p body)
      (and (inot-p body)
	   (comp-set-quantifier-in-body-p (app-arg body)))))

(defun comp-set-quantifier-in-body-p (body)
  (and (iin-p body)
       (fst-p (app-arg body))
       (equal (fst-arg (app-arg body)) 0) ; the quantified var
       (utset-comp-set-fragment-p (app-arg (app-func body))))) ; this fails if 0 (the quant var) occurs in the set

(defun utset-comp-set-fragment-p (trm)
  (or (bvar-p trm)
      (eq trm '|emptyset|)
      (and (or (binunion-p trm) (binintersect-p trm) (setminus-p trm))
	   (utset-comp-set-fragment-p (app-arg (app-func trm)))
	   (utset-comp-set-fragment-p (app-arg trm)))
      (and (fst-p trm)
	   (tset-comp-set-fragment-p (fst-arg trm)))))

(defun tset-comp-set-fragment-p (trm)
  (or (and (or (ibinunionT-p trm) (ibinintersectT-p trm))
	   (tset-comp-set-fragment-p (app-arg (app-func trm)))
	   (tset-comp-set-fragment-p (app-arg trm)))
      (and (or (icomplementT-p trm) (ipowersetT-p trm))
	   (tset-comp-set-fragment-p (app-arg trm)))
      (bvar-p trm)))

(defun utelt-comp-set-fragment-p (trm)
  (or (bvar-p trm)
      (and (fst-p trm)
	   (bvar-p (fst-arg trm)))))
  
(defun idisjoint-p (prop)
  (and (app-p prop)
       (app-p (app-func prop))
       (eq (app-func (app-func prop)) '|disjoint|)))

(defun isetsmeet-p (prop)
  (and (app-p prop)
       (app-p (app-func prop))
       (eq (app-func (app-func prop)) '|setsmeet|)))

(defun inot-p (prop)
  (and (app-p prop)
       (eq (app-func prop) '|not|)))

(defun iforall-p (prop)
  (and (app-p prop)
       (app-p (app-func prop))
       (eq (app-func (app-func prop)) '|dall|)))

(defun iexists-p (prop)
  (and (app-p prop)
       (app-p (app-func prop))
       (eq (app-func (app-func prop)) '|dex|)))

(defun iin-p (prop)
  (and (app-p prop)
       (app-p (app-func prop))
       (eq (app-func (app-func prop)) '|in|)))

(defun ieq-p (prop)
  (and (app-p prop)
       (app-p (app-func prop))
       (eq (app-func (app-func prop)) '|eq|)))

(defun isubset-p (prop)
  (and (app-p prop)
       (app-p (app-func prop))
       (eq (app-func (app-func prop)) '|subset|)))

(defun fbinunionT-p (trm)
  (and (fst-p trm)
       (ibinunionT-p (fst-arg trm))))

(defun ibinunionT-p (trm)
  (and (app-p trm)
       (app-p (app-func trm))
       (app-p (app-func (app-func trm)))
       (eq (app-func (app-func (app-func trm))) '|binunionT|)))

(defun fbinintersectT-p (trm)
  (and (fst-p trm)
       (ibinintersectT-p (fst-arg trm))))

(defun ibinintersectT-p (trm)
  (and (app-p trm)
       (app-p (app-func trm))
       (app-p (app-func (app-func trm)))
       (eq (app-func (app-func (app-func trm))) '|binintersectT|)))

(defun binunion-p (trm)
  (and (app-p trm)
       (app-p (app-func trm))
       (eq (app-func (app-func trm)) '|binunion|)))

(defun binintersect-p (trm)
  (and (app-p trm)
       (app-p (app-func trm))
       (eq (app-func (app-func trm)) '|binintersect|)))

(defun setminus-p (trm)
  (and (app-p trm)
       (app-p (app-func trm))
       (eq (app-func (app-func trm)) '|setminus|)))

(defun fcomplementT-p (trm)
  (and (fst-p trm)
       (icomplementT-p (fst-arg trm))))

(defun icomplementT-p (trm)
  (and (app-p trm)
       (app-p (app-func trm))
       (eq (app-func (app-func trm)) '|complementT|)))

(defun fpowersetT-p (trm)
  (and (fst-p trm)
       (ipowersetT-p (fst-arg trm))))

(defun ipowersetT-p (trm)
  (and (app-p trm)
       (app-p (app-func trm))
       (eq (app-func (app-func trm)) '|powersetT|)))

(defun ipowerset-p (trm)
  (and (app-p trm)
       (eq (app-func trm) '|powerset|)))

(defun simplify-mls-prop (prop)
  (cond ((or (ieq-p prop) (isubset-p prop))
	 (app-n (app-func (app-func prop))
		(list (simplify-mls-utset (app-arg (app-func prop)))
		      (simplify-mls-utset (app-arg prop)))))
	((iin-p prop)
	 (if (fpowersetT-p (app-arg (app-func prop))) ; irrelevant for now, but maybe in the future I could simplify differently
	     (app (app '|in|
		       (simplify-mls-utset (app-arg (app-func prop))))
		  (simplify-mls-utset (app-arg prop)))
	   (app (app '|in|
		     (simplify-mls-utset (app-arg (app-func prop))))
		(simplify-mls-utset (app-arg prop)))))
	((isetsmeet-p prop)
	 (let ((a (simplify-mls-utset (app-arg (app-func prop))))
	       (b (simplify-mls-utset (app-arg prop))))
	   (app '|not| (app (app '|subset| (app (app '|binintersect| a) b)) '|emptyset|))))
	((idisjoint-p prop)
	 (let ((a (simplify-mls-utset (app-arg (app-func prop))))
	       (b (simplify-mls-utset (app-arg prop))))
	   (app (app '|subset| (app (app '|binintersect| a) b)) '|emptyset|)))
	((inot-p prop)
	 (app '|not|
	      (simplify-mls-prop (app-arg prop))))
	((iforall-p prop)
	 (let ((A (simplify-mls-utset (app-arg (app-func prop))))
	       (body (gen-lam-body (app-arg prop))))
	   (if (inot-p body) ; then it's (forall x:A . ~x::B) -- i.e., A and B disjoint, A \cap B <= emptyset
	       (let ((B (simplify-mls-utset (app-arg (app-func (app-arg body))))))
		 (simplify-mls-prop (app (app '|disjoint| A) B)))
	     ; otherwise, it's (forall x:A . x::B), A <= B
	     (let ((B (simplify-mls-utset (app-arg (app-func body)))))
	       (simplify-mls-prop (app (app '|subset| A) B))))))
	((iexists-p prop)
	 (let ((A (simplify-mls-utset (app-arg (app-func prop))))
	       (body (gen-lam-body (app-arg prop))))
	   (if (inot-p body) ; then it's (exists x:A . ~x::B) -- i.e., ~(A<=B)
	       (let ((B (simplify-mls-utset (app-arg (app-func (app-arg body))))))
		 (simplify-mls-prop (app '|not| (app (app '|subset| A) B))))
	     ; otherwise, it's (exists x:A . x::B), ~(disjoint A B)
	     (let ((B (simplify-mls-utset (app-arg (app-func body)))))
	       (simplify-mls-prop (app '|not| (app (app '|disjoint| A) B)))))))
	(t (fail "problem - unknown case for simplify-mls-prop"))))

(defun simplify-mls-utset (set)
  set)

; returns nil if satisfiable
; returns branch if open and saturated (satisfiable)
(defun mls*-tableau (pos neg)
  (mls*-tableau-0 (mapcar #'simplify-mls-prop pos)
		  (mapcar #'simplify-mls-prop neg)))

(defun mls*-tableau-0 (pos neg)
  (let ((mentioned-elts nil)
	(mentioned-sets nil))
    (dolist (p (append pos neg))
      (setq mentioned-elts (append (mentioned-elts p) mentioned-elts))
      (setq mentioned-sets (append (mentioned-sets p) mentioned-sets)))
    (mls*-tableau-2 pos neg
		    (remove-duplicates mentioned-elts :test #'heq)
		    (remove-duplicates mentioned-sets :test #'heq))))

(defun mls*-tableau-2 (pos neg mentioned-elts mentioned-sets)
  (when (> *verbose* 90)
    (format t "Current Branch:~%")
    (dolist (p pos)
      (format t "+~d~%" (output1-extraction-string p nil nil)))
    (dolist (n neg)
      (format t "-~d~%" (output1-extraction-string n nil nil))))
  (if (or (intersection pos neg :test #'heq)
	  (find-if #'(lambda (x)
		       (and (iin-p x)
			    (eq (app-arg (app-func x)) '|emptyset|)))
		   pos))
      (progn
	(when (> *verbose* 90)
	  (format t "--CLOSED BRANCH--~%"))
	nil) ; branch unsatisfiable
    (multiple-value-bind
     (new pos1 neg1)
     (mls*-tableau-nonbranching pos neg mentioned-elts mentioned-sets)
     (if new
	 (mls*-tableau-2 pos1 neg1 mentioned-elts mentioned-sets)
       (multiple-value-bind
	(new pos1 neg1 newelts)
	(mls*-tableau-witness pos neg mentioned-elts mentioned-sets)
	(if new
	    (mls*-tableau-2 pos1 neg1 (append newelts mentioned-elts) mentioned-sets)
	  (multiple-value-bind
	   (new pos1 neg1 pos2 neg2)
	   (mls*-tableau-branching pos neg mentioned-elts mentioned-sets)
	   (if new
	       (progn
		 (when (> *verbose* 95)
		   (format t "Delaying Branch~%")
		   (dolist (p pos2)
		     (format t "+~d~%" (output1-extraction-string p nil nil)))
		   (dolist (n neg2)
		     (format t "-~d~%" (output1-extraction-string n nil nil))))
		 (or (mls*-tableau-2 pos1 neg1 mentioned-elts mentioned-sets)
		     (mls*-tableau-2 pos2 neg2 mentioned-elts mentioned-sets)))
	  ; otherwise, saturated, should be satisfiable...
	     (list pos neg)))))))))

; returns values <bool> <pos1> <neg1>
(defun mls*-tableau-nonbranching (pos neg mentioned-elts mentioned-sets)
  (let ((pos1 pos)
	(neg1 neg)
	(new nil))
    (dolist (p pos)
      (when (iin-p p)
	(let ((x (app-arg p))
	      (A (app-arg (app-func p))))
	  (when (and (fst-p A) (bvar-p (fst-arg A)))
	    (let ((pred (dclass-pred (get (fst-arg A) 'dbtype))))
	      (when (and (app-p pred)
			 (eq (app-func pred) '|in|)
			 (app-p (app-arg pred))
			 (eq (app-func (app-arg pred)) '|powerset|))
		(let* ((U (app-arg (app-arg pred)))
		       (p2 (app-n '|in| (list U x))))
		  (unless (member p2 pos1 :test #'heq)
		    (push p2 pos1)
		    (setq new t)
		    )))))
	  (dolist (AUB mentioned-sets)
;	    (format t "AUB = ~d~%A = ~d~%" AUB A) ; delete me
	    (when (and (fbinunionT-p AUB)
		       (or (heq (fst (app-arg (fst-arg AUB))) A)
			   (heq (fst (app-arg (app-func (fst-arg AUB)))) A)))
	      (let ((p2 (app-n '|in| (list AUB x))))
		(unless (member p2 pos1 :test #'heq)
		  (push p2 pos1)
		  (setq new t)
		  )))
	    (when (and (binunion-p AUB)
		       (or (heq (app-arg AUB) A)
			   (heq (app-arg (app-func AUB)) A)))
	      (let ((p2 (app-n '|in| (list AUB x))))
		(unless (member p2 pos1 :test #'heq)
		  (push p2 pos1)
		  (setq new t)
		  ))))
	  (dolist (p1 pos)
	    (when (and (iin-p p1) (heq (app-arg p1) x))
	      (dolist (AIB mentioned-sets)
		(when (and (fbinintersectT-p AIB)
			   (heq (fst (app-arg (app-func (fst-arg AIB)))) A)
			   (heq (fst (app-arg (fst-arg AIB))) (app-arg (app-func p1))))
		  (let ((p2 (app-n '|in| (list AIB x))))
		    (unless (member p2 pos1 :test #'heq)
		      (push p2 pos1)
		      (setq new t))))
		(when (and (binintersect-p AIB)
			   (heq (app-arg (app-func AIB)) A)
			   (heq (app-arg AIB) (app-arg (app-func p1))))
		  (let ((p2 (app-n '|in| (list AIB x))))
		    (unless (member p2 pos1 :test #'heq)
		      (push p2 pos1)
		      (setq new t)))))))
	  (dolist (p1 neg)
	    (when (and (iin-p p1) (heq (app-arg p1) x))
	      (dolist (AMB mentioned-sets)
		(when (and (setminus-p AMB)
			   (heq (app-arg (app-func AMB)) A)
			   (heq (app-arg AMB) (app-arg (app-func p1))))
		  (let ((p2 (app-n '|in| (list AMB x))))
		    (unless (member p2 pos1 :test #'heq)
		      (push p2 pos1)
		      (setq new t)))))))
	  (when (setminus-p A)
	    (let ((p2 (app-n '|in| (list (app-arg (app-func A)) x)))
		  (n3 (app-n '|in| (list (app-arg A) x))))
	      (unless (member p2 pos1 :test #'heq)
		(push p2 pos1)
		(setq new t))
	      (unless (member n3 neg1 :test #'heq)
		(push n3 neg1)
		(setq new t))))
	  (when (binintersect-p A)
	    (let ((p2 (app-n '|in| (list (app-arg (app-func A)) x)))
		  (p3 (app-n '|in| (list (app-arg A) x))))
	      (unless (member p2 pos1 :test #'heq)
		(push p2 pos1)
		(setq new t))
	      (unless (member p3 pos1 :test #'heq)
		(push p3 pos1)
		(setq new t))))
	  (when (fbinintersectT-p A)
	    (let ((p2 (app-n '|in| (list (fst (app-arg (app-func (fst-arg A)))) x)))
		  (p3 (app-n '|in| (list (fst (app-arg (fst-arg A))) x))))
	      (unless (member p2 pos1 :test #'heq)
		(push p2 pos1)
		(setq new t))
	      (unless (member p3 pos1 :test #'heq)
		(push p3 pos1)
		(setq new t))))
	  (when (fcomplementT-p A) ; like setminus, but different
	    (let ((p2 (app-n '|in| (list (fst (app-arg (fst-arg A))) x))))
	      (unless (member p2 neg1 :test #'heq)
		(push p2 neg1)
		(setq new t))))
	  (when (fpowersetT-p A) ; assume powersets only occur on right of in
	    (let ((p2 (app-n '|subset| (list x (fst (app-arg (fst-arg A)))))))
	      (unless (member p2 pos1 :test #'heq)
		(push p2 pos1)
		(setq new t))))))
      (when (ieq-p p) ; assume this is equality at set level; make two subsets
	(let ((p2 (app-n '|subset| (list (app-arg (app-func p)) (app-arg p))))
	      (p3 (app-n '|subset| (list (app-arg p) (app-arg (app-func p))))))
	  (unless (member p2 pos1 :test #'heq)
	    (push p2 pos1)
	    (setq new t))
	  (unless (member p3 pos1 :test #'heq)
	    (push p3 pos1)
	    (setq new t))))
      (when (isubset-p p)
	(dolist (p1 pos)
	  (when (and (iin-p p1) (heq (app-arg (app-func p1)) (app-arg (app-func p))))
	    (let ((p2 (app-n '|in| (list (app-arg p) (app-arg p1)))))
	      (unless (member p2 pos1 :test #'heq)
		(push p2 pos1)
		(setq new t))))))
      (when (inot-p p)
	(unless (member (app-arg p) neg1 :test #'heq)
	  (push (app-arg p) neg1)
	  (setq new t)))
      )
    (dolist (n neg)
      (when (inot-p n)
	(unless (member (app-arg n) pos1 :test #'heq)
	  (push (app-arg n) pos1)
	  (setq new t)))
      (when (iin-p n)
	(let ((x (app-arg n))
	      (A (app-arg (app-func n))))
	  (when (fpowersetT-p A)
	    (let ((p2 (app-n '|subset| (list x (fst (app-arg (fst-arg A)))))))
	      (unless (member p2 neg1 :test #'heq)
		(push p2 neg1)
		(setq new t))))
	  (dolist (CA mentioned-sets)
	    (when (and (fcomplementT-p CA)
		       (heq (fst (app-arg (fst-arg CA))) A))
	      (let ((p2 (app-n '|in| (list CA x))))
		(unless (member p2 pos1 :test #'heq)
		  (push p2 pos1)
		  (setq new t)
		  )))))))
    (if new
	(values t pos1 neg1)
      nil)))

; returns values <bool> <pos1> <neg1> <newelts>)
(defun mls*-tableau-witness (pos neg mentioned-elts mentioned-sets)
  (let ((pos1 pos)
	(neg1 neg)
	(newelts nil)
	(new nil))
    (dolist (p neg)
      (when (isubset-p p) ; A <= B
	(let ((A (app-arg (app-func p)))
	      (B (app-arg p)))
	  (unless (find-if #'(lambda (p1)
			       (and (iin-p p1)
				    (heq (app-arg (app-func p1)) A)
				    (let ((w (app-arg p1)))
				      (find-if #'(lambda (n1)
						   (and (iin-p n1)
							(heq (app-arg (app-func n1)) B)
							(heq (app-arg n1) w)))
					       neg))))
			   pos)
	    (let ((w (intern-gensym)))
	      (setf (get w 'bvar) t)
	      (setf (get w 'dbtype) (obj))
	      (push w newelts)
	      (setq new t)
	      (let ((p2 (app-n '|in| (list A w)))
		    (p3 (app-n '|in| (list B w))))
		(push p2 pos1)
		(push p3 neg1)))))))
    (if new
	(values t pos1 neg1 newelts)
      nil)))

; returns values <bool> <pos1> <neg1> <pos2> <neg2>)
(defun mls*-tableau-branching (pos neg mentioned-elts mentioned-sets)
  (let ((pos1 pos)
	(neg1 neg)
	(pos2 pos)
	(neg2 neg)
	(new nil))
    (dolist (p pos)
      (unless new
	(when (and (iin-p p)
		   (fbinunionT-p (app-arg (app-func p))))
	  (let ((p2 (app-n '|in| (list (fst (app-arg (app-func (fst-arg (app-arg (app-func p))))))
				       (app-arg p))))
		(p3 (app-n '|in| (list (fst (app-arg (fst-arg (app-arg (app-func p)))))
				       (app-arg p)))))
	    (unless (or (member p2 pos :test #'heq)
			(member p3 pos :test #'heq))
	      (push p2 pos1)
	      (push p3 pos2)
	      (setq new t))))))
    (if new
	(values t pos1 neg1 pos2 neg2)
      (progn
	(dolist (p pos)
	  (unless new
	    (when (and (iin-p p)
		       (binunion-p (app-arg (app-func p))))
	      (let ((p2 (app-n '|in| (list (app-arg (app-func (app-arg (app-func p))))
					   (app-arg p))))
		    (p3 (app-n '|in| (list (app-arg (app-arg (app-func p)))
					   (app-arg p)))))
		(unless (or (member p2 pos :test #'heq)
			    (member p3 pos :test #'heq))
		  (push p2 pos1)
		  (push p3 pos2)
		  (setq new t))))))
	(if new
	    (values t pos1 neg1 pos2 neg2)
	  (progn
	    (dolist (p neg)
	      (unless new
		(when (ieq-p p)
		  (let ((p2 (app-n '|subset| (list (app-arg (app-func p))
						   (app-arg p))))
			(p3 (app-n '|subset| (list (app-arg p)
						   (app-arg (app-func p))
						   ))))
		    (unless (or (member p2 neg :test #'heq)
				(member p3 neg :test #'heq))
		      (push p2 neg1)
		      (push p3 neg2)
		      (setq new t))))))
	    (if new
		(values t pos1 neg1 pos2 neg2)
	      (progn ; last possibility is a cut on x::A
		(dolist (x mentioned-elts)
		  (unless new
		    (dolist (A mentioned-sets)
		      (unless new
			(let ((xinA (app-n '|in| (list A x))))
			  (unless (or (member xinA pos :test #'heq)
				      (member xinA neg :test #'heq))
			    (setq new t)
			    (push xinA pos1)
			    (push xinA neg2)))))))
		(if new
		    (values t pos1 neg1 pos2 neg2)
		  nil)))))))))

(defun mentioned-sets (prop)
  (cond ((or (ieq-p prop) (isubset-p prop))
	 (append (mentioned-sets-trm (app-arg (app-func prop)))
		 (mentioned-sets-trm (app-arg prop))))
	((iin-p prop)
	 (if (fpowersetT-p (app-arg (app-func prop)))
	     (append (mentioned-sets-trm (app-arg (app-func prop)))
		     (mentioned-sets-trm (app-arg prop)))
	   (mentioned-sets-trm (app-arg (app-func prop)))
	   ))
	(t nil)))

(defun mentioned-sets-trm (trm &optional tp)
  (cond ((or (ibinunionT-p trm) (ibinintersectT-p trm))
	 (cons (fst trm)
	       (append (mentioned-sets-trm (app-arg (app-func trm)) t)
		       (mentioned-sets-trm (app-arg trm) t))))
	((or (icomplementT-p trm) (ipowersetT-p trm))
	 (cons (fst trm) (mentioned-sets-trm (app-arg trm) t)))
	((fst-p trm)
	 (cons trm (mentioned-sets-trm (fst-arg trm) t)))
	(t (if tp (list (fst trm)) (list trm)))))

(defun mentioned-elts (prop)
  (cond ((iin-p prop)
	 (if (fpowersetT-p (app-arg (app-func prop)))
	     nil
	   (list (app-arg prop))))
	(t nil)))
