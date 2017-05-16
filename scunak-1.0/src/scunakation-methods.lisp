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
; File: scunakation-methods.lisp
; March 2006

; The scunakation methods are defined here.
; This encodes the Knowledge Base for Knowledge Based Scunakation

(scunakator~defmethod PF1
 (precondition (text-fits (PROOF1)))
 (postcondition (text-is PROOF0))
 (priority 1)
 (defn #'(LAMBDA (X) X))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod D
 (precondition (text-fits (LET WH
                            "$"
                            MATHVARIABLE
                            "$"
                            WH
                            "be"
                            WH
                            A
                            WH
                            ATTRIBUTION)))
 (postcondition (text-is PROOF1))
 (priority 2)
 (defn #'(LAMBDA (L WH1 VAR WH2 WH3 A WH4 ATTR)
		 (format nil "let ~d:~d."
			 var
			 attr)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod D239
 (precondition (text-fits (LET WH
                            "$"
                            MATHVARIABLE
                            "$"
                            WH
                            "be"
                            WH
                            "given")))
 (postcondition (text-is PROOF1))
 (priority 3)
 (defn #'(LAMBDA (L WH1 VAR WH2 WH3)
		 (format nil "let ~d."
			 var
			 attr)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod D240
 (precondition (text-fits (ASSUME WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 4)
 (defn #'(LAMBDA (A W P)
		 (format nil "assume ~d."
			 p)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L
 (precondition (text-fits ("Let")))
 (postcondition (text-is LET))
 (priority 5)
 (defn "Let")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L241
 (precondition (text-fits ("let")))
 (postcondition (text-is LET))
 (priority 6)
 (defn "let")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A
 (precondition (text-fits ("Assume")))
 (postcondition (text-is ASSUME))
 (priority 7)
 (defn "Assume")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A242
 (precondition (text-fits ("assume")))
 (postcondition (text-is ASSUME))
 (priority 8)
 (defn "assume")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A243
 (precondition (text-fits ("Suppose")))
 (postcondition (text-is ASSUME))
 (priority 9)
 (defn "Suppose")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A244
 (precondition (text-fits ("suppose")))
 (postcondition (text-is ASSUME))
 (priority 10)
 (defn "suppose")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A245
 (precondition (text-fits ("a")))
 (postcondition (text-is A))
 (priority 11)
 (defn "a")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A246
 (precondition (text-fits ("an")))
 (postcondition (text-is A))
 (priority 12)
 (defn "an")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H
 (precondition (text-fits (HENCE WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 13)
 (defn #'(LAMBDA (H X Y)
		 (format nil "hence ~d." Y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1
 (precondition (text-fits ("then")))
 (postcondition (text-is HENCE))
 (priority 14)
 (defn "then")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1247
 (precondition (text-fits ("Then")))
 (postcondition (text-is HENCE))
 (priority 15)
 (defn "Then")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1248
 (precondition (text-fits ("Then,")))
 (postcondition (text-is HENCE))
 (priority 16)
 (defn "Then,")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1249
 (precondition (text-fits ("Hence")))
 (postcondition (text-is HENCE))
 (priority 17)
 (defn "Hence")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1250
 (precondition (text-fits ("hence")))
 (postcondition (text-is HENCE))
 (priority 18)
 (defn "hence")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1251
 (precondition (text-fits ("so")))
 (postcondition (text-is HENCE))
 (priority 19)
 (defn "so")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1252
 (precondition (text-fits ("so" WH "that")))
 (postcondition (text-is HENCE))
 (priority 20)
 (defn #'(LAMBDA (W) (LIST "so" W "that")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1253
 (precondition (text-fits ("Thus")))
 (postcondition (text-is HENCE))
 (priority 21)
 (defn "Thus")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1254
 (precondition (text-fits ("Thus,")))
 (postcondition (text-is HENCE))
 (priority 22)
 (defn "Thus,")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1255
 (precondition (text-fits ("Therefore,")))
 (postcondition (text-is HENCE))
 (priority 23)
 (defn "Therefore,")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1256
 (precondition (text-fits ("This" WH "means" WH "that")))
 (postcondition (text-is HENCE))
 (priority 24)
 (defn #'(LAMBDA (WH1 WH2) (LIST "This" WH1 "means" WH2 "that")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1257
 (precondition (text-fits ("This" WH "shows" WH "that")))
 (postcondition (text-is HENCE))
 (priority 25)
 (defn #'(LAMBDA (WH1 WH2) (LIST "This" WH1 "shows" WH2 "that")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H1258
 (precondition (text-fits ("It" WH "follows" WH "that")))
 (postcondition (text-is HENCE))
 (priority 26)
 (defn #'(LAMBDA (WH1 WH2) (LIST "It" WH1 "follows" WH2 "that")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod F
 (precondition (text-fits (FROM WH REF "," WH WEHAVE WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 27)
 (defn #'(LAMBDA (F W1 R W2 WEHAVE W3 P)
;		 (format nil "from ~d fact ~d."
;			 R P)
		 (format nil "clearly ~d."
			 P)
		 ))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod F259
 (precondition (text-fits ("In" WH "view" WH "of")))
 (postcondition (text-is FROM))
 (priority 28)
 (defn #'(LAMBDA (X Y) (LIST "In" X "view" Y "of")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod F260
 (precondition (text-fits ("From")))
 (postcondition (text-is FROM))
 (priority 29)
 (defn "From")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod W
 (precondition (text-fits ("we" WH "have")))
 (postcondition (text-is WEHAVE))
 (priority 30)
 (defn #'(LAMBDA (X) (LIST "we" X "have")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod W261
 (precondition (text-fits ("we" WH "have" WH "that")))
 (postcondition (text-is WEHAVE))
 (priority 31)
 (defn #'(LAMBDA (X Y) (LIST "we" X "have" Y "that")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod W262
 (precondition (text-fits ("we" WH "conclude" WH "that")))
 (postcondition (text-is WEHAVE))
 (priority 32)
 (defn #'(LAMBDA (X Y) (LIST "we" X "conclude" Y "that")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod W263
 (precondition (text-fits ("we" WH "conclude")))
 (postcondition (text-is WEHAVE))
 (priority 33)
 (defn #'(LAMBDA (X) (LIST "we" X "conclude")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R
 (precondition (text-fits ("Definition" WH REFNUM)))
 (postcondition (text-is REF))
 (priority 34)
 (defn #'(LAMBDA (X Y) (format nil "[definition ~d]" Y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R264
 (precondition (text-fits ("Theorem" WH REFNUM)))
 (postcondition (text-is REF))
 (priority 35)
 (defn #'(LAMBDA (X Y) (format nil "[theorem ~d]" Y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R265
 (precondition (text-fits ("Lemma" WH REFNUM)))
 (postcondition (text-is REF))
 (priority 36)
 (defn #'(LAMBDA (X Y) (format nil "[lemma ~d]" Y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R266
 (precondition (text-fits ("(i)")))
 (postcondition (text-is REF))
 (priority 37)
 (defn "(i)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R267
 (precondition (text-fits ("(ii)")))
 (postcondition (text-is REF))
 (priority 38)
 (defn "(ii)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R268
 (precondition (text-fits ("(iii)")))
 (postcondition (text-is REF))
 (priority 39)
 (defn "(iii)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R269
 (precondition (text-fits ("(iv)")))
 (postcondition (text-is REF))
 (priority 40)
 (defn "(iv)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R270
 (precondition (text-fits ("(v)")))
 (postcondition (text-is REF))
 (priority 41)
 (defn "(v)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R271
 (precondition (text-fits ("(a)")))
 (postcondition (text-is REF))
 (priority 42)
 (defn "(a)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R272
 (precondition (text-fits ("(b)")))
 (postcondition (text-is REF))
 (priority 43)
 (defn "(b)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R273
 (precondition (text-fits ("(c)")))
 (postcondition (text-is REF))
 (priority 44)
 (defn "(c)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R274
 (precondition (text-fits ("\\ref{" WORD "}")))
 (postcondition (text-is REF))
 (priority 45)
 (defn #'(LAMBDA (X) (LIST "\\ref{" X "}")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L275
 (precondition (text-fits ("(i)")))
 (postcondition (text-is LABEL))
 (priority 46)
 (defn "(i)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L276
 (precondition (text-fits ("(ii)")))
 (postcondition (text-is LABEL))
 (priority 47)
 (defn "(ii)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L277
 (precondition (text-fits ("(iii)")))
 (postcondition (text-is LABEL))
 (priority 48)
 (defn "(iii)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L278
 (precondition (text-fits ("(iv)")))
 (postcondition (text-is LABEL))
 (priority 49)
 (defn "(iv)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L279
 (precondition (text-fits ("(v)")))
 (postcondition (text-is LABEL))
 (priority 50)
 (defn "(v)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L280
 (precondition (text-fits ("(a)")))
 (postcondition (text-is LABEL))
 (priority 51)
 (defn "(a)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L281
 (precondition (text-fits ("(b)")))
 (postcondition (text-is LABEL))
 (priority 52)
 (defn "(b)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L282
 (precondition (text-fits ("(c)")))
 (postcondition (text-is LABEL))
 (priority 53)
 (defn "(c)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L283
 (precondition (text-fits ("\\label{" WORD "}")))
 (postcondition (text-is LABEL))
 (priority 54)
 (defn #'(LAMBDA (X) (LIST "\\label{" X "}")))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R284
 (precondition (text-fits (NATURAL1)))
 (postcondition (text-is REFNUM))
 (priority 55)
 (defn #'(LAMBDA (X) (FORMAT NIL "~d" X)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R285
 (precondition (text-fits (NATURAL1 REFNUM)))
 (postcondition (text-is REFNUM))
 (priority 56)
 (defn #'(LAMBDA (X Y) (FORMAT NIL "~d~d" X Y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R286
 (precondition (text-fits (NATURAL1 "." REFNUM)))
 (postcondition (text-is REFNUM))
 (priority 57)
 (defn #'(LAMBDA (X Y) (FORMAT NIL "~d.~d" X Y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H287
 (precondition (text-fits (HENCE WH "we" WH "either" WH "have" WH PROP1
                           WH "or" WH PROP1)))
 (postcondition (text-is PROOF1))
 (priority 58)
 (defn #'(LAMBDA (H W1 W2 W3 W4 P1 W5 W6 P2)
		 (format nil "clearly (~d | ~d)." P1 P2)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod CLEAR1
 (precondition (text-fits ("Clearly" WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 58)
 (defn #'(LAMBDA (W P)
		 (format nil "clearly ~d." P)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod CLEAR2
 (precondition (text-fits ("Clearly," WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 58)
 (defn #'(LAMBDA (W P)
		 (format nil "clearly ~d." P)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod CLEAR3
 (precondition (text-fits ("Also," WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 58)
 (defn #'(LAMBDA (W P)
		 (format nil "clearly ~d." P)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod CLEAR4
 (precondition (text-fits ("Also," WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 58)
 (defn #'(LAMBDA (W P)
		 (format nil "clearly ~d." P)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H288
 (precondition (text-fits (HENCE WH "we" WH "either" WH "have" WH LABEL
                           WH PROP "," WH "or" WH "we" WH "have" WH
                           LABEL WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 59)
 (defn #'(LAMBDA (H W1 W2 W3 W4 L1 W4A P1 W5 W5A W5B W6 L2 W6A P2)
		 (format nil "clearly (~d | ~d)." P1 P2)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H288a
 (precondition (text-fits (HENCE WH "we" WH "either" WH "have"
                           WH PROP "," WH "or" WH "we" WH "have" WH
                           PROP)))
 (postcondition (text-is PROOF1))
 (priority 59)
 (defn #'(LAMBDA (H W1 W2 W3 W4 P1 W5 W5A W5B W6 P2)
		 (format nil "clearly (~d | ~d)." P1 P2)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H288b
 (precondition (text-fits ("Either" 
                           WH PROP "," WH "or" WH 
                           PROP)))
 (postcondition (text-is PROOF1))
 (priority 59)
 (defn #'(LAMBDA (W1 P1 W5 W6 P2)
		 (format nil "clearly (~d | ~d)." P1 P2)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H289
 (precondition (text-fits (HENCE WH "either" WH LABEL WH PROP "," WH
                           "or" WH LABEL WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 60)
 (defn #'(LAMBDA (H W1 W2 L1 W3 P1 W4 W5 L2 W6 P2)
		 (format nil "clearly (~d | ~d)." P1 P2)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod PF
 (precondition (text-fits (NOTE WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 61)
 (always-try 2)
 (defn #'(LAMBDA (N W P)
		 (format nil "clearly ~d." p)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod PF290
 (precondition (text-fits (PROP)))
 (postcondition (text-is PROOF1))
 (priority 62)
 (always-try 2)
 (defn #'(LAMBDA (P)
		 (format nil "clearly ~d." P)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod PF291
 (precondition (text-fits (PROP)))
 (postcondition (text-is PROOF1))
 (priority 63)
 (always-try 2)
 (defn #'(LAMBDA (P)
		 (format nil "subgoal ~d." P)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod PF292
 (precondition (text-fits (PROP)))
 (postcondition (text-is PROOF1))
 (priority 64)
 (always-try 2)
 (defn #'(LAMBDA (P)
		 (format nil "assume ~d." P)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod N
 (precondition (text-fits ("Note")))
 (postcondition (text-is NOTE))
 (priority 65)
 (defn "Note")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod N293
 (precondition (text-fits ("Note that")))
 (postcondition (text-is NOTE))
 (priority 66)
 (defn "Note that")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod N294
 (precondition (text-fits ("note")))
 (postcondition (text-is NOTE))
 (priority 67)
 (defn "note")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod N295
 (precondition (text-fits ("note that")))
 (postcondition (text-is NOTE))
 (priority 68)
 (defn "note that")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P
 (precondition (text-fits ("We" WH SOMETIME WH VERIFY WH OBJ WH "is" WH
                           A WH ATTRIBUTION)))
 (postcondition (text-is PROOF1))
 (priority 69)
 (defn #'(LAMBDA (W1 S W2 V W3 O1 W4 W5 A W6 AA)
		 (format nil "subgoal (~d::~d)." O1 AA)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P296
 (precondition (text-fits ("We" WH VERIFY WH SOMETIME WH OBJ WH "is" WH
                           A WH ATTRIBUTION)))
 (postcondition (text-is PROOF1))
 (priority 70)
 (defn #'(LAMBDA (W1 V W2 S W3 O1 W4 W5 A W6 AA)
		 (format nil "subgoal (~d::~d)." O1 AA)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P297
 (precondition (text-fits ("We" WH VERIFY WH OBJ WH "is" WH A WH
                           ATTRIBUTION)))
 (postcondition (text-is PROOF1))
 (priority 71)
 (defn #'(LAMBDA (W1 V W2 O1 W4 W5 A W6 AA)
		 (format nil "subgoal (~d::~d)." O1 AA)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P298
 (precondition (text-fits ("We" WH VERIFY WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 72)
 (defn #'(LAMBDA (W1 V W2 P)
		 (format nil "subgoal (~d::~d)." O1 AA)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P299
 (precondition (text-fits ("We" WH SOMETIME WH VERIFY WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 73)
 (defn #'(LAMBDA (W1 S W2 V W3 P)
		 (format nil "subgoal ~d." P)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P300
 (precondition (text-fits ("We" WH VERIFY WH SOMETIME WH PROP)))
 (postcondition (text-is PROOF1))
 (priority 74)
 (defn #'(LAMBDA (W1 V W2 S W3 P)
		 (format nil "subgoal ~d." P)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod V
 (precondition (text-fits ("verify")))
 (postcondition (text-is VERIFY))
 (priority 75)
 (defn "verify")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod V301
 (precondition (text-fits ("check")))
 (postcondition (text-is VERIFY))
 (priority 76)
 (defn "check")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod V302
 (precondition (text-fits ("show")))
 (postcondition (text-is VERIFY))
 (priority 77)
 (defn "show")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod V303
 (precondition (text-fits ("prove")))
 (postcondition (text-is VERIFY))
 (priority 78)
 (defn "prove")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod V304
 (precondition (text-fits ("demonstrate")))
 (postcondition (text-is VERIFY))
 (priority 79)
 (defn "demonstrate")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod S
 (precondition (text-fits ("first")))
 (postcondition (text-is SOMETIME))
 (priority 80)
 (defn "first")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod S305
 (precondition (text-fits ("now")))
 (postcondition (text-is SOMETIME))
 (priority 81)
 (defn "now")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod S306
 (precondition (text-fits ("next")))
 (postcondition (text-is SOMETIME))
 (priority 82)
 (defn "next")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A307
 (precondition (text-fits ("element" WH "of" WH OBJ)))
 (postcondition (text-is ATTRIBUTION))
 (priority 83)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(in ~d)" Z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A310
 (precondition (text-fits ("set")))
 (postcondition (text-is ATTRIBUTION))
 (priority 86)
 (defn "set")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A311
 (precondition (text-fits ("function")))
 (postcondition (text-is ATTRIBUTION))
 (priority 87)
 (defn "(func _ _)")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A312
 (precondition (text-fits ("function" WH "from" WH OBJ WH "to" WH OBJ)))
 (postcondition (text-is ATTRIBUTION))
 (priority 88)
 (defn #'(LAMBDA (W1 W2 O1 W3 W4 O2)
		 (format nil "(func ~d ~d)" O1 O2)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P317
 (precondition (text-fits (OBJ WH "is" WH ADJ)))
 (postcondition (text-is PROP))
 (priority 93)
 (defn #'(LAMBDA (O W1 W2 A)
		 (format nil "(~d ~d)" A O)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P318
 (precondition (text-fits (OBJ WH "is" WH A WH ATTRIBUTION)))
 (postcondition (text-is PROP))
 (priority 94)
 (defn #'(LAMBDA (O W1 W2 A W3 A1)
		 (format nil "(~d ~d)" A1 O)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A319
 (precondition (text-fits ("infinite")))
 (postcondition (text-is ADJ))
 (priority 95)
 (defn "infinite")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A320
 (precondition (text-fits ("denumerable")))
 (postcondition (text-is ADJ))
 (priority 96)
 (defn "denumerable")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A321
 (precondition (text-fits ("functional")))
 (postcondition (text-is ADJ))
 (priority 97)
 (defn "functional")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A324
 (precondition (text-fits ("Any" WH "subset" WH "of" WH "the" WH "set"
                           WH "$N$" WH "of" WH "integers" WH "is" WH
                           ADJ WH "or" WH ADJ)))
 (postcondition (text-is PROP))
 (priority 100)
 (defn #'(LAMBDA (W1 W2 W3 W4 W5 WW1 WW2 W6 W7 A1 W8 W9 A2)
		 (format nil "(deudonneErrorProp ~d ~d)" A1 A2)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM
 (precondition (text-fits (MATHOBJ "\\inter" WH MATHOBJ)))
 (postcondition (text-is MATHOBJ))
 (priority 101)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d \\cap ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM325
 (precondition (text-fits (MATHOBJ WH "\\inter" WH MATHOBJ)))
 (postcondition (text-is MATHOBJ))
 (priority 102)
 (defn #'(LAMBDA (X W Y Z)
		 (format nil "(~d \\cap ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM326
 (precondition (text-fits ("(" MATHOBJ "\\inter" WH MATHOBJ ")")))
 (postcondition (text-is MATHOBJ))
 (priority 103)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d \\cap ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM327
 (precondition (text-fits ("(" MATHOBJ WH "\\inter" WH MATHOBJ ")")))
 (postcondition (text-is MATHOBJ))
 (priority 104)
 (defn #'(LAMBDA (X W Y Z)
		 (format nil "(~d \\cap ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM328
 (precondition (text-fits (MATHOBJ "\\union" WH MATHOBJ)))
 (postcondition (text-is MATHOBJ))
 (priority 105)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d \\cup ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM329
 (precondition (text-fits (MATHOBJ WH "\\union" WH MATHOBJ)))
 (postcondition (text-is MATHOBJ))
 (priority 106)
 (defn #'(LAMBDA (X W Y Z)
		 (format nil "(~d \\cup ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM330
 (precondition (text-fits ("(" MATHOBJ "\\union" WH MATHOBJ ")")))
 (postcondition (text-is MATHOBJ))
 (priority 107)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d \\cup ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYMT
 (precondition (text-fits (MATHOBJ "\\cap" WH MATHOBJ)))
 (postcondition (text-is MATHOBJ))
 (priority 101)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d \\cap ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM325T
 (precondition (text-fits (MATHOBJ WH "\\cap" WH MATHOBJ)))
 (postcondition (text-is MATHOBJ))
 (priority 102)
 (defn #'(LAMBDA (X W Y Z)
		 (format nil "(~d \\cap ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM326T
 (precondition (text-fits ("(" MATHOBJ "\\cap" WH MATHOBJ ")")))
 (postcondition (text-is MATHOBJ))
 (priority 103)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d \\cap ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM327T
 (precondition (text-fits ("(" MATHOBJ WH "\\cap" WH MATHOBJ ")")))
 (postcondition (text-is MATHOBJ))
 (priority 104)
 (defn #'(LAMBDA (X W Y Z)
		 (format nil "(~d \\cap ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM328T
 (precondition (text-fits (MATHOBJ "\\cup" WH MATHOBJ)))
 (postcondition (text-is MATHOBJ))
 (priority 105)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d \\cup ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM329T
 (precondition (text-fits (MATHOBJ WH "\\cup" WH MATHOBJ)))
 (postcondition (text-is MATHOBJ))
 (priority 106)
 (defn #'(LAMBDA (X W Y Z)
		 (format nil "(~d \\cup ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM330T
 (precondition (text-fits ("(" MATHOBJ "\\cup" WH MATHOBJ ")")))
 (postcondition (text-is MATHOBJ))
 (priority 107)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d \\cup ~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM331
 (precondition (text-fits (MATHOBJ "(" MATHOBJ ")")))
 (postcondition (text-is MATHOBJ))
 (priority 108)
 (defn #'(LAMBDA (X Y)
		 (format nil "(~d ~d)" x y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM332
 (precondition (text-fits (MATHOBJ "\\in" WH MATHOBJ)))
 (postcondition (text-is MATHPROP))
 (priority 109)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d::~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM333
 (precondition (text-fits (MATHOBJ "\\Metaeq" WH MATHOBJ)))
 (postcondition (text-is MATHPROP))
 (priority 110)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d==~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM334
 (precondition (text-fits (MATHOBJ "\\Metaeq" MATHOBJ)))
 (postcondition (text-is MATHPROP))
 (priority 111)
 (defn #'(LAMBDA (X Z)
		 (format nil "(~d==~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM335
 (precondition (text-fits (MATHOBJ "=" WH MATHOBJ)))
 (postcondition (text-is MATHPROP))
 (priority 112)
 (defn #'(LAMBDA (X Y Z)
		 (format nil "(~d==~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM336
 (precondition (text-fits (MATHOBJ "=" MATHOBJ)))
 (postcondition (text-is MATHPROP))
 (priority 113)
 (defn #'(LAMBDA (X Z)
		 (format nil "(~d==~d)" x z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod O2
 (precondition (text-fits ("$" MATHOBJ "$")))
 (postcondition (text-is OBJ))
 (priority 114)
 (defn #'(LAMBDA (X) X))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod O3
 (precondition (text-fits ("$$" MATHOBJ "$$")))
 (postcondition (text-is OBJ))
 (priority 115)
 (defn #'(LAMBDA (X) X))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod O4
 (precondition (text-fits (MATHVARIABLE)))
 (postcondition (text-is MATHOBJ))
 (priority 116)
 (defn #'(LAMBDA (X) (format nil "~d" X)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P2
 (precondition (text-fits (PROP1)))
 (postcondition (text-is PROP))
 (priority 117)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P2337
 (precondition (text-fits ("$" MATHPROP "$")))
 (postcondition (text-is PROP1))
 (priority 118)
 (defn #'(LAMBDA (X) X))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P3
 (precondition (text-fits ("$$" MATHPROP "$$")))
 (postcondition (text-is PROP1))
 (priority 119)
 (defn #'(LAMBDA (X) X))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod PA
 (precondition (text-fits (PROP1 WH "and" WH PROP1)))
 (postcondition (text-is PROP))
 (priority 120)
 (defn #'(LAMBDA (X Y Z W)
		 (format nil "(~d & ~d)" x w)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod PA338
 (precondition (text-fits (PROP1 "," WH "and" WH "either" WH PROP1 WH
                           "or" WH PROP1)))
 (postcondition (text-is PROP))
 (priority 121)
 (defn #'(LAMBDA (P1 W1 W2 W3 P2 W4 W5 P3)
		 (format nil "(~d & (~d | ~d))" p1 p2 p3)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod PA339
 (precondition (text-fits (PROP1 WH "or" WH PROP1)))
 (postcondition (text-is PROP))
 (priority 122)
 (defn #'(LAMBDA (X Y Z W)
		 (format nil "(~d | ~d)" x w)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod PA340
 (precondition (text-fits ("either" WH PROP1 WH "or" WH PROP1)))
 (postcondition (text-is PROP))
 (priority 123)
 (defn #'(LAMBDA (W1 X Y Z W)
		 (format nil "(~d | ~d)" x w)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod PA341
 (precondition (text-fits (OBJ WH "is" WH "a" WH "subset" WH "of" WH
                           OBJ)))
 (postcondition (text-is PROP))
 (priority 124)
 (defn #'(LAMBDA (X W1 W2 W3 W4 W5 Y)
		 (format nil "(~d <= ~d)" x y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod PA342
 (precondition (text-fits ("the" WH "sets" WH OBJ WH "and" WH OBJ WH
                           "are" WH "equal")))
 (postcondition (text-is PROP))
 (priority 125)
 (defn #'(LAMBDA (W1 W2 X W3 W4 Y W5 W6)
		 (format nil "(~d==~d)" x y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod WH
 (precondition (text-fits (WH1)))
 (postcondition (text-is WH))
 (priority 126)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod WH343
 (precondition (text-fits (WH1 WH)))
 (postcondition (text-is WH1))
 (priority 127)
 (defn #'(LAMBDA (X Y) (FORMAT NIL "~d~d" X Y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod WH344
 (precondition (text-fits (" ")))
 (postcondition (text-is WH1))
 (priority 128)
 (defn " ")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod WH345
 (precondition (text-fits (#\return)))
 (postcondition (text-is WH1))
 (priority 129)
 (defn #\return)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod WH346
 (precondition (text-fits (#\newline)))
 (postcondition (text-is WH1))
 (priority 130)
 (defn #\newline)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SYM347
 (precondition (text-fits ("$" MATHSYMBOL "$" WH)))
 (postcondition (text-is SYMBOL))
 (priority 131)
 (defn #'(LAMBDA (X Y) X))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod V1
 (precondition (text-fits ("$" MATHVARIABLE "$")))
 (postcondition (text-is VARIABLE))
 (priority 132)
 (defn #'(LAMBDA (X) X))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod V2
 (precondition (text-fits (WORD)))
 (postcondition (text-is MATHVARIABLE))
 (priority 133)
 (defn #'(LAMBDA (X) X))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod TEXT1
 (precondition (text-fits (TEXTUNIT)))
 (postcondition (text-is TEXT))
 (priority 134)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod TEXT2
 (precondition (text-fits (TEXTUNIT WH TEXT)))
 (postcondition (text-is TEXT))
 (priority 135)
 (defn #'(LAMBDA (X Y) (FORMAT NIL "~d ~d" X Y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod TEXT2348
 (precondition (text-fits (TEXT "," WH TEXT)))
 (postcondition (text-is TEXT))
 (priority 136)
 (defn #'(LAMBDA (X Y) (FORMAT NIL "~d, ~d" X Y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod TEXT2349
 (precondition (text-fits (TEXT ";" WH TEXT)))
 (postcondition (text-is TEXT))
 (priority 137)
 (defn #'(LAMBDA (X Y) (FORMAT NIL "~d; ~d" X Y)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod TEXT1350
 (precondition (text-fits (WORD)))
 (postcondition (text-is TEXTUNIT))
 (priority 138)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod TEXT1351
 (precondition (text-fits ("(" TEXT ")")))
 (postcondition (text-is TEXTUNIT))
 (priority 139)
 (defn #'(LAMBDA (X) (FORMAT NIL "(~d)" X)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod TEXT2352
 (precondition (text-fits ("\\textbf{" TEXT "}")))
 (postcondition (text-is TEXTUNIT))
 (priority 140)
 (defn #'(LAMBDA (X) (FORMAT NIL "\\textbf{~d}" X)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod TEXT2353
 (precondition (text-fits ("{\\em" WH TEXT "}")))
 (postcondition (text-is TEXTUNIT))
 (priority 141)
 (defn #'(LAMBDA (X) (FORMAT NIL "{\\em ~d}" X)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod TEXT1354
 (precondition (text-fits (INMATH MATH OUTMATH)))
 (postcondition (text-is TEXTUNIT))
 (priority 142)
 (defn #'(LAMBDA (X Y Z) (FORMAT NIL "~d~d~d" X Y Z)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod INMATH1
 (precondition (text-fits ("$")))
 (postcondition (text-is INMATH))
 (priority 143)
 (defn "$")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod INMATH2
 (precondition (text-fits ("$$")))
 (postcondition (text-is INMATH))
 (priority 144)
 (defn "$$")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod OUTMATH1
 (precondition (text-fits ("$")))
 (postcondition (text-is OUTMATH))
 (priority 145)
 (defn "$")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod OUTMATH2
 (precondition (text-fits ("$$")))
 (postcondition (text-is OUTMATH))
 (priority 146)
 (defn "$$")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod MATH1
 (precondition (text-fits (MATHSTRING)))
 (postcondition (text-is MATH))
 (priority 147)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod WORD1
 (precondition (text-fits (ALPHA1)))
 (postcondition (text-is WORD))
 (priority 148)
 (defn #'(LAMBDA (CH) (FORMAT NIL "~d" CH)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod WORD2
 (precondition (text-fits (ALPHA1 WORD)))
 (postcondition (text-is WORD))
 (priority 149)
 (defn #'(LAMBDA (CH STR) (FORMAT NIL "~d~d" CH STR)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod MATHSTRING1
 (precondition (text-fits NIL))
 (postcondition (text-is MATHSTRING))
 (priority 150)
 (defn "")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod MATHSTRING2
 (precondition (text-fits (MATHCHAR MATHSTRING)))
 (postcondition (text-is MATHSTRING))
 (priority 151)
 (defn #'(LAMBDA (CH STR) (FORMAT NIL "~d~d" CH STR)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod MATHCHAR1
 (precondition (text-fits (CHAR)))
 (postcondition (text-is MATHCHAR))
 (priority 152)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod MATHCHAR1355
 (precondition (text-fits (WH)))
 (postcondition (text-is MATHCHAR))
 (priority 153)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod MATHCHAR1356
 (precondition (text-fits ("^")))
 (postcondition (text-is MATHCHAR))
 (priority 154)
 (defn "^")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod MATHCHAR1357
 (precondition (text-fits ("_")))
 (postcondition (text-is MATHCHAR))
 (priority 155)
 (defn "_")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod GENSTRING1
 (precondition (text-fits NIL))
 (postcondition (text-is GENSTRING))
 (priority 156)
 (defn "")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod GENSTRING2
 (precondition (text-fits (GENCHAR GENSTRING)))
 (postcondition (text-is GENSTRING))
 (priority 157)
 (defn #'(LAMBDA (CH STR) (FORMAT NIL "~d~d" CH STR)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod GENCHAR1
 (precondition (text-fits (CHAR)))
 (postcondition (text-is GENCHAR))
 (priority 158)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod GENCHAR1358
 (precondition (text-fits ("$")))
 (postcondition (text-is GENCHAR))
 (priority 159)
 (defn "$")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod GENCHAR1359
 (precondition (text-fits (WH)))
 (postcondition (text-is GENCHAR))
 (priority 160)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod STRING1
 (precondition (text-fits NIL))
 (postcondition (text-is STRING))
 (priority 161)
 (defn "")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod STRING2
 (precondition (text-fits (CHAR STRING)))
 (postcondition (text-is STRING))
 (priority 162)
 (defn #'(LAMBDA (CH STR) (FORMAT NIL "~d~d" CH STR)))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod CHARESC
 (precondition (text-fits ("\\")))
 (postcondition (text-is CHAR))
 (priority 163)
 (defn #\\)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod CHARSPEC
 (precondition (text-fits (SPECHAR)))
 (postcondition (text-is CHAR))
 (priority 164)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod CHARNAT
 (precondition (text-fits (NATURAL1)))
 (postcondition (text-is CHAR))
 (priority 165)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod CHARALPHA
 (precondition (text-fits (ALPHA1)))
 (postcondition (text-is CHAR))
 (priority 166)
 (defn #'IDENTITY)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod CHAR123
 (precondition (text-fits ("{")))
 (postcondition (text-is CHAR))
 (priority 167)
 (defn #\{)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod CHAR125
 (precondition (text-fits ("}")))
 (postcondition (text-is CHAR))
 (priority 168)
 (defn #\})
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod a360
 (precondition (text-fits ("a")))
 (postcondition (text-is ALPHA1))
 (priority 169)
 (defn #\a)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod b361
 (precondition (text-fits ("b")))
 (postcondition (text-is ALPHA1))
 (priority 170)
 (defn #\b)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod c362
 (precondition (text-fits ("c")))
 (postcondition (text-is ALPHA1))
 (priority 171)
 (defn #\c)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod d363
 (precondition (text-fits ("d")))
 (postcondition (text-is ALPHA1))
 (priority 172)
 (defn #\d)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod e364
 (precondition (text-fits ("e")))
 (postcondition (text-is ALPHA1))
 (priority 173)
 (defn #\e)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod f365
 (precondition (text-fits ("f")))
 (postcondition (text-is ALPHA1))
 (priority 174)
 (defn #\f)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod g366
 (precondition (text-fits ("g")))
 (postcondition (text-is ALPHA1))
 (priority 175)
 (defn #\g)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod h367
 (precondition (text-fits ("h")))
 (postcondition (text-is ALPHA1))
 (priority 176)
 (defn #\h)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod i368
 (precondition (text-fits ("i")))
 (postcondition (text-is ALPHA1))
 (priority 177)
 (defn #\i)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod j369
 (precondition (text-fits ("j")))
 (postcondition (text-is ALPHA1))
 (priority 178)
 (defn #\j)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod k370
 (precondition (text-fits ("k")))
 (postcondition (text-is ALPHA1))
 (priority 179)
 (defn #\k)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod l371
 (precondition (text-fits ("l")))
 (postcondition (text-is ALPHA1))
 (priority 180)
 (defn #\l)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod m372
 (precondition (text-fits ("m")))
 (postcondition (text-is ALPHA1))
 (priority 181)
 (defn #\m)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod n373
 (precondition (text-fits ("n")))
 (postcondition (text-is ALPHA1))
 (priority 182)
 (defn #\n)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod o374
 (precondition (text-fits ("o")))
 (postcondition (text-is ALPHA1))
 (priority 183)
 (defn #\o)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod p375
 (precondition (text-fits ("p")))
 (postcondition (text-is ALPHA1))
 (priority 184)
 (defn #\p)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod q376
 (precondition (text-fits ("q")))
 (postcondition (text-is ALPHA1))
 (priority 185)
 (defn #\q)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod r377
 (precondition (text-fits ("r")))
 (postcondition (text-is ALPHA1))
 (priority 186)
 (defn #\r)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod s378
 (precondition (text-fits ("s")))
 (postcondition (text-is ALPHA1))
 (priority 187)
 (defn #\s)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod t379
 (precondition (text-fits ("t")))
 (postcondition (text-is ALPHA1))
 (priority 188)
 (defn #\t)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod u380
 (precondition (text-fits ("u")))
 (postcondition (text-is ALPHA1))
 (priority 189)
 (defn #\u)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod v381
 (precondition (text-fits ("v")))
 (postcondition (text-is ALPHA1))
 (priority 190)
 (defn #\v)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod w382
 (precondition (text-fits ("w")))
 (postcondition (text-is ALPHA1))
 (priority 191)
 (defn #\w)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod x383
 (precondition (text-fits ("x")))
 (postcondition (text-is ALPHA1))
 (priority 192)
 (defn #\x)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod y384
 (precondition (text-fits ("y")))
 (postcondition (text-is ALPHA1))
 (priority 193)
 (defn #\y)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod z385
 (precondition (text-fits ("z")))
 (postcondition (text-is ALPHA1))
 (priority 194)
 (defn #\z)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod A386
 (precondition (text-fits ("A")))
 (postcondition (text-is ALPHA1))
 (priority 195)
 (defn #\A)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod B387
 (precondition (text-fits ("B")))
 (postcondition (text-is ALPHA1))
 (priority 196)
 (defn #\B)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod C388
 (precondition (text-fits ("C")))
 (postcondition (text-is ALPHA1))
 (priority 197)
 (defn #\C)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod D389
 (precondition (text-fits ("D")))
 (postcondition (text-is ALPHA1))
 (priority 198)
 (defn #\D)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod E390
 (precondition (text-fits ("E")))
 (postcondition (text-is ALPHA1))
 (priority 199)
 (defn #\E)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod F391
 (precondition (text-fits ("F")))
 (postcondition (text-is ALPHA1))
 (priority 200)
 (defn #\F)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod G392
 (precondition (text-fits ("G")))
 (postcondition (text-is ALPHA1))
 (priority 201)
 (defn #\G)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod H393
 (precondition (text-fits ("H")))
 (postcondition (text-is ALPHA1))
 (priority 202)
 (defn #\H)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod I394
 (precondition (text-fits ("I")))
 (postcondition (text-is ALPHA1))
 (priority 203)
 (defn #\I)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod J395
 (precondition (text-fits ("J")))
 (postcondition (text-is ALPHA1))
 (priority 204)
 (defn #\J)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod K396
 (precondition (text-fits ("K")))
 (postcondition (text-is ALPHA1))
 (priority 205)
 (defn #\K)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod L397
 (precondition (text-fits ("L")))
 (postcondition (text-is ALPHA1))
 (priority 206)
 (defn #\L)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod M398
 (precondition (text-fits ("M")))
 (postcondition (text-is ALPHA1))
 (priority 207)
 (defn #\M)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod N399
 (precondition (text-fits ("N")))
 (postcondition (text-is ALPHA1))
 (priority 208)
 (defn #\N)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod O400
 (precondition (text-fits ("O")))
 (postcondition (text-is ALPHA1))
 (priority 209)
 (defn #\O)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod P401
 (precondition (text-fits ("P")))
 (postcondition (text-is ALPHA1))
 (priority 210)
 (defn #\P)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod Q402
 (precondition (text-fits ("Q")))
 (postcondition (text-is ALPHA1))
 (priority 211)
 (defn #\Q)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod R403
 (precondition (text-fits ("R")))
 (postcondition (text-is ALPHA1))
 (priority 212)
 (defn #\R)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod S404
 (precondition (text-fits ("S")))
 (postcondition (text-is ALPHA1))
 (priority 213)
 (defn #\S)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod T405
 (precondition (text-fits ("T")))
 (postcondition (text-is ALPHA1))
 (priority 214)
 (defn #\T)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod U406
 (precondition (text-fits ("U")))
 (postcondition (text-is ALPHA1))
 (priority 215)
 (defn #\U)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod V407
 (precondition (text-fits ("V")))
 (postcondition (text-is ALPHA1))
 (priority 216)
 (defn #\V)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod W408
 (precondition (text-fits ("W")))
 (postcondition (text-is ALPHA1))
 (priority 217)
 (defn #\W)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod X409
 (precondition (text-fits ("X")))
 (postcondition (text-is ALPHA1))
 (priority 218)
 (defn #\X)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod Y410
 (precondition (text-fits ("Y")))
 (postcondition (text-is ALPHA1))
 (priority 219)
 (defn #\Y)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod Z411
 (precondition (text-fits ("Z")))
 (postcondition (text-is ALPHA1))
 (priority 220)
 (defn #\Z)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod 0412
 (precondition (text-fits ("0")))
 (postcondition (text-is NATURAL1))
 (priority 221)
 (defn #\0)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod 1413
 (precondition (text-fits ("1")))
 (postcondition (text-is NATURAL1))
 (priority 222)
 (defn #\1)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod 2414
 (precondition (text-fits ("2")))
 (postcondition (text-is NATURAL1))
 (priority 223)
 (defn #\2)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod 3415
 (precondition (text-fits ("3")))
 (postcondition (text-is NATURAL1))
 (priority 224)
 (defn #\3)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod 4416
 (precondition (text-fits ("4")))
 (postcondition (text-is NATURAL1))
 (priority 225)
 (defn #\4)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod 5417
 (precondition (text-fits ("5")))
 (postcondition (text-is NATURAL1))
 (priority 226)
 (defn #\5)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod 6418
 (precondition (text-fits ("6")))
 (postcondition (text-is NATURAL1))
 (priority 227)
 (defn #\6)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod 7419
 (precondition (text-fits ("7")))
 (postcondition (text-is NATURAL1))
 (priority 228)
 (defn #\7)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod 8420
 (precondition (text-fits ("8")))
 (postcondition (text-is NATURAL1))
 (priority 229)
 (defn #\8)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod 9421
 (precondition (text-fits ("9")))
 (postcondition (text-is NATURAL1))
 (priority 230)
 (defn #\9)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR35
 (precondition (text-fits ("#")))
 (postcondition (text-is SPECHAR))
 (priority 231)
 (defn #\#)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR37
 (precondition (text-fits ("%")))
 (postcondition (text-is SPECHAR))
 (priority 232)
 (defn #\%)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR38
 (precondition (text-fits ("&")))
 (postcondition (text-is SPECHAR))
 (priority 233)
 (defn #\&)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR33
 (precondition (text-fits ("!")))
 (postcondition (text-is SPECHAR))
 (priority 234)
 (defn #\!)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR34
 (precondition (text-fits ("\"")))
 (postcondition (text-is SPECHAR))
 (priority 235)
 (defn #\")
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR39
 (precondition (text-fits ("'")))
 (postcondition (text-is SPECHAR))
 (priority 236)
 (defn #\')
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR40
 (precondition (text-fits ("(")))
 (postcondition (text-is SPECHAR))
 (priority 237)
 (defn #\()
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR41
 (precondition (text-fits (")")))
 (postcondition (text-is SPECHAR))
 (priority 238)
 (defn #\))
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR42
 (precondition (text-fits ("*")))
 (postcondition (text-is SPECHAR))
 (priority 239)
 (defn #\*)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR43
 (precondition (text-fits ("+")))
 (postcondition (text-is SPECHAR))
 (priority 240)
 (defn #\+)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR44
 (precondition (text-fits (",")))
 (postcondition (text-is SPECHAR))
 (priority 241)
 (defn #\,)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR45
 (precondition (text-fits ("-")))
 (postcondition (text-is SPECHAR))
 (priority 242)
 (defn #\-)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR46
 (precondition (text-fits (".")))
 (postcondition (text-is SPECHAR))
 (priority 243)
 (defn #\.)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR47
 (precondition (text-fits ("/")))
 (postcondition (text-is SPECHAR))
 (priority 244)
 (defn #\/)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR58
 (precondition (text-fits (":")))
 (postcondition (text-is SPECHAR))
 (priority 245)
 (defn #\:)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR59
 (precondition (text-fits (";")))
 (postcondition (text-is SPECHAR))
 (priority 246)
 (defn #\;)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR60
 (precondition (text-fits ("<")))
 (postcondition (text-is SPECHAR))
 (priority 247)
 (defn #\<)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR61
 (precondition (text-fits ("=")))
 (postcondition (text-is SPECHAR))
 (priority 248)
 (defn #\=)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR62
 (precondition (text-fits (">")))
 (postcondition (text-is SPECHAR))
 (priority 249)
 (defn #\>)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR63
 (precondition (text-fits ("?")))
 (postcondition (text-is SPECHAR))
 (priority 250)
 (defn #\?)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR64
 (precondition (text-fits ("@")))
 (postcondition (text-is SPECHAR))
 (priority 251)
 (defn #\@)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR91
 (precondition (text-fits ("[")))
 (postcondition (text-is SPECHAR))
 (priority 252)
 (defn #\[)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR93
 (precondition (text-fits ("]")))
 (postcondition (text-is SPECHAR))
 (priority 253)
 (defn #\])
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR96
 (precondition (text-fits ("`")))
 (postcondition (text-is SPECHAR))
 (priority 254)
 (defn #\`)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))

(scunakator~defmethod SPECHAR124
 (precondition (text-fits ("|")))
 (postcondition (text-is SPECHAR))
 (priority 255)
 (defn #\|)
 (help-msg "Scunakation Method for Scunakating Mathematical Text."))
