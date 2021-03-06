; Author: Chad E Brown
; June 2006
; Testing Scunak on the basic set problems

(load "test-connect.lisp")

(defun bool-props-sets-test ()
  (send-a '(TUTOR-AUTO-BACK "setextsub"))
  (send-a '(TUTOR-STUDENT-USABLE "notE" "contradiction" "subsetI1" "subsetI2" "binintersectEL" "binintersectER" "binintersectI" "binunionIL" "binunionIR" "binunionE" "binunionCases" "emptysetsubset" "subsetemptysetimpeq"))
  (send-a '(LET "A" OBJ))
  (send-a '(LET "B" OBJ))
  (send-a '(LET "C" OBJ))
(send-a '(tutor ("unionComm" A B)))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunion" A B))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunion" B A))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("unionAssoc" A B C)))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunion" ("binunion" A B) C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunion" A B))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunion" A ("binunion" B C)))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("intersectComm" A B)))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" B A))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("intersectAssoc" A B C)))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" A ("binintersect" B C)))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersect" B C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersect" A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" ("binintersect" A B) C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersect" A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersect" B C))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("unionintersectDist1" A B C)))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunion" ("binintersect" A B) C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" ("binunion" A C) ("binunion" B C)))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersect" A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("unionintersectDist2" A B C)))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunion" A ("binintersect" B C)))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" B C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" ("binunion" A B) ("binunion" A C)))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersect" B C))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("intersectunionDist1" A B C)))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" ("binunion" A B) C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersect" A C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersect" B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunion" ("binintersect" A C) ("binintersect" B C)))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" B C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" A B))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("intersectunionDist2" A B C)))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" A ("binunion" B C)))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersect" A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersect" A C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" OBJ) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunion" ("binintersect" A B) ("binintersect" A C)))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersect" A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunion" B C))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))

 (send-a '(TUTOR-STUDENT-USABLE "notE" "contradiction" "subsetTI" "complementTI" "complementTE" "complementTI1" "complementTE1" "binintersectTEL" "binintersectTER" "binintersectTI" "binunionTIL" "binunionTIR" "emptysetsubset" "emptyInPowerset" "powersetI1" "powersetE1" "powersetI" "powersetTI" "binunionTE"))
  (send-a '(LET "U" OBJ))
  (send-a '(LET "A" ("powerset" "U")))
  (send-a '(LET "B" ("powerset" "U")))
  (send-a '(LET "C" ("powerset" "U")))
(send-a '(tutor ("unionTComm" U A B)))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunionT" U A B))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunionT" U B A))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("unionTAssoc" U A B C)))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunionT" U ("binunionT" U A B) C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunionT" U A B))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunionT" U A ("binunionT" U B C)))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("intersectTComm" U A B)))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U B A))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("intersectTAssoc" U A B C)))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U A ("binintersectT" U B C)))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersectT" U B C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersectT" U A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U ("binintersectT" U A B) C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersectT" U A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersectT" U B C))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("unionintersectTDist1" U A B C)))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunionT" U ("binintersectT" U A B) C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U ("binunionT" U A C) ("binunionT" U B C)))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersectT" U A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("unionintersectTDist2" U A B C)))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunionT" U A ("binintersectT" U B C)))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U B C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U ("binunionT" U A B) ("binunionT" U A C)))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersectT" U B C))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("intersectunionTDist1" U A B C)))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U ("binunionT" U A B) C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "A")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersectT" U A C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersectT" U B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunionT" U ("binintersectT" U A C) ("binintersectT" U B C)))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U B C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U A B))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("intersectunionTDist2" U A B C)))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U A ("binunionT" U B C)))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN "B")) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersectT" U A B))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binintersectT" U A C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binunionT" U ("binintersectT" U A B) ("binintersectT" U A C)))) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U A B))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN B)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U A C))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN C)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("binunionT" U B C))) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
(send-a '(tutor ("complementProp1" U A)))
(send-a '(CLEARLY ("emptyset" IN ("powerset" U))) '(OK) '(NOT-OK))
(send-a '(QED) '(OK) '(NOT-OK))
(send-a '(LET "x" "U") '(OK) '(NOT-OK))
(send-a '(ASSUME ("x" IN ("binintersectT" U A ("complementT" U A)))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN A)) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("x" IN ("complementT" U A))) '(OK) '(NOT-OK))
(send-a '(CLEARLY ("not" ("x" IN A))) '(OK) '(NOT-OK))
(send-a '(CLEARLY "false") '(OK) '(NOT-OK))
(send-a '(CLEARLY (("binintersectT" U A ("complementT" U A)) <= "emptyset")) '(OK) '(NOT-OK))
  (send-a '(QED) '(STUDENT-SUCCESSFUL EXIT-TUTOR) '(NOT-OK NOT-CORRECT STUDENT-FAILED))
  (scunak-disconnect)
)
(scunak-connect-acl "-k macu -p bool-props-sets-sm -f setrules.pam bool-props-sets.pam")
(bool-props-sets-test)
(scunak-connect-clisp "-k macu -p bool-props-sets-sm -f setrules.pam bool-props-sets.pam")
(bool-props-sets-test)

