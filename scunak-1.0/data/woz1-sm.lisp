(setq *quick-fill-gap-method* 'A) ; the old quick-fill-gap

(setq *quick-fill-gap-simplify* 5)

(setq *tutor-auto-back* '(|setextsub| |orE| |powersetTI|))

(setq *scip-eager-elims* t)

(setq *sig-granularity-perfect* '(|notE| |xmcases| |eqI| |notI|
|contradiction| |symeq| |transeq| |symtrans1eq| |symtrans2eq|
|binunionT| |binintersectT| |powersetT| |setminusT| |complementT|
|setextT| |subsetTI| |powersetTI| |powersetTE| |powersetTI1|
|powersetTE1| |complementTI| |complementTE| |complementTI1|
|complementTE1| |binintersectTEL| |binintersectTER| |binintersectTI|
|binunionTE1| |binunionTIL| |binunionTIR|
|binintersectTELcontra| |binintersectTERcontra| |binunionTILcontra|
|binunionTIRcontra| |binunionTEcontra| |demorgan1a| |demorgan2a|
|demorgan2a1| |demorgan2a2| |demorgan1b| |demorgan2b2| |demorgan2b|
|demorgan1| |demorgan2| |demorgan1Eq2| |demorgan2Eq2| |demorgan3Eq2|
|demorgan4Eq2| |contrasubsetT| |contrasubsetT1| |binintersectTSub1|
|binintersectTSub2| |binunionTSub1| |binunionTSub2| |impI| |impE|
|woz13rule1| |woz13rule2| |woz13rule3| |woz13rule4|
|woz14rule1| |woz14rule2| |woz14rule3| |subsetTrans|))

(setq *sig-irrelevant*
      '(|emptysetE| |setadjoinIL|
	|setadjoinIR| |powersetE| |setunionI| |univHas| |univAdj| |univPow|
	|univSU| |emptyinunitempty| |trueI| |emptynotinempty| |falseE|
	|notfalse| |dnegE| |dnegI| |uniqinunit| |eqinunit| |secondinupair|
	|prop2setI| |prop2setE| |prop2set2propI| |prop2set2propE| |prop2setI2|
	|prop2setE2| |vacuousImpI| |trivialImpI| |contrapositive1a|
	|contrapositive2a| |contrapositive3a| |contrapositive4a| |equivEimp1|
	|equivEimp2| |xorI1| |xorI2| |equivAndE1| |equivAndE2| |equivAndE3|
	|equivOrE1| |equivOrE2| |setunionE2| |subsetRefl| |subsetE| |subsetE2|
	|notsubsetI| |notequalI1| |notequalI2| |setextsub|
	|eqimpsubset1| |eqimpsubset2| |setadjoinSub| |setadjoinOr|
	|powersetI1| |powersetE1| |emptysetimpfalse| |notinemptyset|
	|emptysetsubset| |subsetemptysetimpeq| |witnessnonempty| |upairsetIL|
	|upairsetIR| |upairsetE| 
	|doubleComplementI1|
	|doubleComplementE1|
	|doubleComplementSub1|
	|doubleComplementSub2|
	|doubleComplementEq|
	))


(setq *sig-granularity-toohigh*
      '(|complementUnionInPowersetComplement|
	|inComplementUnionImpInComplement1| |inComplementUnionImpNotIn1|
	|complementTcontraSubset| |contraSubsetComplement|
	|intersectInPowersetIntersectUnions| |inIntersectImpInIntersectUnions|
	|inIntersectImpInUnion2| |inIntersectImpInUnion| |demorganCombo1|
	|complementInPowersetComplementIntersect|
	|complementSubsetComplementIntersect|
	|complementImpComplementIntersect| |complementTnotintersectT|
	|contrasubsetT2|
	|contrasubsetT3|
	))

(setq *sig-granularity-perfect* '(|notE| |xmcases| |eqI| |notI| |contradiction| |symeq| |transeq| |symtrans1eq| |symtrans2eq| |binunionT| |binintersectT| |powersetT| |setminusT| |complementT| |setextT| |subsetTI| |powersetTI| |powersetTE| |powersetTI1| |powersetTE1| |complementTI| |complementTE| |complementTI1| |complementTE1| |binintersectTEL| |binintersectTER| |binintersectTI| |binunionTE1| |binunionTE| |binunionTIL| |binunionTIR| |binintersectTELcontra| |binintersectTERcontra| |binunionTILcontra| |binunionTIRcontra| |binunionTEcontra| |demorgan1a| |demorgan2a| |demorgan2a1| |demorgan2a2| |demorgan1b| |demorgan2b2| |demorgan2b| |demorgan1| |demorgan2| |demorgan1Eq2| |demorgan2Eq2| |demorgan3Eq2| |demorgan4Eq2| |contrasubsetT| |contrasubsetT1| |binintersectTSub1| |binintersectTSub2| |binunionTSub1| |binunionTSub2| |impI| |impE| |woz13rule1| |woz13rule2| |woz13rule3| |doubleComplementSub1| |doubleComplementSub2| |doubleComplementEq| |subsetTrans|))

(setq *sig-granularity-toohigh*
      '(|woz13rule4|))

(setq *preunify-msv-goal* 1)
(setq *preunify-msv-hence* 1)
(setq *preunify-msv-supp* 1)
