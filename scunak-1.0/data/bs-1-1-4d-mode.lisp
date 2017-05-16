(setq *justification-ref-assoc*
      '((|1.1.1| |setext| |setextsub|)))

(setq *tutor-auto-back* '(|setextsub|))

(setq *sig-granularity-perfect*
      '(|xmcases| |notE| |setext| |emptysetE| |setadjoinIL| |setadjoinIR|
 |setadjoinE| |powersetI| |powersetE| |setunionI| |setunionE| |univHas|
 |univAdj| |univPow| |univSU| |emptyinunitempty| |trueI| |notIp|
 |emptynotinempty| |falseE| |notI| |notfalse| |dnegE| |contradiction|
 |dnegI| |eqI| |symeq| |transeq| |symtrans1eq| |symtrans2eq|
 |uniqinunit| |eqinunit| |secondinupair| |prop2setI| |prop2setE|
 |prop2set2propI| |prop2set2propE| |prop2setI2| |prop2setE2| |orIL|
 |orIR| |orE| |excludedmiddle| |impI| |impE| |vacuousImpI|
 |trivialImpI| |contrapositive1| |contrapositive1a| |contrapositive2|
 |contrapositive2a| |contrapositive3| |contrapositive3a|
 |contrapositive4| |contrapositive4a| |andI| |andEL| |andER| |equivI|
 |equivE| |equivEimp1| |equivEimp2| |xorI1| |xorI2| |xorE| |equivAndE1|
 |equivAndE2| |equivAndE3| |equivOrE1| |equivOrE2| |setunionE2|
 |subsetI1| |subsetI2| |subsetRefl| |subsetE| |subsetE2| |subsetTrans|
 |notsubsetI| |notequalI1| |notequalI2| |setextsub| |eqimpsubset1|
 |eqimpsubset2| |setadjoinSub| |setadjoinOr| |powersetI1| |powersetE1|
 |emptysetimpfalse| |notinemptyset| |emptysetsubset|
 |subsetemptysetimpeq| |noeltsimpempty| |witnessnonempty| |upairsetIL|
 |upairsetIR| |upairsetE| |binunionIL| |binunionLsub| |binunionIR|
 |binunionRsub| |binunionE| |binintersectI| |binintersectEL|
 |binintersectER| |binintersectLsub| |binintersectRsub| |setminusI|
 |setminusEL| |setminusER| |setminusLsub| |setminusILneg|
 |setminusIRneg| |setminusERneg| |setminusELneg| |setoftrueEq|
 |nonemptyImpWitness| |symdiffI1| |symdiffI2| |symdiffE| |symdiffIneg1|
 |symdiffIneg2| |notinsingleton| |singletonsuniq| |singletonsswitch|
 |setunionsingleton1| |setunionsingleton2| |setunionsingleton|
 |theprop| |the| |binunionT_lem| |binunionT| |binintersectT_lem|
 |binintersectT| |powersetT_lem| |powersetT| |setminusT_lem|
 |setminusT| |complementT_lem| |complementT| |setextT| |subsetTI|
 |powersetTI| |powersetTE| |powersetTI1| |powersetTE1| |complementTI|
 |complementTE| |complementTI1| |complementTE1| |binintersectTEL|
 |binintersectTER| |binintersectTI| |binunionTE1| |binunionTE|
 |binunionTIL| |binunionTIR| |binintersectTELcontra|
 |binintersectTERcontra| |binunionTILcontra| |binunionTIRcontra|
 |binunionTEcontra| |demorgan1a| |demorgan2a| |demorgan2a1|
 |demorgan2a2| |demorgan1b| |demorgan2b2| |demorgan2b| |demorgan1|
 |demorgan2| |contrasubsetT| |contrasubsetT1| |contrasubsetT2|
 |contrasubsetT3| |doubleComplementI1| |doubleComplementE1|
 |doubleComplementSub1| |doubleComplementSub2| |doubleComplementEq|
 |binintersectTSub1| |binintersectTSub2| |binunionTSub1|
 |binunionTSub2| |complementTnotintersectT|
 |complementImpComplementIntersect|
 |complementSubsetComplementIntersect|
 |complementInPowersetComplementIntersect| |demorganCombo1|
 |inIntersectImpInUnion| |inIntersectImpInUnion2|
 |inIntersectImpInIntersectUnions| |intersectInPowersetIntersectUnions|
 |contraSubsetComplement| |complementTcontraSubset|
 |inComplementUnionImpNotIn1| |inComplementUnionImpInComplement1|
 |complementUnionInPowersetComplement| |upairequniteq| |setukpairinjL1|
 |setukpairinjL2| |setukpairinjR11| |setukpairinjR12| |setukpairinjR1|
 |setukpairinjR2| |setukpairIL| |setukpairIR| |kpairiskpair| |kpair|
 |setukpairinjL| |setukpairinjR| |kfstsingleton| |kfstpairEq|
 |ksndsingleton| |ksndpairEq| |kpairsurjEq| |powersetsubset|
 |singletonsubset| |singletoninpowerset| |singletoninpowunion|
 |upairsubunion| |upairinpowunion| |ubforcartprodlem1|
 |ubforcartprodlem2| |ubforcartprodlem3| |cartprodmempair1|
 |cartprodmempair| |cartprodmempairc| |cartprodpairmemEL|
 |cartprodpairmemER| |cartprodfstin| |cartprodfst| |cartprodsndin|
 |cartprodsnd| |cartprodpairin| |cartprodpair| |cartprodmempaircEq|
 |cartprodfstpairEq| |cartprodsndpairEq| |cartprodpairsurjEq|
 |subbreln| |eqbreln| |breln12breln| |subbreln1| |eqbreln1|
 |breln1invprop| |breln1inv| |breln1invI| |breln1invE| |breln1compprop|
 |breln1comp| |breln1compI| |breln1compE| |breln1compEex|
 |breln1unionprop| |breln1union| |breln1unionIL| |breln1unionIR|
 |breln1unionI| |breln1unionE| |breln1unionEcases| |funcImageSingleton|
 |apProp| |ap| |funcinfuncset| |infuncsetfunc| |ap2| |ap2apEq1|
 |ap2apEq2| |funcGraphProp1| |funcGraphProp2| |funcGraphProp3|
 |funcGraphProp4| |funcext| |funcext2| |eta1| |eta2|))

; simplified to be elts with pf types mentioning to subset, binunion or binintersect
; automatically generated
(setq *sig-granularity-perfect*
      '(|subset#F| |subset#U| |subsetI1| |subsetI2| |subsetRefl| |subsetE|
 |subsetE2| |subsetTrans| |notsubsetI| |notequalI1| |setextsub|
 |eqimpsubset1| |eqimpsubset2| |setadjoinSub| |powersetI1| |powersetE1|
 |emptysetsubset| |subsetemptysetimpeq| |binunion#F| |binunion#U|
 |binintersect#F| |binintersect#U| |binunionIL| |binunionLsub|
 |binunionIR| |binunionRsub| |binunionE| |binintersectI|
 |binintersectEL| |binintersectER| |binintersectLsub|
 |binintersectRsub| |setminusLsub| |regular#F| |regular#U| |symdiff#F|
 |symdiff#U| |setunionsingleton1| |setunionsingleton2| |binunionT_lem|
 |binunionT#F| |binunionT#U| |binintersectT_lem| |binintersectT#F|
 |binintersectT#U| |subsetTI| |powersetTI| |powersetTE| |contrasubsetT|
 |contrasubsetT1| |contrasubsetT2| |contrasubsetT3|
 |doubleComplementSub1| |doubleComplementSub2| |binintersectTSub1|
 |binintersectTSub2| |binunionTSub1| |binunionTSub2|
 |complementSubsetComplementIntersect| |contraSubsetComplement|
 |complementTcontraSubset| |powersetsubset| |singletonsubset|
 |singletoninpowunion| |upairsubunion| |upairinpowunion|
 |ubforcartprodlem1| |ubforcartprodlem2| |ubforcartprodlem3|
 |cartprod#F| |cartprod#U| |dpsetconstrSub| |breln#F| |breln#U|
 |subbreln| |subbreln1| |breln1unionprop| |breln1union#F|
 |breln1union#U|))

; simplified to be just what we need
(setq *sig-granularity-perfect*
      '(|subsetI1| |subsetI2| |binintersectER| |binintersectEL| |binintersectI| |binunionE| |binunionIL| |binunionIR|))

(setq *sig-granularity-toolow* nil)

(setq *sig-irrelevant* nil)

(setq *sig-granularity-toohigh* nil)

(setq *preunify-msv-goal* 2)
(setq *preunify-msv-hence* 1)
(setq *preunify-msv-supp* 1)

(setq *quick-fill-gap-simplify* 5)
(setq *scip-eager-elims* t)

(setq *scunak-time-limit* 60)

