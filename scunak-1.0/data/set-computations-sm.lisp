(setq *quick-fill-gap-method* 'A) ; the old quick-fill-gap

(setq *quick-fill-gap-simplify* nil)

;(setq *tutor-auto-back* '(|setextsub| |xmcases| |powersetTI| |binunionTE|))
(setq *tutor-auto-back* nil)
(setq *tutor-max-tasks* 6)

(setq *scip-eager-elims* nil)

(setq *sig-granularity-perfect* '(|notE| 
|contradiction| 
|setextsub| |subsetI1| |subsetI2| |setext|
|binunionIL| |binunionIR| |binunionE|
|binintersectEL| |binintersectER| |binintersectI|
|orE| |setadjoinIL| |setadjoinIR| |setadjoinE| |upairsetIR|
|symeq| |transeq| |boxeq|
))

(setq *sig-irrelevant* nil)

(setq *preunify-msv-goal* 1)
(setq *preunify-msv-hence* 1)
(setq *preunify-msv-supp* 1)
