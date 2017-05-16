(setq *quick-fill-gap-method* 'A) ; the old quick-fill-gap

(setq *quick-fill-gap-simplify* nil)

;(setq *tutor-auto-back* '(|setextsub| |xmcases| |powersetTI| |binunionTE|))
(setq *tutor-auto-back* '(|setextsub|))
(setq *tutor-max-tasks* 4)

(setq *scip-eager-elims* nil)

(setq *sig-granularity-perfect* '(|notE| 
|contradiction| 
|subsetTI| |complementTI| |complementTE| |complementTI1|
|complementTE1| |binintersectTEL| |binintersectTER| |binintersectTI|
|binunionTIL| |binunionTIR|

|emptysetsubset| |emptyInPowerset| |powersetI1| |powersetE1| |powersetI|

|powersetTI| |binunionTE|

))

(setq *sig-irrelevant* nil)

(setq *preunify-msv-goal* 1)
(setq *preunify-msv-hence* 1)
(setq *preunify-msv-supp* 1)
