(setq *tutor-auto-back* '(|setextsub| |binunionCases|))

; simplified to be just what we need
(setq *sig-granularity-perfect*
      '(|subsetI1| |subsetI2| |binintersectER| |binintersectEL| |binintersectI| |binunionE| |binunionIL| |binunionIR|))

(setq *sig-granularity-toolow* nil)

(setq *sig-irrelevant* nil)

(setq *sig-granularity-toohigh* nil)

(setq *preunify-msv-goal* 2)
(setq *preunify-msv-hence* 1)
(setq *preunify-msv-supp* 1)

(setq *quick-fill-gap-simplify* nil)
(setq *scip-eager-elims* t)


