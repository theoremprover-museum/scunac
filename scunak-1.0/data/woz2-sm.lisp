(setq *quick-fill-gap-method* 'A) ; the old quick-fill-gap

(setq *quick-fill-gap-simplify* 5)

(setq *tutor-auto-back* '(|setextsub| |orE|))

(setq *sig-granularity-perfect*
      '(|breln1invprop| |breln1inv| |breln1invI| |breln1invE| |breln1compprop|
	|breln1comp| |breln1compI| |breln1compE| |breln1unionprop|
	|breln1union| |breln1unionI| |breln1unionIL| |breln1unionIR|
	|breln1unionE| |breln1all| |subbreln1|
	|contradiction|
	|dexE|
	))

(setq *sig-granularity-perfect*
      '(|breln1invprop| |breln1inv| |breln1invI| |breln1invE| |breln1compprop| |breln1comp| |breln1compI| |breln1compE| |breln1unionprop| |breln1union| |breln1unionI| |breln1unionIL| |breln1unionIR| |breln1unionE| |breln1all| |subbreln1| |contradiction|))

(setq *sig-granularity-perfect-woz2A*
      '(|woz2W| |woz2Ex| |breln1invprop| |breln1inv| |breln1invI| |breln1invE| |breln1compprop| |breln1comp| |breln1compI| |breln1compE| |breln1unionprop| |breln1union| |breln1unionI| |breln1unionIL| |breln1unionIR| |breln1unionE| |breln1all| |subbreln1| |contradiction|))

(setq *sig-granularity-perfect-woz2B*
      '(|breln1unionCommutes| |woz2A| |woz2W| |woz2Ex| |breln1invprop| |breln1inv| |breln1invI| |breln1invE| |breln1compprop| |breln1comp| |breln1compI| |breln1compE| |breln1unionprop| |breln1union| |breln1unionI| |breln1unionIL| |breln1unionIR| |breln1unionE| |breln1all| |subbreln1| |contradiction|))


