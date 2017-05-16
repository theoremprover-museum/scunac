(setq *vampire-props* '(|not|))
(setq *vampire-allow-second* nil)

(newconst '|not| (dpi (prop) (prop)) '("Chad Edward Brown"))

(newconst '|xmcases| (dpi (prop) (dpi (prop) (dpi (dpi (pf '1) (pf '1)) (dpi (dpi (pf (app '|not| '2)) (pf '2)) (pf '2))))) '("Chad Edward Brown"))

(newconst '|notE| (dpi (prop) (dpi (prop) (dpi (pf '1) (dpi (pf (app '|not| '2)) (pf '2))))) '("Chad Edward Brown"))

(newconst '|eq| (dpi (obj) (dpi (obj) (prop))) '("Chad Edward Brown"))

(newconst '|eqCE| (dpi (dpi (obj) (prop)) (dpi (dclass '0) (dpi (dclass '1) (dpi (dpi (dclass '2) (prop)) (dpi (pf (app (app '|eq| (fst '2)) (fst '1))) (dpi (pf (app '1 '3)) (pf (app '2 '3)))))))) '("Chad Edward Brown"))

(newconst '|in| (dpi (obj) (dpi (obj) (prop))) '("Chad Edward Brown"))

(newconst '|setext| (dpi (obj) (dpi (obj) (dpi (dpi (obj) (dpi (pf (app (app '|in| '2) '0)) (pf (app (app '|in| '2) '1)))) (dpi (dpi (obj) (dpi (pf (app (app '|in| '2) '0)) (pf (app (app '|in| '4) '1)))) (pf (app (app '|eq| '3) '2)))))) '("Chad Edward Brown"))

(newconst '|emptyset| (obj) '("Chad Edward Brown"))

(newconst '|emptysetE| (dpi (obj) (dpi (pf (app (app '|in| '|emptyset|) '0)) (dpi (prop) (pf '0)))) '("Chad Edward Brown"))

(newconst '|dsetconstr| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (obj))) '("Chad Edward Brown"))

(newconst '|dsetconstrI| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (dclass (app '|in| '1)) (dpi (pf (app '1 '0)) (pf (app (app '|in| (app (app '|dsetconstr| '3) '2)) (fst '1))))))) '("Chad Edward Brown"))

(newconst '|dsetconstrEL| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|dsetconstr| '2) '1)) '0)) (pf (app (app '|in| '3) '1)))))) '("Chad Edward Brown"))

(newconst '|dsetconstrER| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|dsetconstr| '2) '1)) '0)) (pf (app '2 (pair '1 (app (app (app (app '|dsetconstrEL| '3) '2) '1) '0)))))))) '("Chad Edward Brown"))

(newconst '|setadjoin| (dpi (obj) (dpi (obj) (obj))) '("Chad Edward Brown"))

(newconst '|setadjoinIL| (dpi (obj) (dpi (obj) (pf (app (app '|in| (app (app '|setadjoin| '1) '0)) '1)))) '("Chad Edward Brown"))

(newconst '|setadjoinIR| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '1) '0)) (pf (app (app '|in| (app (app '|setadjoin| '3) '2)) '1)))))) '("Chad Edward Brown"))

(newconst '|setadjoinE| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|setadjoin| '2) '1)) '0)) (dpi (prop) (dpi (dpi (pf (app (app '|eq| '2) '4)) (pf '1)) (dpi (dpi (pf (app (app '|in| '4) '3)) (pf '2)) (pf '2)))))))) '("Chad Edward Brown"))

(newconst '|powerset| (dpi (obj) (obj)) '("Chad Edward Brown"))

(newconst '|powersetI| (dpi (obj) (dpi (obj) (dpi (dpi (obj) (dpi (pf (app (app '|in| '1) '0)) (pf (app (app '|in| '3) '1)))) (pf (app (app '|in| (app '|powerset| '2)) '1))))) '("Chad Edward Brown"))

(newconst '|powersetE| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app '|powerset| '2)) '1)) (dpi (pf (app (app '|in| '2) '1)) (pf (app (app '|in| '4) '2))))))) '("Chad Edward Brown"))

(newconst '|setunion| (dpi (obj) (obj)) '("Chad Edward Brown"))

(newconst '|setunionI| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '0) '1)) (dpi (pf (app (app '|in| '3) '1)) (pf (app (app '|in| (app '|setunion| '4)) '3))))))) '("Chad Edward Brown"))

(newconst '|setunionE| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app '|setunion| '1)) '0)) (dpi (prop) (dpi (dpi (obj) (dpi (pf (app (app '|in| '0) '3)) (dpi (pf (app (app '|in| '5) '1)) (pf '3)))) (pf '1)))))) '("Chad Edward Brown"))

(newconst '|univ| (dpi (obj) (obj)) '("Chad Edward Brown"))

(newconst '|univHas| (dpi (obj) (pf (app (app '|in| (app '|univ| '0)) '0))) '("Chad Edward Brown"))

(newconst '|univSep| (dpi (obj) (dpi (dclass (app '|in| (app '|univ| '0))) (dpi (dpi (dclass (app '|in| (fst '0))) (prop)) (pf (app (app '|in| (app '|univ| '2)) (app (app '|dsetconstr| (fst '1)) '0)))))) '("Chad Edward Brown"))

(newconst '|univAdj| (dpi (obj) (dpi (dclass (app '|in| (app '|univ| '0))) (dpi (dclass (app '|in| (app '|univ| '1))) (pf (app (app '|in| (app '|univ| '2)) (app (app '|setadjoin| (fst '1)) (fst '0))))))) '("Chad Edward Brown"))

(newconst '|univPow| (dpi (obj) (dpi (dclass (app '|in| (app '|univ| '0))) (pf (app (app '|in| (app '|univ| '1)) (app '|powerset| (fst '0)))))) '("Chad Edward Brown"))

(newconst '|univSU| (dpi (obj) (dpi (dclass (app '|in| (app '|univ| '0))) (pf (app (app '|in| (app '|univ| '1)) (app '|setunion| (fst '0)))))) '("Chad Edward Brown"))

(newabbrev '|emptyinunitempty| (pf (app (app '|in| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) '|emptyset|)) (app (app '|setadjoinIL| '|emptyset|) '|emptyset|) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|true| (prop) (app (app '|in| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) '|emptyset|) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|trueI| (pf '|true|) (app '|true#F| '|emptyinunitempty|) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|notIp| (dpi (prop) (dpi (dpi (pf '0) (dpi (prop) (pf '0))) (pf (app '|not| '1)))) (lam (lam (app (app (app (app '|xmcases| '1) (app '|not| '1)) (lam (app (app '1 '0) (app '|not| '2)))) (lam '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|emptynotinempty| (pf (app '|not| (app (app '|in| '|emptyset|) '|emptyset|))) (app (app '|notIp| (app (app '|in| '|emptyset|) '|emptyset|)) (app '|emptysetE| '|emptyset|)) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|false| (prop) (app (app '|in| '|emptyset|) '|emptyset|) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|falseE| (dpi (prop) (dpi (pf '|false|) (pf '1))) (lam (lam (app (app (app '|emptysetE| '|emptyset|) (app '|false#U| '0)) '1))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|notI| (dpi (prop) (dpi (dpi (pf '0) (pf '|false|)) (pf (app '|not| '1)))) (lam (lam (app (app '|notIp| '1) (lam (lam (app (app '|falseE| '0) (app '2 '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|notfalse| (pf (app '|not| '|false|)) (app (app '|notI| '|false|) (lam '0)) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dnegE| (dpi (prop) (dpi (pf (app '|not| (app '|not| '0))) (pf '1))) (lam (lam (app (app (app (app '|xmcases| '1) '1) (lam '0)) (lam (app (app (app (app '|notE| (app '|not| '2)) '2) '0) '1))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|contradiction| (dpi (prop) (dpi (dpi (pf (app '|not| '0)) (pf '|false|)) (pf '1))) (lam (lam (app (app (app (app '|xmcases| '1) '1) (lam '0)) (lam (app (app '|falseE| '2) (app '1 '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dnegI| (dpi (prop) (dpi (pf '0) (pf (app '|not| (app '|not| '1))))) (lam (lam (app (app '|notI| (app '|not| '1)) (app (app (app '|notE| '1) '|false|) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqE| (dpi (obj) (dpi (obj) (dpi (dpi (obj) (prop)) (dpi (pf (app (app '|eq| '2) '1)) (dpi (pf (app '1 '3)) (pf (app '2 '3))))))) (lam (lam (lam (app (app (app (app '|eqCE| (lam '|true|)) (pair '2 '|trueI|)) (pair '1 '|trueI|)) (lam (app '1 (fst '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqI| (dpi (obj) (pf (app (app '|eq| '0) '0))) (lam (app (app (app (app '|setext| '0) '0) (lam (lam '0))) (lam (lam '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|symeq| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| '1) '0)) (pf (app (app '|eq| '1) '2))))) (lam (lam (lam (app (app (app (app (app '|eqE| '2) '1) (lam (app (app '|eq| '0) '3))) '0) (app '|eqI| '2))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|transeq| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| '2) '1)) (dpi (pf (app (app '|eq| '2) '1)) (pf (app (app '|eq| '4) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app (app '|eqE| '3) '2) (app '|eq| '4)) '0) '1)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|symtrans1eq| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| '2) '1)) (dpi (pf (app (app '|eq| '1) '2)) (pf (app (app '|eq| '4) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app (app '|eqE| '3) '2) (app '|eq| '4)) (app (app (app '|symeq| '2) '3) '0)) '1)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|symtrans2eq| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| '2) '1)) (dpi (pf (app (app '|eq| '1) '2)) (pf (app (app '|eq| '2) '4))))))) (lam (lam (lam (lam (app (app (app (app '|eqE| '2) '3) (app '|eq| '1)) (app (app (app '|symeq| '3) '2) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqE2| (dpi (obj) (dpi (obj) (dpi (dpi (obj) (prop)) (dpi (pf (app (app '|eq| '2) '1)) (dpi (pf (app '1 '2)) (pf (app '2 '4))))))) (lam (lam (lam (lam (app (app (app (app '|eqE| '2) '3) '1) (app (app (app '|symeq| '3) '2) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqCE2| (dpi (dpi (obj) (prop)) (dpi (dclass '0) (dpi (dclass '1) (dpi (dpi (dclass '2) (prop)) (dpi (pf (app (app '|eq| (fst '2)) (fst '1))) (dpi (pf (app '1 '2)) (pf (app '2 '4)))))))) (lam (lam (lam (lam (lam (app (app (app (app (app '|eqCE| '4) '2) '3) '1) (app (app (app '|symeq| (fst '3)) (fst '2)) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqET| (dpi (obj) (dpi (dclass (app '|in| '0)) (dpi (dclass (app '|in| '1)) (dpi (pf (app (app '|eq| (fst '1)) (fst '0))) (dpi (dpi (dclass (app '|in| '3)) (prop)) (dpi (pf (app '0 '3)) (pf (app '1 '3)))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app '|dsetconstrER| '5) '1) (fst '3)) (app (app (app (app (app '|eqE| (fst '4)) (fst '3)) (app '|in| (app (app '|dsetconstr| '5) '1))) '2) (app (app (app (app '|dsetconstrI| '5) '1) '4) '0))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqET2| (dpi (obj) (dpi (dclass (app '|in| '0)) (dpi (dclass (app '|in| '1)) (dpi (pf (app (app '|eq| (fst '1)) (fst '0))) (dpi (dpi (dclass (app '|in| '3)) (prop)) (dpi (pf (app '0 '2)) (pf (app '1 '4)))))))) (lam (lam (lam (lam (app (app (app (app '|eqET| '3) '1) '2) (app (app (app '|symeq| (fst '2)) (fst '1)) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|uniqinunit| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|setadjoin| '0) '|emptyset|)) '1)) (pf (app (app '|eq| '2) '1))))) (lam (lam (lam (app (app (app (app (app (app (app '|setadjoinE| '1) '|emptyset|) '2) '0) (app (app '|eq| '2) '1)) (lam '0)) (lam (app (app (app '|emptysetE| '3) '0) (app (app '|eq| '3) '2))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqinunit| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| '1) '0)) (pf (app (app '|in| (app (app '|setadjoin| '1) '|emptyset|)) '2))))) (lam (lam (lam (app (app (app (app (app '|eqE2| '2) '1) (app '|in| (app (app '|setadjoin| '1) '|emptyset|))) '0) (app (app '|setadjoinIL| '1) '|emptyset|))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|secondinupair| (dpi (obj) (dpi (obj) (pf (app (app '|in| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '0)))) (lam (lam (app (app (app (app '|setadjoinIR| '1) (app (app '|setadjoin| '0) '|emptyset|)) '0) (app (app '|setadjoinIL| '0) '|emptyset|)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|prop2set| (dpi (prop) (obj)) (lam (app (app '|dsetconstr| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (lam '1))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|set2prop| (dpi (obj) (prop)) (lam (app (app '|in| '0) '|emptyset|)) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|prop2setI| (dpi (prop) (dpi (pf '0) (pf (app (app '|in| (app '|prop2set| '1)) '|emptyset|)))) (lam (lam (app (app (app '|prop2set#F| '1) (lam (app (app '|in| '0) '|emptyset|))) (app (app (app (app '|dsetconstrI| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (lam '2)) (pair '|emptyset| '|emptyinunitempty|)) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|prop2setE| (dpi (prop) (dpi (pf (app (app '|in| (app '|prop2set| '0)) '|emptyset|)) (pf '1))) (lam (lam (app (app (app (app '|dsetconstrER| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (lam '2)) '|emptyset|) (app (app (app '|prop2set#U| '1) (lam (app (app '|in| '0) '|emptyset|))) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|prop2set2propI| (dpi (prop) (dpi (pf '0) (pf (app '|set2prop| (app '|prop2set| '1))))) (lam (lam (app (app '|set2prop#F| (app '|prop2set| '1)) (app (app '|prop2setI| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|prop2set2propE| (dpi (prop) (dpi (pf (app '|set2prop| (app '|prop2set| '0))) (pf '1))) (lam (lam (app (app '|prop2setE| '1) (app (app '|set2prop#U| (app '|prop2set| '1)) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|prop2setI2| (dpi (prop) (dpi (pf '0) (pf (app (app '|eq| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (app '|prop2set| '1))))) (lam (lam (app (app (app (app '|setext| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (app '|prop2set| '1)) (lam (lam (app (app (app (app (app '|eqE2| '1) '|emptyset|) (app '|in| (app '|prop2set| '3))) (app (app (app '|uniqinunit| '1) '|emptyset|) '0)) (app (app '|prop2setI| '3) '2))))) (lam (lam (app (app (app (app '|dsetconstrEL| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (lam '4)) '1) (app (app (app '|prop2set#U| '3) (lam (app (app '|in| '0) '2))) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|prop2setE2| (dpi (prop) (dpi (pf (app (app '|eq| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (app '|prop2set| '0))) (pf '1))) (lam (lam (app (app '|prop2setE| '1) (app (app (app (app (app '|eqE| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (app '|prop2set| '1)) (lam (app (app '|in| '0) '|emptyset|))) '0) (app (app '|setadjoinIL| '|emptyset|) '|emptyset|))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|or| (dpi (prop) (dpi (prop) (prop))) (lam (lam (app (app '|in| (app (app '|setadjoin| (app '|prop2set| '1)) (app (app '|setadjoin| (app '|prop2set| '0)) '|emptyset|))) (app (app '|setadjoin| '|emptyset|) '|emptyset|)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|imp| (dpi (prop) (dpi (prop) (prop))) (lam (app '|or| (app '|not| '0))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|and| (dpi (prop) (dpi (prop) (prop))) (lam (lam (app '|not| (app (app '|imp| '1) (app '|not| '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|equiv| (dpi (prop) (dpi (prop) (prop))) (lam (lam (app (app '|and| (app (app '|imp| '1) '0)) (app (app '|imp| '0) '1)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|orIL| (dpi (prop) (dpi (prop) (dpi (pf '1) (pf (app (app '|or| '2) '1))))) (lam (lam (lam (app (app (app '|or#F| '2) '1) (app (app (app (app (app '|eqE2| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (app '|prop2set| '2)) (app '|in| (app (app '|setadjoin| (app '|prop2set| '2)) (app (app '|setadjoin| (app '|prop2set| '1)) '|emptyset|)))) (app (app '|prop2setI2| '2) '0)) (app (app '|setadjoinIL| (app '|prop2set| '2)) (app (app '|setadjoin| (app '|prop2set| '1)) '|emptyset|))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|orIR| (dpi (prop) (dpi (prop) (dpi (pf '0) (pf (app (app '|or| '2) '1))))) (lam (lam (lam (app (app (app '|or#F| '2) '1) (app (app (app (app (app '|eqE2| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (app '|prop2set| '1)) (app '|in| (app (app '|setadjoin| (app '|prop2set| '2)) (app (app '|setadjoin| (app '|prop2set| '1)) '|emptyset|)))) (app (app '|prop2setI2| '1) '0)) (app (app '|secondinupair| (app '|prop2set| '2)) (app '|prop2set| '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|orE| (dpi (prop) (dpi (prop) (dpi (pf (app (app '|or| '1) '0)) (dpi (prop) (dpi (dpi (pf '3) (pf '1)) (dpi (dpi (pf '3) (pf '2)) (pf '2))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app (app (app '|setadjoinE| (app '|prop2set| '5)) (app (app '|setadjoin| (app '|prop2set| '4)) '|emptyset|)) (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (app (app (app '|or#U| '5) '4) '3)) '2) (lam (app '2 (app (app '|prop2setE2| '6) '0)))) (lam (app '1 (app (app '|prop2setE2| '5) (app (app (app '|uniqinunit| (app (app '|setadjoin| '|emptyset|) '|emptyset|)) (app '|prop2set| '5)) '0))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|excludedmiddle| (dpi (prop) (pf (app (app '|or| '0) (app '|not| '0)))) (lam (app (app (app (app '|xmcases| '0) (app (app '|or| '0) (app '|not| '0))) (app (app '|orIL| '0) (app '|not| '0))) (app (app '|orIR| '0) (app '|not| '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|impI| (dpi (prop) (dpi (prop) (dpi (dpi (pf '1) (pf '1)) (pf (app (app '|imp| '2) '1))))) (lam (lam (lam (app (app (app '|imp#F| '2) '1) (app (app (app (app '|xmcases| '2) (app (app '|or| (app '|not| '2)) '1)) (lam (app (app (app '|orIR| (app '|not| '3)) '2) (app '1 '0)))) (app (app '|orIL| (app '|not| '2)) '1)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|impE| (dpi (prop) (dpi (prop) (dpi (pf (app (app '|imp| '1) '0)) (dpi (pf '2) (pf '2))))) (lam (lam (lam (lam (app (app (app (app (app (app '|orE| (app '|not| '3)) '2) (app (app (app '|imp#U| '3) '2) '1)) '2) (app (app (app '|notE| '3) '2) '0)) (lam '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|vacuousImpI| (dpi (prop) (dpi (prop) (dpi (pf (app '|not| '1)) (pf (app (app '|imp| '2) '1))))) (lam (lam (lam (app (app (app '|imp#F| '2) '1) (app (app (app '|orIL| (app '|not| '2)) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|trivialImpI| (dpi (prop) (dpi (prop) (dpi (pf '0) (pf (app (app '|imp| '2) '1))))) (lam (lam (lam (app (app (app '|imp#F| '2) '1) (app (app (app '|orIR| (app '|not| '2)) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|contrapositive1| (dpi (prop) (dpi (prop) (dpi (dpi (pf '1) (pf '1)) (dpi (pf (app '|not| '1)) (pf (app '|not| '3)))))) (lam (lam (lam (lam (app (app '|notI| '3) (lam (app (app (app (app '|notE| '3) '|false|) (app '2 '0)) '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|contrapositive1a| (dpi (prop) (dpi (prop) (dpi (pf (app (app '|imp| '1) '0)) (dpi (pf (app '|not| '1)) (pf (app '|not| '3)))))) (lam (lam (lam (app (app (app '|contrapositive1| '2) '1) (app (app (app '|impE| '2) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|contrapositive2| (dpi (prop) (dpi (prop) (dpi (dpi (pf (app '|not| '1)) (pf '1)) (dpi (pf (app '|not| '1)) (pf '3))))) (lam (lam (lam (lam (app (app '|contradiction| '3) (lam (app (app (app (app '|notE| '3) '|false|) (app '2 '0)) '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|contrapositive2a| (dpi (prop) (dpi (prop) (dpi (pf (app (app '|imp| (app '|not| '1)) '0)) (dpi (pf (app '|not| '1)) (pf '3))))) (lam (lam (lam (app (app (app '|contrapositive2| '2) '1) (app (app (app '|impE| (app '|not| '2)) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|contrapositive3| (dpi (prop) (dpi (prop) (dpi (dpi (pf (app '|not| '1)) (pf (app '|not| '1))) (dpi (pf '1) (pf '3))))) (lam (lam (lam (lam (app (app (app (app '|contrapositive2| '3) (app '|not| '2)) '1) (app (app '|dnegI| '2) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|contrapositive3a| (dpi (prop) (dpi (prop) (dpi (pf (app (app '|imp| (app '|not| '1)) (app '|not| '0))) (dpi (pf '1) (pf '3))))) (lam (lam (lam (lam (app (app (app (app '|contrapositive2a| '3) (app '|not| '2)) '1) (app (app '|dnegI| '2) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|contrapositive4| (dpi (prop) (dpi (prop) (dpi (dpi (pf '1) (pf (app '|not| '1))) (dpi (pf '1) (pf (app '|not| '3)))))) (lam (lam (lam (app (app (app '|contrapositive3| (app '|not| '2)) '1) (lam (app '1 (app (app '|dnegE| '3) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|contrapositive4a| (dpi (prop) (dpi (prop) (dpi (pf (app (app '|imp| '1) (app '|not| '0))) (dpi (pf '1) (pf (app '|not| '3)))))) (lam (lam (lam (app (app (app '|contrapositive4| '2) '1) (app (app (app '|impE| '2) (app '|not| '1)) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|andI| (dpi (prop) (dpi (prop) (dpi (pf '1) (dpi (pf '1) (pf (app (app '|and| '3) '2)))))) (lam (lam (lam (lam (app (app (app '|and#F| '3) '2) (app (app '|notI| (app (app '|imp| '3) (app '|not| '2))) (lam (app (app (app (app '|notE| '3) '|false|) '1) (app (app (app (app '|impE| '4) (app '|not| '3)) '0) '2))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|andEL| (dpi (prop) (dpi (prop) (dpi (pf (app (app '|and| '1) '0)) (pf '2)))) (lam (lam (lam (app (app '|contradiction| '2) (lam (app (app (app (app '|notE| (app (app '|imp| '3) (app '|not| '2))) '|false|) (app (app (app '|vacuousImpI| '3) (app '|not| '2)) '0)) (app (app (app '|and#U| '3) '2) '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|andER| (dpi (prop) (dpi (prop) (dpi (pf (app (app '|and| '1) '0)) (pf '1)))) (lam (lam (lam (app (app '|contradiction| '1) (lam (app (app (app (app '|notE| (app (app '|imp| '3) (app '|not| '2))) '|false|) (app (app (app '|trivialImpI| '3) (app '|not| '2)) '0)) (app (app (app '|and#U| '3) '2) '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|equivI| (dpi (prop) (dpi (prop) (dpi (dpi (pf '1) (pf '1)) (dpi (dpi (pf '1) (pf '3)) (pf (app (app '|equiv| '3) '2)))))) (lam (lam (lam (lam (app (app (app '|equiv#F| '3) '2) (app (app (app (app '|andI| (app (app '|imp| '3) '2)) (app (app '|imp| '2) '3)) (app (app (app '|impI| '3) '2) '1)) (app (app (app '|impI| '2) '3) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|equivE| (dpi (prop) (dpi (prop) (dpi (prop) (dpi (pf (app (app '|equiv| '2) '1)) (dpi (dpi (pf '3) (dpi (pf '3) (pf '3))) (dpi (dpi (pf (app '|not| '4)) (dpi (pf (app '|not| '4)) (pf '4))) (pf '3))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app (app '|orE| '5) (app '|not| '5)) (app '|excludedmiddle| '5)) '3) (lam (app (app (app (app (app (app '|orE| '5) (app '|not| '5)) (app '|excludedmiddle| '5)) '4) (app '2 '0)) (lam (app (app '3 '1) (app (app (app (app '|impE| '7) '6) (app (app (app '|andEL| (app (app '|imp| '7) '6)) (app (app '|imp| '6) '7)) (app (app (app '|equiv#U| '7) '6) '4))) '1)))))) (lam (app (app (app (app (app (app '|orE| '5) (app '|not| '5)) (app '|excludedmiddle| '5)) '4) (lam (app (app '3 (app (app (app (app '|impE| '6) '7) (app (app (app '|andER| (app (app '|imp| '7) '6)) (app (app '|imp| '6) '7)) (app (app (app '|equiv#U| '7) '6) '4))) '0)) '0))) (app '1 '0)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|equivEimp1| (dpi (prop) (dpi (prop) (dpi (pf (app (app '|equiv| '1) '0)) (dpi (pf '2) (pf '2))))) (lam (lam (lam (lam (app (app (app (app (app (app '|equivE| '3) '2) '2) '1) (lam (lam '0))) (lam (lam (app (app (app (app '|notE| '5) '4) '2) '1)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|equivEimp2| (dpi (prop) (dpi (prop) (dpi (pf (app (app '|equiv| '1) '0)) (dpi (pf '1) (pf '3))))) (lam (lam (lam (lam (app (app (app (app (app (app '|equivE| '3) '2) '3) '1) (lam (lam '1))) (lam (app (app (app '|notE| '3) '4) '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|xor| (dpi (prop) (dpi (prop) (prop))) (lam (lam (app '|not| (app (app '|equiv| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|xorI1| (dpi (prop) (dpi (prop) (dpi (pf '1) (dpi (pf (app '|not| '1)) (pf (app (app '|xor| '3) '2)))))) (lam (lam (lam (lam (app (app (app '|xor#F| '3) '2) (app (app '|notI| (app (app '|equiv| '3) '2)) (lam (app (app (app (app (app (app '|equivE| '4) '3) '|false|) '0) (lam (lam (app (app (app (app '|notE| '5) '|false|) '0) '3)))) (lam (lam (app (app (app (app '|notE| '6) '|false|) '4) '1))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|xorI2| (dpi (prop) (dpi (prop) (dpi (pf (app '|not| '1)) (dpi (pf '1) (pf (app (app '|xor| '3) '2)))))) (lam (lam (lam (lam (app (app (app '|xor#F| '3) '2) (app (app '|notI| (app (app '|equiv| '3) '2)) (lam (app (app (app (app (app (app '|equivE| '4) '3) '|false|) '0) (lam (lam (app (app (app (app '|notE| '6) '|false|) '1) '4)))) (lam (app (app (app '|notE| '4) '|false|) '2)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|xorE| (dpi (prop) (dpi (prop) (dpi (prop) (dpi (pf (app (app '|xor| '2) '1)) (dpi (dpi (pf '3) (dpi (pf (app '|not| '3)) (pf '3))) (dpi (dpi (pf (app '|not| '4)) (dpi (pf '4) (pf '4))) (pf '3))))))) (lam (lam (lam (lam (lam (lam (app (app '|contradiction| '3) (lam (app (app (app (app '|notE| (app (app '|equiv| '6) '5)) '|false|) (app (app (app (app '|equivI| '6) '5) (lam (app (app '|contradiction| '6) (lam (app (app (app (app '|notE| '6) '|false|) (app (app '4 '1) '0)) '2))))) (lam (app (app '|contradiction| '7) (lam (app (app (app (app '|notE| '6) '|false|) (app (app '3 '0) '1)) '2)))))) (app (app (app '|xor#U| '6) '5) '3)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|equivAndE1| (dpi (prop) (dpi (prop) (dpi (prop) (dpi (pf (app (app '|equiv| '2) (app (app '|and| '1) '0))) (dpi (pf '3) (pf '3)))))) (lam (lam (lam (lam (lam (app (app (app '|andEL| '3) '2) (app (app (app (app '|equivEimp1| '4) (app (app '|and| '3) '2)) '1) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|equivAndE2| (dpi (prop) (dpi (prop) (dpi (prop) (dpi (pf (app (app '|equiv| '2) (app (app '|and| '1) '0))) (dpi (pf '3) (pf '2)))))) (lam (lam (lam (lam (lam (app (app (app '|andER| '3) '2) (app (app (app (app '|equivEimp1| '4) (app (app '|and| '3) '2)) '1) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|equivAndE3| (dpi (prop) (dpi (prop) (dpi (prop) (dpi (pf (app (app '|equiv| '2) (app (app '|and| '1) '0))) (dpi (pf '2) (dpi (pf '2) (pf '5))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app '|equivEimp2| '5) (app (app '|and| '4) '3)) '2) (app (app (app (app '|andI| '4) '3) '1) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|equivOrE1| (dpi (prop) (dpi (prop) (dpi (prop) (dpi (pf (app (app '|equiv| '2) (app (app '|or| '1) '0))) (dpi (pf '2) (pf '4)))))) (lam (lam (lam (lam (lam (app (app (app (app '|equivEimp2| '4) (app (app '|or| '3) '2)) '1) (app (app (app '|orIL| '3) '2) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|equivOrE2| (dpi (prop) (dpi (prop) (dpi (prop) (dpi (pf (app (app '|equiv| '2) (app (app '|or| '1) '0))) (dpi (pf '1) (pf '4)))))) (lam (lam (lam (lam (lam (app (app (app (app '|equivEimp2| '4) (app (app '|or| '3) '2)) '1) (app (app (app '|orIR| '3) '2) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dall| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (prop))) (lam (lam (app (app '|eq| (app (app '|dsetconstr| '1) '0)) '1))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dex| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (prop))) (lam (lam (app '|not| (app (app '|eq| (app (app '|dsetconstr| '1) '0)) '|emptyset|)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dallI| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (dpi (dclass (app '|in| '1)) (pf (app '1 '0))) (pf (app (app '|dall| '2) '1))))) (lam (lam (lam (app (app (app '|dall#F| '2) '1) (app (app (app (app '|setext| (app (app '|dsetconstr| '2) '1)) '2) (app (app '|dsetconstrEL| '2) '1)) (lam (lam (app (app (app (app '|dsetconstrI| '4) '3) (pair '1 '0)) (app '2 (pair '1 '0)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dallE| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (pf (app (app '|dall| '1) '0)) (dpi (dclass (app '|in| '2)) (pf (app '2 '0)))))) (lam (lam (lam (lam (app (app (app (app '|dsetconstrER| '3) '2) (fst '0)) (app (app (app (app (app '|eqE2| (app (app '|dsetconstr| '3) '2)) '3) (lam (app (app '|in| '0) (fst '1)))) (app (app (app '|dall#U| '3) '2) '1)) (snd '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dexI| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (dclass (app '|in| '1)) (dpi (pf (app '1 '0)) (pf (app (app '|dex| '3) '2)))))) (lam (lam (lam (lam (app (app (app '|dex#F| '3) '2) (app (app '|notI| (app (app '|eq| (app (app '|dsetconstr| '3) '2)) '|emptyset|)) (lam (app (app (app '|emptysetE| (fst '2)) (app (app (app (app (app '|eqE| (app (app '|dsetconstr| '4) '3)) '|emptyset|) (lam (app (app '|in| '0) (fst '3)))) '0) (app (app (app (app '|dsetconstrI| '4) '3) '2) '1))) '|false|)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dexE| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (pf (app (app '|dex| '1) '0)) (dpi (prop) (dpi (dpi (dclass (app '|in| '3)) (dpi (pf (app '3 '0)) (pf '2))) (pf '1)))))) (lam (lam (lam (lam (lam (app (app (app (app '|contrapositive2| '1) (app (app '|eq| (app (app '|dsetconstr| '4) '3)) '|emptyset|)) (lam (app (app (app (app '|setext| (app (app '|dsetconstr| '5) '4)) '|emptyset|) (lam (lam (app (app (app (app '|notE| '4) (app (app '|in| '|emptyset|) '1)) (app (app '3 (pair '1 (app (app (app (app '|dsetconstrEL| '7) '6) '1) '0))) (app (app (app (app '|dsetconstrER| '7) '6) '1) '0))) '2)))) (lam (lam (app (app (app '|emptysetE| '1) '0) (app (app '|in| (app (app '|dsetconstr| '7) '6)) '1))))))) (app (app (app '|dex#U| '4) '3) '2))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setunionE2| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app '|setunion| '1)) '0)) (pf (app (app '|dex| '2) (lam (app (app '|in| (fst '0)) '2))))))) (lam (lam (lam (app (app (app (app (app '|setunionE| '2) '1) '0) (app (app '|dex| '2) (lam (app (app '|in| (fst '0)) '2)))) (lam (lam (lam (app (app (app (app '|dexI| '5) (lam (app (app '|in| (fst '0)) '5))) (pair '2 '0)) '1)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|subset| (dpi (obj) (dpi (obj) (prop))) (lam (lam (app (app '|dall| '1) (lam (app (app '|in| '1) (fst '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|subsetI1| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (pf (app (app '|in| '1) (fst '0)))) (pf (app (app '|subset| '2) '1))))) (lam (lam (lam (app (app (app '|subset#F| '2) '1) (app (app (app '|dallI| '2) (lam (app (app '|in| '2) (fst '0)))) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|subsetI2| (dpi (obj) (dpi (obj) (dpi (dpi (obj) (dpi (pf (app (app '|in| '2) '0)) (pf (app (app '|in| '2) '1)))) (pf (app (app '|subset| '2) '1))))) (lam (lam (lam (app (app (app '|subsetI1| '2) '1) (lam (app (app '1 (fst '0)) (snd '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|subsetRefl| (dpi (obj) (pf (app (app '|subset| '0) '0))) (lam (app (app (app '|subsetI2| '0) '0) (lam (lam '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|subsetE| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|subset| '2) '1)) (dpi (pf (app (app '|in| '3) '1)) (pf (app (app '|in| '3) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app '|dallE| '4) (lam (app (app '|in| '4) (fst '0)))) (app (app (app '|subset#U| '4) '3) '1)) (pair '2 '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|subsetE2| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|subset| '2) '1)) (dpi (pf (app '|not| (app (app '|in| '2) '1))) (pf (app '|not| (app (app '|in| '4) '2)))))))) (lam (lam (lam (lam (app (app (app '|contrapositive1| (app (app '|in| '3) '1)) (app (app '|in| '2) '1)) (app (app (app (app '|subsetE| '3) '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|subsetTrans| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|subset| '2) '1)) (dpi (pf (app (app '|subset| '2) '1)) (pf (app (app '|subset| '4) '2))))))) (lam (lam (lam (lam (lam (app (app (app '|subsetI2| '4) '2) (lam (lam (app (app (app (app (app '|subsetE| '5) '4) '1) '2) (app (app (app (app (app '|subsetE| '6) '5) '1) '3) '0)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|notsubsetI| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '2) '0)) (dpi (pf (app '|not| (app (app '|in| '2) '1))) (pf (app '|not| (app (app '|subset| '4) '3)))))))) (lam (lam (lam (lam (app (app (app '|contrapositive1| (app (app '|subset| '3) '2)) (app (app '|in| '2) '1)) (lam (app (app (app (app (app '|subsetE| '4) '3) '2) '0) '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|notequalI1| (dpi (obj) (dpi (obj) (dpi (pf (app '|not| (app (app '|subset| '1) '0))) (pf (app '|not| (app (app '|eq| '2) '1)))))) (lam (lam (app (app (app '|contrapositive1| (app (app '|eq| '1) '0)) (app (app '|subset| '1) '0)) (lam (app (app (app (app (app '|eqE| '2) '1) (app '|subset| '2)) '0) (app (app (app '|subsetI2| '2) '2) (lam (lam '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|notequalI2| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '2) '0)) (dpi (pf (app '|not| (app (app '|in| '2) '1))) (pf (app '|not| (app (app '|eq| '4) '3)))))))) (lam (lam (lam (lam (lam (app (app (app '|notequalI1| '4) '3) (app (app (app (app (app '|notsubsetI| '4) '3) '2) '1) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setextsub| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|subset| '1) '0)) (dpi (pf (app (app '|subset| '1) '2)) (pf (app (app '|eq| '3) '2)))))) (lam (lam (lam (lam (app (app (app (app '|setext| '3) '2) (lam (app (app (app (app '|subsetE| '4) '3) '0) '2))) (lam (app (app (app (app '|subsetE| '3) '4) '0) '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqimpsubset1| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| '1) '0)) (pf (app (app '|subset| '2) '1))))) (lam (lam (lam (app (app (app (app (app '|eqE| '2) '1) (app '|subset| '2)) '0) (app (app (app '|subsetI1| '2) '2) (lam (snd '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqimpsubset2| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| '1) '0)) (pf (app (app '|subset| '1) '2))))) (lam (lam (lam (app (app (app (app (app '|eqE| '2) '1) (lam (app (app '|subset| '0) '3))) '0) (app (app (app '|subsetI1| '2) '2) (lam (snd '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setadjoinSub| (dpi (obj) (dpi (obj) (pf (app (app '|subset| '0) (app (app '|setadjoin| '1) '0))))) (lam (lam (app (app (app '|subsetI1| '0) (app (app '|setadjoin| '1) '0)) (lam (app (app (app (app '|setadjoinIR| '2) '1) (fst '0)) (snd '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setadjoinOr| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|setadjoin| '2) '1)) '0)) (pf (app (app '|or| (app (app '|eq| '1) '3)) (app (app '|in| '2) '1))))))) (lam (lam (lam (lam (app (app (app (app (app (app (app '|setadjoinE| '3) '2) '1) '0) (app (app '|or| (app (app '|eq| '1) '3)) (app (app '|in| '2) '1))) (app (app '|orIL| (app (app '|eq| '1) '3)) (app (app '|in| '2) '1))) (app (app '|orIR| (app (app '|eq| '1) '3)) (app (app '|in| '2) '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|powersetI1| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|subset| '0) '1)) (pf (app (app '|in| (app '|powerset| '2)) '1))))) (lam (lam (lam (app (app (app '|powersetI| '2) '1) (lam (app (app (app (app '|subsetE| '2) '3) '0) '1)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|powersetE1| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app '|powerset| '1)) '0)) (pf (app (app '|subset| '1) '2))))) (lam (lam (lam (app (app (app '|subsetI1| '1) '2) (lam (app (app (app (app (app '|powersetE| '3) '2) (fst '0)) '1) (snd '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|emptysetimpfalse| (dpi (obj) (dpi (pf (app (app '|in| '|emptyset|) '0)) (pf '|false|))) (lam (lam (app (app (app '|emptysetE| '1) '0) '|false|))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|emptyE1| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (pf (app (app '|dex| '1) '0)) (dpi (pf (app (app '|eq| (app (app '|dsetconstr| '2) '1)) '|emptyset|)) (pf '|false|))))) (lam (lam (lam (lam (app (app (app (app (app '|dexE| '3) '2) '1) '|false|) (lam (lam (app (app (app '|emptysetE| (fst '1)) (app (app (app (app (app '|eqE| (app (app '|dsetconstr| '5) '4)) '|emptyset|) (lam (app (app '|in| '0) (fst '2)))) '2) (app (app (app (app '|dsetconstrI| '5) '4) '1) '0))) '|false|)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|notinemptyset| (dpi (obj) (pf (app '|not| (app (app '|in| '|emptyset|) '0)))) (lam (app (app '|notI| (app (app '|in| '|emptyset|) '0)) (lam (app (app (app '|emptysetE| '1) '0) '|false|)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|emptysetsubset| (dpi (obj) (pf (app (app '|subset| '|emptyset|) '0))) (lam (app (app (app '|subsetI2| '|emptyset|) '0) (lam (lam (app (app '|falseE| (app (app '|in| '2) '1)) (app (app '|emptysetimpfalse| '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|subsetemptysetimpeq| (dpi (obj) (dpi (pf (app (app '|subset| '0) '|emptyset|)) (pf (app (app '|eq| '1) '|emptyset|)))) (lam (lam (app (app (app (app '|setextsub| '1) '|emptyset|) '0) (app '|emptysetsubset| '1)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|noeltsimpempty| (dpi (obj) (dpi (dpi (obj) (pf (app '|not| (app (app '|in| '1) '0)))) (pf (app (app '|eq| '1) '|emptyset|)))) (lam (lam (app (app '|subsetemptysetimpeq| '1) (app (app (app '|subsetI1| '1) '|emptyset|) (lam (app (app (app (app '|notE| (app (app '|in| '2) (fst '0))) (app (app '|in| '|emptyset|) (fst '0))) (snd '0)) (app '1 (fst '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|nonempty| (dpi (obj) (prop)) (lam (app '|not| (app (app '|eq| '0) '|emptyset|))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|witnessnonempty| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '1) '0)) (pf (app '|nonempty| '2))))) (lam (lam (lam (app (app '|nonempty#F| '2) (app (app (app (app (app '|notequalI2| '2) '|emptyset|) '1) '0) (app '|notinemptyset| '1)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|upairsetIL| (dpi (obj) (dpi (obj) (pf (app (app '|in| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '1)))) (lam (lam (app (app '|setadjoinIL| '1) (app (app '|setadjoin| '0) '|emptyset|)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|upairsetIR| (dpi (obj) (dpi (obj) (pf (app (app '|in| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '0)))) (lam (lam (app (app (app (app '|setadjoinIR| '1) (app (app '|setadjoin| '0) '|emptyset|)) '0) (app (app '|setadjoinIL| '0) '|emptyset|)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|upairsetE| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) '0)) (pf (app (app '|or| (app (app '|eq| '1) '3)) (app (app '|eq| '1) '2))))))) (lam (lam (lam (lam (app (app (app (app (app (app (app '|setadjoinE| '3) (app (app '|setadjoin| '2) '|emptyset|)) '1) '0) (app (app '|or| (app (app '|eq| '1) '3)) (app (app '|eq| '1) '2))) (app (app '|orIL| (app (app '|eq| '1) '3)) (app (app '|eq| '1) '2))) (lam (app (app (app '|orIR| (app (app '|eq| '2) '4)) (app (app '|eq| '2) '3)) (app (app (app '|uniqinunit| '2) '3) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|binunion| (dpi (obj) (dpi (obj) (obj))) (lam (lam (app '|setunion| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))))) '("AUTO") '("Chad Edward Brown"))

(newabbrev '|binintersect| (dpi (obj) (dpi (obj) (obj))) (lam (lam (app (app '|dsetconstr| '1) (lam (app (app '|in| '1) (fst '0)))))) '("AUTO") '("Chad Edward Brown"))

(newabbrev '|setminus| (dpi (obj) (dpi (obj) (obj))) (lam (lam (app (app '|dsetconstr| '1) (lam (app '|not| (app (app '|in| '1) (fst '0))))))) '("AUTO") '("Chad Edward Brown"))

(newabbrev '|binunionIL| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '2) '0)) (pf (app (app '|in| (app (app '|binunion| '3) '2)) '1)))))) (lam (lam (lam (lam (app (app (app (app '|binunion#F| '3) '2) (lam (app (app '|in| '0) '2))) (app (app (app (app (app '|setunionI| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) '1) '3) '0) (app (app '|setadjoinIL| '3) (app (app '|setadjoin| '2) '|emptyset|)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|binunionLsub| (dpi (obj) (dpi (obj) (pf (app (app '|subset| '1) (app (app '|binunion| '1) '0))))) (lam (lam (app (app (app '|subsetI2| '1) (app (app '|binunion| '1) '0)) (app (app '|binunionIL| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|binunionIR| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '1) '0)) (pf (app (app '|in| (app (app '|binunion| '3) '2)) '1)))))) (lam (lam (lam (lam (app (app (app (app '|binunion#F| '3) '2) (lam (app (app '|in| '0) '2))) (app (app (app (app (app '|setunionI| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) '1) '2) '0) (app (app '|upairsetIR| '3) '2))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|binunionRsub| (dpi (obj) (dpi (obj) (pf (app (app '|subset| '0) (app (app '|binunion| '1) '0))))) (lam (lam (app (app (app '|subsetI2| '0) (app (app '|binunion| '1) '0)) (app (app '|binunionIR| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|binunionE| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|binunion| '2) '1)) '0)) (pf (app (app '|or| (app (app '|in| '3) '1)) (app (app '|in| '2) '1))))))) (lam (lam (lam (lam (app (app (app (app (app '|dexE| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) (lam (app (app '|in| (fst '0)) '2))) (app (app (app '|setunionE2| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) '1) (app (app (app (app '|binunion#U| '3) '2) (lam (app (app '|in| '0) '2))) '0))) (app (app '|or| (app (app '|in| '3) '1)) (app (app '|in| '2) '1))) (lam (lam (app (app (app (app (app (app '|orE| (app (app '|eq| (fst '1)) '5)) (app (app '|eq| (fst '1)) '4)) (app (app (app (app '|upairsetE| '5) '4) (fst '1)) (snd '1))) (app (app '|or| (app (app '|in| '5) '3)) (app (app '|in| '4) '3))) (lam (app (app (app '|orIL| (app (app '|in| '6) '4)) (app (app '|in| '5) '4)) (app (app (app (app (app '|eqE| (fst '2)) '6) (lam (app (app '|in| '0) '5))) '0) '1)))) (lam (app (app (app '|orIR| (app (app '|in| '6) '4)) (app (app '|in| '5) '4)) (app (app (app (app (app '|eqE| (fst '2)) '5) (lam (app (app '|in| '0) '5))) '0) '1))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|binintersectI| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '2) '0)) (dpi (pf (app (app '|in| '2) '1)) (pf (app (app '|in| (app (app '|binintersect| '4) '3)) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app '|binintersect#F| '4) '3) (lam (app (app '|in| '0) '3))) (app (app (app (app '|dsetconstrI| '4) (lam (app (app '|in| '4) (fst '0)))) (pair '2 '1)) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|binintersectEL| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|binintersect| '2) '1)) '0)) (pf (app (app '|in| '3) '1)))))) (lam (lam (lam (lam (app (app (app (app '|dsetconstrEL| '3) (lam (app (app '|in| '3) (fst '0)))) '1) (app (app (app (app '|binintersect#U| '3) '2) (lam (app (app '|in| '0) '2))) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|binintersectER| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|binintersect| '2) '1)) '0)) (pf (app (app '|in| '2) '1)))))) (lam (lam (lam (lam (app (app (app (app '|dsetconstrER| '3) (lam (app (app '|in| '3) (fst '0)))) '1) (app (app (app (app '|binintersect#U| '3) '2) (lam (app (app '|in| '0) '2))) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|binintersectLsub| (dpi (obj) (dpi (obj) (pf (app (app '|subset| (app (app '|binintersect| '1) '0)) '1)))) (lam (lam (app (app (app '|subsetI2| (app (app '|binintersect| '1) '0)) '1) (app (app '|binintersectEL| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|binintersectRsub| (dpi (obj) (dpi (obj) (pf (app (app '|subset| (app (app '|binintersect| '1) '0)) '0)))) (lam (lam (app (app (app '|subsetI2| (app (app '|binintersect| '1) '0)) '0) (app (app '|binintersectER| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setminusI| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '2) '0)) (dpi (pf (app '|not| (app (app '|in| '2) '1))) (pf (app (app '|in| (app (app '|setminus| '4) '3)) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app '|setminus#F| '4) '3) (lam (app (app '|in| '0) '3))) (app (app (app (app '|dsetconstrI| '4) (lam (app '|not| (app (app '|in| '4) (fst '0))))) (pair '2 '1)) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setminusEL| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|setminus| '2) '1)) '0)) (pf (app (app '|in| '3) '1)))))) (lam (lam (lam (lam (app (app (app (app '|dsetconstrEL| '3) (lam (app '|not| (app (app '|in| '3) (fst '0))))) '1) (app (app (app (app '|setminus#U| '3) '2) (lam (app (app '|in| '0) '2))) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setminusER| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|setminus| '2) '1)) '0)) (pf (app '|not| (app (app '|in| '2) '1))))))) (lam (lam (lam (lam (app (app (app (app '|dsetconstrER| '3) (lam (app '|not| (app (app '|in| '3) (fst '0))))) '1) (app (app (app (app '|setminus#U| '3) '2) (lam (app (app '|in| '0) '2))) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setminusLsub| (dpi (obj) (dpi (obj) (pf (app (app '|subset| (app (app '|setminus| '1) '0)) '1)))) (lam (lam (app (app (app '|subsetI2| (app (app '|setminus| '1) '0)) '1) (app (app '|setminusEL| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setminusILneg| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app '|not| (app (app '|in| '2) '0))) (pf (app '|not| (app (app '|in| (app (app '|setminus| '3) '2)) '1))))))) (lam (lam (lam (app (app (app '|contrapositive1| (app (app '|in| (app (app '|setminus| '2) '1)) '0)) (app (app '|in| '2) '0)) (app (app (app '|setminusEL| '2) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setminusIRneg| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '1) '0)) (pf (app '|not| (app (app '|in| (app (app '|setminus| '3) '2)) '1))))))) (lam (lam (lam (lam (app (app '|notI| (app (app '|in| (app (app '|setminus| '3) '2)) '1)) (lam (app (app (app (app '|notE| (app (app '|in| '3) '2)) '|false|) '1) (app (app (app (app '|setminusER| '4) '3) '2) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setminusERneg| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app '|not| (app (app '|in| (app (app '|setminus| '2) '1)) '0))) (dpi (pf (app (app '|in| '3) '1)) (pf (app (app '|in| '3) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app '|contrapositive2| (app (app '|in| '3) '2)) (app (app '|in| (app (app '|setminus| '4) '3)) '2)) (app (app (app (app '|setminusI| '4) '3) '2) '0)) '1)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setminusELneg| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app '|not| (app (app '|in| (app (app '|setminus| '2) '1)) '0))) (dpi (pf (app '|not| (app (app '|in| '2) '1))) (pf (app '|not| (app (app '|in| '4) '2)))))))) (lam (lam (lam (lam (app (app (app '|contrapositive1| (app (app '|in| '3) '1)) (app (app '|in| '2) '1)) (app (app (app (app '|setminusERneg| '3) '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|atleast2p| (dpi (obj) (prop)) (lam (app (app '|dex| '0) (lam (app (app '|dex| '1) (lam (app '|not| (app (app '|eq| (fst '1)) (fst '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|atmost1p| (dpi (obj) (prop)) (lam (app (app '|dall| '0) (lam (app (app '|dall| '1) (lam (app (app '|eq| (fst '1)) (fst '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|atmost2p| (dpi (obj) (prop)) (lam (app (app '|dall| '0) (lam (app (app '|dall| '1) (lam (app (app '|dall| '2) (lam (app (app '|or| (app (app '|eq| (fst '2)) (fst '0))) (app (app '|eq| (fst '1)) (fst '0)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|unitsetp| (dpi (obj) (prop)) (lam (app (app '|and| (app '|nonempty| '0)) (app '|atmost1p| '0))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|upairsetp| (dpi (obj) (prop)) (lam (app (app '|and| (app '|atleast2p| '0)) (app '|atmost2p| '0))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|regular| (dpi (obj) (prop)) (lam (app (app '|dex| '0) (lam (app (app '|eq| (app (app '|binintersect| (fst '0)) '1)) '|emptyset|)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setoftrueEq| (dpi (obj) (pf (app (app '|eq| (app (app '|dsetconstr| '0) (lam '|true|))) '0))) (lam (app (app (app (app '|setext| (app (app '|dsetconstr| '0) (lam '|true|))) '0) (app (app '|dsetconstrEL| '0) (lam '|true|))) (lam (lam (app (app (app (app '|dsetconstrI| '2) (lam '|true|)) (pair '1 '0)) '|trueI|))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|nonemptyImpWitness| (dpi (obj) (dpi (pf (app '|nonempty| '0)) (pf (app (app '|dex| '1) (lam '|true|))))) (lam (lam (app (app (app '|dex#F| '1) (lam '|true|)) (app (app (app (app (app '|eqE2| (app (app '|dsetconstr| '1) (lam '|true|))) '1) (lam (app '|not| (app (app '|eq| '0) '|emptyset|)))) (app '|setoftrueEq| '1)) (app (app '|nonempty#U| '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|symdiff| (dpi (obj) (dpi (obj) (obj))) (lam (lam (app (app '|dsetconstr| (app (app '|binunion| '1) '0)) (lam (app (app '|or| (app '|not| (app (app '|in| '2) (fst '0)))) (app '|not| (app (app '|in| '1) (fst '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|symdiffI1| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '2) '0)) (dpi (pf (app '|not| (app (app '|in| '2) '1))) (pf (app (app '|in| (app (app '|symdiff| '4) '3)) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app '|symdiff#F| '4) '3) (lam (app (app '|in| '0) '3))) (app (app (app (app '|dsetconstrI| (app (app '|binunion| '4) '3)) (lam (app (app '|or| (app '|not| (app (app '|in| '5) (fst '0)))) (app '|not| (app (app '|in| '4) (fst '0)))))) (pair '2 (app (app (app (app '|binunionIL| '4) '3) '2) '1))) (app (app (app '|orIR| (app '|not| (app (app '|in| '4) '2))) (app '|not| (app (app '|in| '3) '2))) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|symdiffI2| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app '|not| (app (app '|in| '2) '0))) (dpi (pf (app (app '|in| '2) '1)) (pf (app (app '|in| (app (app '|symdiff| '4) '3)) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app '|symdiff#F| '4) '3) (lam (app (app '|in| '0) '3))) (app (app (app (app '|dsetconstrI| (app (app '|binunion| '4) '3)) (lam (app (app '|or| (app '|not| (app (app '|in| '5) (fst '0)))) (app '|not| (app (app '|in| '4) (fst '0)))))) (pair '2 (app (app (app (app '|binunionIR| '4) '3) '2) '0))) (app (app (app '|orIL| (app '|not| (app (app '|in| '4) '2))) (app '|not| (app (app '|in| '3) '2))) '1)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|symdiffE| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|symdiff| '2) '1)) '0)) (dpi (prop) (dpi (dpi (pf (app (app '|in| '4) '2)) (dpi (pf (app '|not| (app (app '|in| '4) '3))) (pf '2))) (dpi (dpi (pf (app '|not| (app (app '|in| '5) '3))) (dpi (pf (app (app '|in| '5) '4)) (pf '3))) (pf '2)))))))) (lam (lam (lam (lam (lam (lam (lam (app (app (app (app (app (app '|orE| (app '|not| (app (app '|in| '6) '4))) (app '|not| (app (app '|in| '5) '4))) (app (app (app (app '|dsetconstrER| (app (app '|binunion| '6) '5)) (lam (app (app '|or| (app '|not| (app (app '|in| '7) (fst '0)))) (app '|not| (app (app '|in| '6) (fst '0)))))) '4) (app (app (app (app '|symdiff#U| '6) '5) (lam (app (app '|in| '0) '5))) '3))) '2) (lam (app (app (app (app (app (app '|orE| (app (app '|in| '7) '5)) (app (app '|in| '6) '5)) (app (app (app (app '|binunionE| '7) '6) '5) (app (app (app (app '|dsetconstrEL| (app (app '|binunion| '7) '6)) (lam (app (app '|or| (app '|not| (app (app '|in| '8) (fst '0)))) (app '|not| (app (app '|in| '7) (fst '0)))))) '5) (app (app (app (app '|symdiff#U| '7) '6) (lam (app (app '|in| '0) '6))) '4)))) '3) (lam (app (app (app (app '|notE| (app (app '|in| '8) '6)) '4) '0) '1))) (app '1 '0)))) (lam (app (app (app (app (app (app '|orE| (app (app '|in| '7) '5)) (app (app '|in| '6) '5)) (app (app (app (app '|binunionE| '7) '6) '5) (app (app (app (app '|dsetconstrEL| (app (app '|binunion| '7) '6)) (lam (app (app '|or| (app '|not| (app (app '|in| '8) (fst '0)))) (app '|not| (app (app '|in| '7) (fst '0)))))) '5) (app (app (app (app '|symdiff#U| '7) '6) (lam (app (app '|in| '0) '6))) '4)))) '3) (lam (app (app '3 '0) '1))) (lam (app (app (app (app '|notE| (app (app '|in| '7) '6)) '4) '0) '1)))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|symdiffIneg1| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| '2) '0)) (dpi (pf (app (app '|in| '2) '1)) (pf (app '|not| (app (app '|in| (app (app '|symdiff| '4) '3)) '2)))))))) (lam (lam (lam (lam (lam (app (app '|notI| (app (app '|in| (app (app '|symdiff| '4) '3)) '2)) (lam (app (app (app (app (app (app (app '|symdiffE| '5) '4) '3) '0) '|false|) (lam (app (app (app '|notE| (app (app '|in| '5) '4)) '|false|) '2))) (lam (lam (app (app (app (app '|notE| (app (app '|in| '7) '5)) '|false|) '4) '1))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|symdiffIneg2| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app '|not| (app (app '|in| '2) '0))) (dpi (pf (app '|not| (app (app '|in| '2) '1))) (pf (app '|not| (app (app '|in| (app (app '|symdiff| '4) '3)) '2)))))))) (lam (lam (lam (lam (lam (app (app '|notI| (app (app '|in| (app (app '|symdiff| '4) '3)) '2)) (lam (app (app (app (app (app (app (app '|symdiffE| '5) '4) '3) '0) '|false|) (lam (lam (app (app (app (app '|notE| (app (app '|in| '7) '5)) '|false|) '1) '4)))) (lam (lam (app (app (app (app '|notE| (app (app '|in| '6) '5)) '|false|) '0) '3))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setsmeet| (dpi (obj) (dpi (obj) (prop))) (lam (lam (app (app '|dex| '1) (lam (app (app '|in| '1) (fst '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|disjoint| (dpi (obj) (dpi (obj) (prop))) (lam (lam (app '|not| (app (app '|dex| '1) (lam (app (app '|in| '1) (fst '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|notinsingleton| (dpi (obj) (dpi (obj) (dpi (pf (app '|not| (app (app '|eq| '1) '0))) (pf (app '|not| (app (app '|in| (app (app '|setadjoin| '2) '|emptyset|)) '1)))))) (lam (lam (app (app (app '|contrapositive1| (app (app '|in| (app (app '|setadjoin| '1) '|emptyset|)) '0)) (app (app '|eq| '1) '0)) (lam (app (app (app '|symeq| '1) '2) (app (app (app '|uniqinunit| '1) '2) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|singletonsuniq| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| '0) '|emptyset|))) (pf (app (app '|eq| '2) '1))))) (lam (lam (lam (app (app (app '|uniqinunit| '2) '1) (app (app (app (app (app '|eqE| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| '1) '|emptyset|)) (lam (app (app '|in| '0) '3))) '0) (app (app '|setadjoinIL| '2) '|emptyset|)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|singletonsswitch| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|setadjoin| '0) '|emptyset|)) '1)) (pf (app (app '|in| (app (app '|setadjoin| '2) '|emptyset|)) '1))))) (lam (lam (lam (app (app (app '|eqinunit| '1) '2) (app (app (app '|symeq| '2) '1) (app (app (app '|uniqinunit| '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setunionsingleton1| (dpi (obj) (pf (app (app '|subset| (app '|setunion| (app (app '|setadjoin| '0) '|emptyset|))) '0))) (lam (app (app (app '|subsetI2| (app '|setunion| (app (app '|setadjoin| '0) '|emptyset|))) '0) (lam (lam (app (app (app (app (app '|dexE| (app (app '|setadjoin| '2) '|emptyset|)) (lam (app (app '|in| (fst '0)) '2))) (app (app (app '|setunionE2| (app (app '|setadjoin| '2) '|emptyset|)) '1) '0)) (app (app '|in| '2) '1)) (lam (app (app (app (app '|eqE| (fst '0)) '3) (lam (app (app '|in| '0) '3))) (app (app (app '|uniqinunit| (fst '0)) '3) (snd '0))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setunionsingleton2| (dpi (obj) (pf (app (app '|subset| '0) (app '|setunion| (app (app '|setadjoin| '0) '|emptyset|))))) (lam (app (app (app '|subsetI2| '0) (app '|setunion| (app (app '|setadjoin| '0) '|emptyset|))) (lam (lam (app (app (app (app (app '|setunionI| (app (app '|setadjoin| '2) '|emptyset|)) '1) '2) '0) (app (app '|setadjoinIL| '2) '|emptyset|)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setunionsingleton| (dpi (obj) (pf (app (app '|eq| (app '|setunion| (app (app '|setadjoin| '0) '|emptyset|))) '0))) (lam (app (app (app (app '|setextsub| (app '|setunion| (app (app '|setadjoin| '0) '|emptyset|))) '0) (app '|setunionsingleton1| '0)) (app '|setunionsingleton2| '0))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|singleton| (dpi (obj) (prop)) (lam (app (app '|dex| '0) (lam (app (app '|eq| '1) (app (app '|setadjoin| (fst '0)) '|emptyset|))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|theprop| (dpi (dclass '|singleton|) (pf (app (app '|in| (fst '0)) (app '|setunion| (fst '0))))) (lam (app (app (app (app (app '|dexE| (fst '0)) (lam (app (app '|eq| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))) (app (app '|singleton#U| (fst '0)) (snd '0))) (app (app '|in| (fst '0)) (app '|setunion| (fst '0)))) (lam (lam (app (app (app (app (app '|eqE2| (fst '2)) (app (app '|setadjoin| (fst '1)) '|emptyset|)) (lam (app (app '|in| '0) (app '|setunion| '0)))) '0) (app (app (app '|eqinunit| (app '|setunion| (app (app '|setadjoin| (fst '1)) '|emptyset|))) (fst '1)) (app '|setunionsingleton| (fst '1)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|the| (dpi (dclass '|singleton|) (dclass (app '|in| (fst '0)))) (lam (pair (app '|setunion| (fst '0)) (app '|theprop| '0))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|singletonprop| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '2)) (dpi (pf (app '2 '1)) (dpi (pf (app '3 '1)) (pf (app (app '|eq| (fst '3)) (fst '2))))))) (dpi (pf (app (app '|dex| '2) '1)) (pf (app '|singleton| (app (app '|dsetconstr| '3) '2))))))) (lam (lam (lam (lam (app (app (app (app (app '|dexE| '3) '2) '0) (app '|singleton| (app (app '|dsetconstr| '3) '2))) (lam (lam (app (app '|singleton#F| (app (app '|dsetconstr| '5) '4)) (app (app (app (app '|dexI| (app (app '|dsetconstr| '5) '4)) (lam (app (app '|eq| (app (app '|dsetconstr| '6) '5)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))) (pair (fst '1) (app (app (app (app '|dsetconstrI| '5) '4) '1) '0))) (app (app (app (app '|setext| (app (app '|dsetconstr| '5) '4)) (app (app '|setadjoin| (fst '1)) '|emptyset|)) (lam (lam (app (app (app '|eqinunit| '1) (fst '3)) (app (app (app (app '5 (pair '1 (app (app (app (app '|dsetconstrEL| '7) '6) '1) '0))) '3) (app (app (app (app '|dsetconstrER| '7) '6) '1) '0)) '2))))) (lam (lam (app (app (app (app (app '|eqE2| '1) (fst '3)) (app '|in| (app (app '|dsetconstr| '7) '6))) (app (app (app '|uniqinunit| '1) (fst '3)) '0)) (app (app (app (app '|dsetconstrI| '7) '6) '3) '2)))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ex1| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (prop))) (lam (lam (app '|singleton| (app (app '|dsetconstr| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ex1I| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (dclass (app '|in| '1)) (dpi (pf (app '1 '0)) (dpi (dpi (dclass (app '|in| '3)) (dpi (pf (app '3 '0)) (pf (app (app '|eq| (fst '1)) (fst '3))))) (pf (app (app '|ex1| '4) '3))))))) (lam (lam (lam (lam (lam (app (app (app '|ex1#F| '4) '3) (app (app '|singleton#F| (app (app '|dsetconstr| '4) '3)) (app (app (app (app '|dexI| (app (app '|dsetconstr| '4) '3)) (lam (app (app '|eq| (app (app '|dsetconstr| '5) '4)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))) (pair (fst '2) (app (app (app (app '|dsetconstrI| '4) '3) '2) '1))) (app (app (app (app '|setext| (app (app '|dsetconstr| '4) '3)) (app (app '|setadjoin| (fst '2)) '|emptyset|)) (lam (lam (app (app (app '|eqinunit| '1) (fst '4)) (app (app '2 (pair '1 (app (app (app (app '|dsetconstrEL| '6) '5) '1) '0))) (app (app (app (app '|dsetconstrER| '6) '5) '1) '0)))))) (lam (lam (app (app (app (app (app '|eqE2| '1) (fst '4)) (app '|in| (app (app '|dsetconstr| '6) '5))) (app (app (app '|uniqinunit| '1) (fst '4)) '0)) (app (app (app (app '|dsetconstrI| '6) '5) '4) '3))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ex1I2| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '2)) (dpi (pf (app '2 '1)) (dpi (pf (app '3 '1)) (pf (app (app '|eq| (fst '3)) (fst '2))))))) (dpi (pf (app (app '|dex| '2) '1)) (pf (app (app '|ex1| '3) '2)))))) (lam (lam (lam (lam (app (app (app '|ex1#F| '3) '2) (app (app (app (app '|singletonprop| '3) '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ex1E1| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (pf (app (app '|ex1| '1) '0)) (pf (app (app '|dex| '2) '1))))) (lam (lam (lam (app (app (app (app (app '|dexE| (app (app '|dsetconstr| '2) '1)) (lam (app (app '|eq| (app (app '|dsetconstr| '3) '2)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))) (app (app '|singleton#U| (app (app '|dsetconstr| '2) '1)) (app (app (app '|ex1#U| '2) '1) '0))) (app (app '|dex| '2) '1)) (lam (lam (app (app (app (app '|dexI| '4) '3) (pair (fst '1) (app (app (app (app '|dsetconstrEL| '4) '3) (fst '1)) (snd '1)))) (app (app (app (app '|dsetconstrER| '4) '3) (fst '1)) (snd '1))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ex1E2| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (prop)) (dpi (pf (app (app '|ex1| '1) '0)) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app '3 '1)) (dpi (pf (app '4 '1)) (pf (app (app '|eq| (fst '3)) (fst '2)))))))))) (lam (lam (lam (lam (lam (lam (lam (app (app (app (app (app '|dexE| (app (app '|dsetconstr| '6) '5)) (lam (app (app '|eq| (app (app '|dsetconstr| '7) '6)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))) (app (app '|singleton#U| (app (app '|dsetconstr| '6) '5)) (app (app (app '|ex1#U| '6) '5) '4))) (app (app '|eq| (fst '3)) (fst '2))) (lam (lam (app (app (app (app (app '|symtrans1eq| (fst '5)) (fst '1)) (fst '4)) (app (app (app '|uniqinunit| (fst '5)) (fst '1)) (app (app (app (app (app '|eqE| (app (app '|dsetconstr| '8) '7)) (app (app '|setadjoin| (fst '1)) '|emptyset|)) (lam (app (app '|in| '0) (fst '6)))) '0) (app (app (app (app '|dsetconstrI| '8) '7) '5) '3)))) (app (app (app '|uniqinunit| (fst '4)) (fst '1)) (app (app (app (app (app '|eqE| (app (app '|dsetconstr| '8) '7)) (app (app '|setadjoin| (fst '1)) '|emptyset|)) (lam (app (app '|in| '0) (fst '5)))) '0) (app (app (app (app '|dsetconstrI| '8) '7) '4) '2)))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|upairequniteq| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) (app (app '|setadjoin| '0) '|emptyset|))) (pf (app (app '|eq| '3) '2)))))) (lam (lam (lam (lam (app (app (app (app (app '|symtrans1eq| '3) '1) '2) (app (app (app '|uniqinunit| '3) '1) (app (app (app (app (app '|eqE| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) (app (app '|setadjoin| '1) '|emptyset|)) (lam (app (app '|in| '0) '4))) '0) (app (app '|setadjoinIL| '3) (app (app '|setadjoin| '2) '|emptyset|))))) (app (app (app '|uniqinunit| '2) '1) (app (app (app (app (app '|eqE| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) (app (app '|setadjoin| '1) '|emptyset|)) (lam (app (app '|in| '0) '3))) '0) (app (app '|secondinupair| '3) '2)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setukpairinjL1| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|setadjoin| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| '0) '|emptyset|))) (pf (app (app '|eq| '3) '1)))))) (lam (lam (lam (lam (app (app (app (app (app (app '|orE| (app (app '|eq| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| '3) '|emptyset|))) (app (app '|eq| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|)))) (app (app (app (app '|upairsetE| (app (app '|setadjoin| '3) '|emptyset|)) (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) (app (app '|setadjoin| '1) '|emptyset|)) '0)) (app (app '|eq| '3) '1)) (lam (app (app (app '|symeq| '2) '4) (app (app (app '|singletonsuniq| '2) '4) '0)))) (lam (app (app (app '|uniqinunit| '4) '2) (app (app (app (app (app '|eqE2| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| '4) (app (app '|setadjoin| '3) '|emptyset|))) (lam (app (app '|in| '0) '5))) '0) (app (app '|setadjoinIL| '4) (app (app '|setadjoin| '3) '|emptyset|)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setukpairinjL2| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| (app (app '|setadjoin| (app (app '|setadjoin| '3) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|)))) (pf (app (app '|eq| '4) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app '|setukpairinjL1| '4) '3) '2) (app (app (app (app (app '|eqE2| (app (app '|setadjoin| (app (app '|setadjoin| '4) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '4) (app (app '|setadjoin| '3) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) '|emptyset|))) (lam (app (app '|in| '0) (app (app '|setadjoin| '3) '|emptyset|)))) '0) (app (app '|setadjoinIL| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) '|emptyset|))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setukpairinjR11| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| '1) '0)) (pf (app (app '|eq| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) (app (app '|setadjoin| '2) '|emptyset|)))))) (lam (lam (lam (app (app (app (app '|setext| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) (app (app '|setadjoin| '2) '|emptyset|)) (lam (lam (app (app (app (app (app (app '|orE| (app (app '|eq| '1) '4)) (app (app '|eq| '1) '3)) (app (app (app (app '|upairsetE| '4) '3) '1) '0)) (app (app '|in| (app (app '|setadjoin| '4) '|emptyset|)) '1)) (app (app '|eqinunit| '1) '4)) (lam (app (app (app '|eqinunit| '2) '5) (app (app (app (app (app '|symtrans1eq| '2) '4) '5) '0) '3))))))) (lam (lam (app (app (app (app (app '|eqE2| '1) '4) (app '|in| (app (app '|setadjoin| '4) (app (app '|setadjoin| '3) '|emptyset|)))) (app (app (app '|uniqinunit| '1) '4) '0)) (app (app '|setadjoinIL| '4) (app (app '|setadjoin| '3) '|emptyset|))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setukpairinjR12| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| '1) '0)) (pf (app (app '|eq| (app (app '|setadjoin| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| '2) '|emptyset|)) '|emptyset|)))))) (lam (lam (lam (app (app (app '|setukpairinjR11| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) (app (app (app '|symeq| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) (app (app '|setadjoin| '2) '|emptyset|)) (app (app (app '|setukpairinjR11| '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setukpairinjR1| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| (app (app '|setadjoin| (app (app '|setadjoin| '3) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|)))) (dpi (pf (app (app '|eq| '2) '1)) (pf (app (app '|eq| '4) '2)))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app '|eqE| '3) '2) (app '|eq| '4)) '0) (app (app (app '|uniqinunit| '4) '3) (app (app (app (app (app '|eqE| (app (app '|setadjoin| '5) (app (app '|setadjoin| '4) '|emptyset|))) (app (app '|setadjoin| '3) '|emptyset|)) (lam (app (app '|in| '0) '5))) (app (app (app '|uniqinunit| (app (app '|setadjoin| '5) (app (app '|setadjoin| '4) '|emptyset|))) (app (app '|setadjoin| '3) '|emptyset|)) (app (app (app (app (app '|eqE| (app (app '|setadjoin| (app (app '|setadjoin| '5) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '5) (app (app '|setadjoin| '4) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| '3) '|emptyset|)) '|emptyset|)) (lam (app (app '|in| '0) (app (app '|setadjoin| '6) (app (app '|setadjoin| '5) '|emptyset|))))) (app (app (app (app (app '|transeq| (app (app '|setadjoin| (app (app '|setadjoin| '5) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '5) (app (app '|setadjoin| '4) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| '3) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| '3) '|emptyset|)) '|emptyset|)) '1) (app (app (app '|setukpairinjR12| '3) '2) '0))) (app (app '|secondinupair| (app (app '|setadjoin| '5) '|emptyset|)) (app (app '|setadjoin| '5) (app (app '|setadjoin| '4) '|emptyset|)))))) (app (app '|secondinupair| '5) '4)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setukpairinjR2| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| (app (app '|setadjoin| (app (app '|setadjoin| '3) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|)))) (pf (app (app '|eq| '3) '1))))))) (lam (lam (lam (lam (lam (app (app (app (app (app (app '|orE| (app (app '|eq| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) (app (app '|setadjoin| '4) '|emptyset|))) (app (app '|eq| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) (app (app '|setadjoin| '4) (app (app '|setadjoin| '3) '|emptyset|)))) (app (app (app (app '|upairsetE| (app (app '|setadjoin| '4) '|emptyset|)) (app (app '|setadjoin| '4) (app (app '|setadjoin| '3) '|emptyset|))) (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) (app (app (app (app (app '|eqE2| (app (app '|setadjoin| (app (app '|setadjoin| '4) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '4) (app (app '|setadjoin| '3) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) '|emptyset|))) (lam (app (app '|in| '0) (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))))) '0) (app (app '|secondinupair| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|)))))) (app (app '|eq| '3) '1)) (lam (app (app (app (app (app (app '|setukpairinjR1| '5) '4) '3) '2) '1) (app (app (app (app '|upairequniteq| '3) '2) '5) '0)))) (lam (app (app (app (app (app (app '|orE| (app (app '|eq| '2) '5)) (app (app '|eq| '2) '4)) (app (app (app (app '|upairsetE| '5) '4) '2) (app (app (app (app (app '|eqE| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) (app (app '|setadjoin| '5) (app (app '|setadjoin| '4) '|emptyset|))) (lam (app (app '|in| '0) '3))) '0) (app (app '|secondinupair| '3) '2)))) (app (app '|eq| '4) '2)) (lam (app (app (app (app (app (app '|setukpairinjR1| '6) '5) '4) '3) '2) (app (app (app '|symeq| '3) '4) (app (app (app (app (app '|eqE| '6) '4) (app '|eq| '3)) (app (app (app (app (app '|setukpairinjL2| '6) '5) '4) '3) '2)) '0))))) (app (app '|symeq| '2) '4))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setukpairIL| (dpi (obj) (dpi (obj) (pf (app (app '|in| (app '|setunion| (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|)))) '1)))) (lam (lam (app (app (app (app (app '|setunionI| (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|))) '1) (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoinIL| '1) '|emptyset|)) (app (app '|setadjoinIL| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setukpairIR| (dpi (obj) (dpi (obj) (pf (app (app '|in| (app '|setunion| (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|)))) '0)))) (lam (lam (app (app (app (app (app '|setunionI| (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|))) '0) (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) (app (app '|secondinupair| '1) '0)) (app (app '|secondinupair| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|iskpair| (dpi (obj) (prop)) (lam (app (app '|dex| (app '|setunion| '0)) (lam (app (app '|dex| (app '|setunion| '1)) (lam (app (app '|eq| '2) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|kpairiskpair| (dpi (obj) (dpi (obj) (pf (app '|iskpair| (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|)))))) (lam (lam (app (app '|iskpair#F| (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|))) (app (app (app (app '|dexI| (app '|setunion| (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|)))) (lam (app (app '|dex| (app '|setunion| (app (app '|setadjoin| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) '|emptyset|)))) (lam (app (app '|eq| (app (app '|setadjoin| (app (app '|setadjoin| '3) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))))))) (pair '1 (app (app '|setukpairIL| '1) '0))) (app (app (app (app '|dexI| (app '|setunion| (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|)))) (lam (app (app '|eq| (app (app '|setadjoin| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '2) (app (app '|setadjoin| '1) '|emptyset|))) '|emptyset|))) (app (app '|setadjoin| (app (app '|setadjoin| '2) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '2) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))))) (pair '0 (app (app '|setukpairIR| '1) '0))) (app '|eqI| (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|kpair| (dpi (obj) (dpi (obj) (dclass '|iskpair|))) (lam (lam (pair (app (app '|setadjoin| (app (app '|setadjoin| '1) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '1) (app (app '|setadjoin| '0) '|emptyset|))) '|emptyset|)) (app (app '|kpairiskpair| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setukpairinjL| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| (fst (app (app '|kpair| '3) '2))) (fst (app (app '|kpair| '1) '0)))) (pf (app (app '|eq| '4) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app (app '|setukpairinjL2| '4) '3) '2) '1) (app (app (app (app '|kpair#U| '4) '3) (lam (app (app '|eq| '0) (app (app '|setadjoin| (app (app '|setadjoin| '3) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '3) (app (app '|setadjoin| '2) '|emptyset|))) '|emptyset|))))) (app (app (app (app '|kpair#U| '2) '1) (app '|eq| (fst (app (app '|kpair| '4) '3)))) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setukpairinjR| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|eq| (fst (app (app '|kpair| '3) '2))) (fst (app (app '|kpair| '1) '0)))) (pf (app (app '|eq| '3) '1))))))) (lam (lam (lam (lam (lam (app (app (app (app (app '|setukpairinjR2| '4) '3) '2) '1) (app (app (app (app '|kpair#U| '2) '1) (app '|eq| (app (app '|setadjoin| (app (app '|setadjoin| '4) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| '4) (app (app '|setadjoin| '3) '|emptyset|))) '|emptyset|)))) (app (app (app (app '|kpair#U| '4) '3) (lam (app (app '|eq| '0) (fst (app (app '|kpair| '3) '2))))) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|kfstsingleton| (dpi (dclass '|iskpair|) (pf (app '|singleton| (app (app '|dsetconstr| (app '|setunion| (fst '0))) (lam (app (app '|in| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))))))) (lam (app (app (app (app (app '|dexE| (app '|setunion| (fst '0))) (lam (app (app '|dex| (app '|setunion| (fst '1))) (lam (app (app '|eq| (fst '2)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))))))) (app (app '|iskpair#U| (fst '0)) (snd '0))) (app '|singleton| (app (app '|dsetconstr| (app '|setunion| (fst '0))) (lam (app (app '|in| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))))) (lam (lam (app (app (app (app (app '|dexE| (app '|setunion| (fst '2))) (lam (app (app '|eq| (fst '3)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '2)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '2)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))))) '0) (app '|singleton| (app (app '|dsetconstr| (app '|setunion| (fst '2))) (lam (app (app '|in| (fst '3)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))))) (lam (lam (app (app (app '|ex1#U| (app '|setunion| (fst '4))) (lam (app (app '|in| (fst '5)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))) (app (app (app (app (app '|ex1I| (app '|setunion| (fst '4))) (lam (app (app '|in| (fst '5)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))) '3) (app (app (app (app (app '|eqE2| (fst '4)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '3)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '3)) (app (app '|setadjoin| (fst '1)) '|emptyset|))) '|emptyset|))) (lam (app (app '|in| '0) (app (app '|setadjoin| (fst '4)) '|emptyset|)))) '0) (app (app '|setadjoinIL| (app (app '|setadjoin| (fst '3)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '3)) (app (app '|setadjoin| (fst '1)) '|emptyset|))) '|emptyset|)))) (lam (lam (app (app (app '|symeq| (fst '5)) (fst '1)) (app (app (app (app '|setukpairinjL1| (fst '5)) (fst '3)) (fst '1)) (app (app (app (app (app '|eqE| (fst '6)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '5)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '5)) (app (app '|setadjoin| (fst '3)) '|emptyset|))) '|emptyset|))) (lam (app (app '|in| '0) (app (app '|setadjoin| (fst '2)) '|emptyset|)))) '2) '0)))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|kfst| (dpi (dclass '|iskpair|) (obj)) (lam (fst (app '|the| (pair (app (app '|dsetconstr| (app '|setunion| (fst '0))) (lam (app (app '|in| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))) (app '|kfstsingleton| '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|kfstpairEq| (dpi (obj) (dpi (obj) (pf (app (app '|eq| (app '|kfst| (app (app '|kpair| '1) '0))) '1)))) (lam (lam (app (app (app '|symeq| '1) (app '|kfst| (app (app '|kpair| '1) '0))) (app (app (app (app '|setukpairinjL1| '1) '0) (app '|kfst| (app (app '|kpair| '1) '0))) (app (app (app (app '|kpair#U| '1) '0) (lam (app (app '|in| '0) (app (app '|setadjoin| (app '|kfst| (app (app '|kpair| '2) '1))) '|emptyset|)))) (app (app (app (app '|dsetconstrER| (app '|setunion| (fst (app (app '|kpair| '1) '0)))) (lam (app (app '|in| (fst (app (app '|kpair| '2) '1))) (app (app '|setadjoin| (fst '0)) '|emptyset|)))) (app '|kfst| (app (app '|kpair| '1) '0))) (app (app (app '|kfst#F| (app (app '|kpair| '1) '0)) (app '|in| (app (app '|dsetconstr| (app '|setunion| (fst (app (app '|kpair| '1) '0)))) (lam (app (app '|in| (fst (app (app '|kpair| '2) '1))) (app (app '|setadjoin| (fst '0)) '|emptyset|)))))) (snd (app '|the| (pair (app (app '|dsetconstr| (app '|setunion| (fst (app (app '|kpair| '1) '0)))) (lam (app (app '|in| (fst (app (app '|kpair| '2) '1))) (app (app '|setadjoin| (fst '0)) '|emptyset|)))) (app '|kfstsingleton| (app (app '|kpair| '1) '0)))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ksndsingleton| (dpi (dclass '|iskpair|) (pf (app '|singleton| (app (app '|dsetconstr| (app '|setunion| (fst '0))) (lam (app (app '|eq| (fst '1)) (fst (app (app '|kpair| (app '|kfst| '1)) (fst '0))))))))) (lam (app (app (app (app (app '|dexE| (app '|setunion| (fst '0))) (lam (app (app '|dex| (app '|setunion| (fst '1))) (lam (app (app '|eq| (fst '2)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))))))) (app (app '|iskpair#U| (fst '0)) (snd '0))) (app '|singleton| (app (app '|dsetconstr| (app '|setunion| (fst '0))) (lam (app (app '|eq| (fst '1)) (fst (app (app '|kpair| (app '|kfst| '1)) (fst '0)))))))) (lam (lam (app (app (app (app (app '|dexE| (app '|setunion| (fst '2))) (lam (app (app '|eq| (fst '3)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '2)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '2)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))))) '0) (app '|singleton| (app (app '|dsetconstr| (app '|setunion| (fst '2))) (lam (app (app '|eq| (fst '3)) (fst (app (app '|kpair| (app '|kfst| '3)) (fst '0)))))))) (lam (lam (app (app (app '|ex1#U| (app '|setunion| (fst '4))) (lam (app (app '|eq| (fst '5)) (fst (app (app '|kpair| (app '|kfst| '5)) (fst '0)))))) (app (app (app (app (app '|ex1I| (app '|setunion| (fst '4))) (lam (app (app '|eq| (fst '5)) (fst (app (app '|kpair| (app '|kfst| '5)) (fst '0)))))) '1) (app (app (app (app (app '|eqE2| (app '|kfst| '4)) (fst '3)) (lam (app (app '|eq| (fst '5)) (fst (app (app '|kpair| '0) (fst '2)))))) (app (app (app (app (app (app '|eqCE2| '|iskpair|) '4) (app (app '|kpair| (fst '3)) (fst '1))) (lam (app (app '|eq| (app '|kfst| '0)) (fst '4)))) (app (app (app (app '|kpair#F| (fst '3)) (fst '1)) (app '|eq| (fst '4))) '0)) (app (app '|kfstpairEq| (fst '3)) (fst '1)))) (app (app (app (app '|kpair#F| (fst '3)) (fst '1)) (app '|eq| (fst '4))) '0))) (lam (lam (app (app (app (app (app '|setukpairinjR| (fst '5)) (fst '1)) (fst '5)) (fst '3)) (app (app (app (app (app (app '|eqCE| '|iskpair|) '6) (app (app '|kpair| (fst '5)) (fst '1))) (lam (app (app '|eq| (fst '0)) (fst (app (app '|kpair| (fst '6)) (fst '4)))))) (app (app (app (app (app '|eqE| (app '|kfst| '6)) (fst '5)) (lam (app (app '|eq| (fst '7)) (fst (app (app '|kpair| '0) (fst '2)))))) (app (app (app (app (app (app '|eqCE2| '|iskpair|) '6) (app (app '|kpair| (fst '5)) (fst '3))) (lam (app (app '|eq| (app '|kfst| '0)) (fst '6)))) (app (app (app (app '|kpair#F| (fst '5)) (fst '3)) (app '|eq| (fst '6))) '2)) (app (app '|kfstpairEq| (fst '5)) (fst '3)))) '0)) (app (app (app (app '|kpair#F| (fst '5)) (fst '3)) (app '|eq| (fst '6))) '2)))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ksnd| (dpi (dclass '|iskpair|) (obj)) (lam (fst (app '|the| (pair (app (app '|dsetconstr| (app '|setunion| (fst '0))) (lam (app (app '|eq| (fst '1)) (fst (app (app '|kpair| (app '|kfst| '1)) (fst '0)))))) (app '|ksndsingleton| '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ksndpairEq| (dpi (obj) (dpi (obj) (pf (app (app '|eq| (app '|ksnd| (app (app '|kpair| '1) '0))) '0)))) (lam (lam (app (app (app '|symeq| '0) (app '|ksnd| (app (app '|kpair| '1) '0))) (app (app (app (app (app '|setukpairinjR| '1) '0) (app '|kfst| (app (app '|kpair| '1) '0))) (app '|ksnd| (app (app '|kpair| '1) '0))) (app (app (app (app '|dsetconstrER| (app '|setunion| (fst (app (app '|kpair| '1) '0)))) (lam (app (app '|eq| (fst (app (app '|kpair| '2) '1))) (fst (app (app '|kpair| (app '|kfst| (app (app '|kpair| '2) '1))) (fst '0)))))) (app '|ksnd| (app (app '|kpair| '1) '0))) (app (app (app '|ksnd#F| (app (app '|kpair| '1) '0)) (app '|in| (app (app '|dsetconstr| (app '|setunion| (fst (app (app '|kpair| '1) '0)))) (lam (app (app '|eq| (fst (app (app '|kpair| '2) '1))) (fst (app (app '|kpair| (app '|kfst| (app (app '|kpair| '2) '1))) (fst '0)))))))) (snd (app '|the| (pair (app (app '|dsetconstr| (app '|setunion| (fst (app (app '|kpair| '1) '0)))) (lam (app (app '|eq| (fst (app (app '|kpair| '2) '1))) (fst (app (app '|kpair| (app '|kfst| (app (app '|kpair| '2) '1))) (fst '0)))))) (app '|ksndsingleton| (app (app '|kpair| '1) '0))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|kpairsurjEq| (dpi (dclass '|iskpair|) (pf (app (app '|eq| (fst (app (app '|kpair| (app '|kfst| '0)) (app '|ksnd| '0)))) (fst '0)))) (lam (app (app (app (app (app '|dexE| (app '|setunion| (fst '0))) (lam (app (app '|dex| (app '|setunion| (fst '1))) (lam (app (app '|eq| (fst '2)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))))))) (app (app '|iskpair#U| (fst '0)) (snd '0))) (app (app '|eq| (fst (app (app '|kpair| (app '|kfst| '0)) (app '|ksnd| '0)))) (fst '0))) (lam (lam (app (app (app (app (app '|dexE| (app '|setunion| (fst '2))) (lam (app (app '|eq| (fst '3)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '2)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '2)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))))) '0) (app (app '|eq| (fst (app (app '|kpair| (app '|kfst| '2)) (app '|ksnd| '2)))) (fst '2))) (lam (lam (app (app (app (app (app '|symtrans1eq| (fst (app (app '|kpair| (app '|kfst| '4)) (app '|ksnd| '4)))) (fst (app (app '|kpair| (fst '3)) (fst '1)))) (fst '4)) (app (app (app (app (app '|eqE2| (app '|ksnd| '4)) (fst '1)) (lam (app (app '|eq| (fst (app (app '|kpair| (app '|kfst| '5)) '0))) (fst (app (app '|kpair| (fst '4)) (fst '2)))))) (app (app (app (app (app (app '|eqCE2| '|iskpair|) '4) (app (app '|kpair| (fst '3)) (fst '1))) (lam (app (app '|eq| (app '|ksnd| '0)) (fst '2)))) (app (app (app (app '|kpair#F| (fst '3)) (fst '1)) (app '|eq| (fst '4))) '0)) (app (app '|ksndpairEq| (fst '3)) (fst '1)))) (app (app (app (app (app '|eqE2| (app '|kfst| '4)) (fst '3)) (lam (app (app '|eq| (fst (app (app '|kpair| '0) (fst '2)))) (fst (app (app '|kpair| (fst '4)) (fst '2)))))) (app (app (app (app (app (app '|eqCE2| '|iskpair|) '4) (app (app '|kpair| (fst '3)) (fst '1))) (lam (app (app '|eq| (app '|kfst| '0)) (fst '4)))) (app (app (app (app '|kpair#F| (fst '3)) (fst '1)) (app '|eq| (fst '4))) '0)) (app (app '|kfstpairEq| (fst '3)) (fst '1)))) (app '|eqI| (fst (app (app '|kpair| (fst '3)) (fst '1))))))) (app (app (app (app '|kpair#F| (fst '3)) (fst '1)) (app '|eq| (fst '4))) '0))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|powersetsubset| (dpi (obj) (dpi (obj) (dpi (pf (app (app '|subset| '1) '0)) (pf (app (app '|subset| (app '|powerset| '2)) (app '|powerset| '1)))))) (lam (lam (lam (app (app (app '|subsetI2| (app '|powerset| '2)) (app '|powerset| '1)) (lam (lam (app (app (app '|powersetI| '3) '1) (lam (lam (app (app (app (app (app '|subsetE| '6) '5) '1) '4) (app (app (app (app (app '|powersetE| '6) '3) '1) '2) '0))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|singletonsubset| (dpi (obj) (dpi (dclass (app '|in| '0)) (pf (app (app '|subset| (app (app '|setadjoin| (fst '0)) '|emptyset|)) '1)))) (lam (lam (app (app (app '|subsetI2| (app (app '|setadjoin| (fst '0)) '|emptyset|)) '1) (lam (lam (app (app (app (app (app '|eqE2| '1) (fst '2)) (app '|in| '3)) (app (app (app '|uniqinunit| '1) (fst '2)) '0)) (snd '2))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|singletoninpowerset| (dpi (obj) (dpi (dclass (app '|in| '0)) (pf (app (app '|in| (app '|powerset| '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))))) (lam (lam (app (app (app '|powersetI1| '1) (app (app '|setadjoin| (fst '0)) '|emptyset|)) (app (app '|singletonsubset| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|singletoninpowunion| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (pf (app (app '|in| (app '|powerset| (app (app '|binunion| '2) '1))) (app (app '|setadjoin| (fst '0)) '|emptyset|)))))) (lam (lam (lam (app (app (app (app (app '|subsetE| (app '|powerset| '2)) (app '|powerset| (app (app '|binunion| '2) '1))) (app (app '|setadjoin| (fst '0)) '|emptyset|)) (app (app (app '|powersetsubset| '2) (app (app '|binunion| '2) '1)) (app (app '|binunionLsub| '2) '1))) (app (app '|singletoninpowerset| '2) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|upairsubunion| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (pf (app (app '|subset| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) (app (app '|binunion| '3) '2))))))) (lam (lam (lam (lam (app (app (app '|subsetI2| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) (app (app '|binunion| '3) '2)) (lam (lam (app (app (app (app (app (app '|orE| (app (app '|eq| '1) (fst '3))) (app (app '|eq| '1) (fst '2))) (app (app (app (app '|upairsetE| (fst '3)) (fst '2)) '1) '0)) (app (app '|in| (app (app '|binunion| '5) '4)) '1)) (lam (app (app (app (app (app '|eqE2| '2) (fst '4)) (app '|in| (app (app '|binunion| '6) '5))) '0) (app (app (app (app (app '|subsetE| '6) (app (app '|binunion| '6) '5)) (fst '4)) (app (app '|binunionLsub| '6) '5)) (snd '4))))) (lam (app (app (app (app (app '|eqE2| '2) (fst '3)) (app '|in| (app (app '|binunion| '6) '5))) '0) (app (app (app (app (app '|subsetE| '5) (app (app '|binunion| '6) '5)) (fst '3)) (app (app '|binunionRsub| '6) '5)) (snd '3)))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|upairinpowunion| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (pf (app (app '|in| (app '|powerset| (app (app '|binunion| '3) '2))) (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|)))))))) (lam (lam (lam (lam (app (app (app '|powersetI1| (app (app '|binunion| '3) '2)) (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) (app (app (app (app '|upairsubunion| '3) '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ubforcartprodlem1| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (pf (app (app '|subset| (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))) (app '|powerset| (app (app '|binunion| '3) '2)))))))) (lam (lam (lam (lam (app (app (app '|subsetI2| (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))) (app '|powerset| (app (app '|binunion| '3) '2))) (lam (lam (app (app (app (app (app (app '|orE| (app (app '|eq| '1) (app (app '|setadjoin| (fst '3)) '|emptyset|))) (app (app '|eq| '1) (app (app '|setadjoin| (fst '3)) (app (app '|setadjoin| (fst '2)) '|emptyset|)))) (app (app (app (app '|upairsetE| (app (app '|setadjoin| (fst '3)) '|emptyset|)) (app (app '|setadjoin| (fst '3)) (app (app '|setadjoin| (fst '2)) '|emptyset|))) '1) '0)) (app (app '|in| (app '|powerset| (app (app '|binunion| '5) '4))) '1)) (lam (app (app (app (app (app '|eqE2| '2) (app (app '|setadjoin| (fst '4)) '|emptyset|)) (app '|in| (app '|powerset| (app (app '|binunion| '6) '5)))) '0) (app (app (app '|singletoninpowunion| '6) '5) '4)))) (lam (app (app (app (app (app '|eqE2| '2) (app (app '|setadjoin| (fst '4)) (app (app '|setadjoin| (fst '3)) '|emptyset|))) (app '|in| (app '|powerset| (app (app '|binunion| '6) '5)))) '0) (app (app (app (app '|upairinpowunion| '6) '5) '4) '3))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ubforcartprodlem2| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (pf (app (app '|in| (app '|powerset| (app '|powerset| (app (app '|binunion| '3) '2)))) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|)))))))) (lam (lam (lam (lam (app (app (app '|powersetI1| (app '|powerset| (app (app '|binunion| '3) '2))) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) '|emptyset|)) (app (app '|setadjoin| (app (app '|setadjoin| (fst '1)) (app (app '|setadjoin| (fst '0)) '|emptyset|))) '|emptyset|))) (app (app (app (app '|ubforcartprodlem1| '3) '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ubforcartprodlem3| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (pf (app (app '|in| (app '|powerset| (app '|powerset| (app (app '|binunion| '3) '2)))) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) (lam (lam (lam (lam (app (app (app (app '|kpair#F| (fst '1)) (fst '0)) (app '|in| (app '|powerset| (app '|powerset| (app (app '|binunion| '3) '2))))) (app (app (app (app '|ubforcartprodlem2| '3) '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprod| (dpi (obj) (dpi (obj) (obj))) (lam (lam (app (app '|dsetconstr| (app '|powerset| (app '|powerset| (app (app '|binunion| '1) '0)))) (lam (app (app '|dex| '2) (lam (app (app '|dex| '2) (lam (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodmempair1| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|cartprod| '1) '0))) (pf (app (app '|dex| '2) (lam (app (app '|dex| '2) (lam (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))))) (lam (lam (lam (app (app (app (app '|dsetconstrER| (app '|powerset| (app '|powerset| (app (app '|binunion| '2) '1)))) (lam (app (app '|dex| '3) (lam (app (app '|dex| '3) (lam (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))) (fst '0)) (app (app (app (app '|cartprod#U| '2) '1) (lam (app (app '|in| '0) (fst '1)))) (snd '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodmempair| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|cartprod| '1) '0))) (pf (app '|iskpair| (fst '0)))))) (lam (lam (lam (app (app (app (app (app '|dexE| '2) (lam (app (app '|dex| '2) (lam (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (app (app (app '|cartprodmempair1| '2) '1) '0)) (app '|iskpair| (fst '0))) (lam (lam (app (app (app (app (app '|dexE| '3) (lam (app (app '|eq| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '0)))))) '0) (app '|iskpair| (fst '2))) (lam (lam (app (app (app (app (app '|eqE2| (fst '4)) (fst (app (app '|kpair| (fst '3)) (fst '1)))) '|iskpair|) '0) (snd (app (app '|kpair| (fst '3)) (fst '1))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodmempairc| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|cartprod| '1) '0))) (dclass '|iskpair|)))) (lam (lam (lam (pair (fst '0) (app (app (app '|cartprodmempair| '2) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodpairmemEL| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|cartprod| '3) '2)) (fst (app (app '|kpair| '1) '0)))) (pf (app (app '|in| '4) '2))))))) (lam (lam (lam (lam (lam (app (app (app (app (app '|dexE| '4) (lam (app (app '|dex| '4) (lam (app (app '|eq| (fst (app (app '|kpair| '4) '3))) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (app (app (app '|cartprodmempair1| '4) '3) (pair (fst (app (app '|kpair| '2) '1)) '0))) (app (app '|in| '4) '2)) (lam (lam (app (app (app (app (app '|dexE| '5) (lam (app (app '|eq| (fst (app (app '|kpair| '5) '4))) (fst (app (app '|kpair| (fst '2)) (fst '0)))))) '0) (app (app '|in| '6) '4)) (lam (lam (app (app (app (app (app '|eqE2| '6) (fst '3)) (app '|in| '8)) (app (app (app (app (app '|setukpairinjL| '6) '5) (fst '3)) (fst '1)) '0)) (snd '3))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodpairmemER| (dpi (obj) (dpi (obj) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app '|cartprod| '3) '2)) (fst (app (app '|kpair| '1) '0)))) (pf (app (app '|in| '3) '1))))))) (lam (lam (lam (lam (lam (app (app (app (app (app '|dexE| '4) (lam (app (app '|dex| '4) (lam (app (app '|eq| (fst (app (app '|kpair| '4) '3))) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (app (app (app '|cartprodmempair1| '4) '3) (pair (fst (app (app '|kpair| '2) '1)) '0))) (app (app '|in| '3) '1)) (lam (lam (app (app (app (app (app '|dexE| '5) (lam (app (app '|eq| (fst (app (app '|kpair| '5) '4))) (fst (app (app '|kpair| (fst '2)) (fst '0)))))) '0) (app (app '|in| '5) '3)) (lam (lam (app (app (app (app (app '|eqE2| '5) (fst '1)) (app '|in| '7)) (app (app (app (app (app '|setukpairinjR| '6) '5) (fst '3)) (fst '1)) '0)) (snd '1))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodfstin| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|cartprod| '1) '0))) (pf (app (app '|in| '2) (app '|kfst| (app (app (app '|cartprodmempairc| '2) '1) '0))))))) (lam (lam (lam (app (app (app (app (app '|dexE| '2) (lam (app (app '|dex| '2) (lam (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (app (app (app '|cartprodmempair1| '2) '1) '0)) (app (app '|in| '2) (app '|kfst| (app (app (app '|cartprodmempairc| '2) '1) '0)))) (lam (lam (app (app (app (app (app '|dexE| '3) (lam (app (app '|eq| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '0)))))) '0) (app (app '|in| '4) (app '|kfst| (app (app (app '|cartprodmempairc| '4) '3) '2)))) (lam (lam (app (app (app (app (app (app '|eqCE2| '|iskpair|) (app (app (app '|cartprodmempairc| '6) '5) '4)) (app (app '|kpair| (fst '3)) (fst '1))) (lam (app (app '|in| '7) (app '|kfst| '0)))) (app (app (app (app (app '|cartprodmempairc#F| '6) '5) '4) (lam (app (app '|eq| '0) (fst (app (app '|kpair| (fst '4)) (fst '2)))))) '0)) (app (app (app (app (app '|eqE2| (app '|kfst| (app (app '|kpair| (fst '3)) (fst '1)))) (fst '3)) (app '|in| '6)) (app (app '|kfstpairEq| (fst '3)) (fst '1))) (snd '3)))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodfst| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|cartprod| '1) '0))) (dclass (app '|in| '2))))) (lam (lam (lam (pair (app '|kfst| (app (app (app '|cartprodmempairc| '2) '1) '0)) (app (app (app '|cartprodfstin| '2) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodsndin| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|cartprod| '1) '0))) (pf (app (app '|in| '1) (app '|ksnd| (app (app (app '|cartprodmempairc| '2) '1) '0))))))) (lam (lam (lam (app (app (app (app (app '|dexE| '2) (lam (app (app '|dex| '2) (lam (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (app (app (app '|cartprodmempair1| '2) '1) '0)) (app (app '|in| '1) (app '|ksnd| (app (app (app '|cartprodmempairc| '2) '1) '0)))) (lam (lam (app (app (app (app (app '|dexE| '3) (lam (app (app '|eq| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '0)))))) '0) (app (app '|in| '3) (app '|ksnd| (app (app (app '|cartprodmempairc| '4) '3) '2)))) (lam (lam (app (app (app (app (app (app '|eqCE2| '|iskpair|) (app (app (app '|cartprodmempairc| '6) '5) '4)) (app (app '|kpair| (fst '3)) (fst '1))) (lam (app (app '|in| '6) (app '|ksnd| '0)))) (app (app (app (app (app '|cartprodmempairc#F| '6) '5) '4) (lam (app (app '|eq| '0) (fst (app (app '|kpair| (fst '4)) (fst '2)))))) '0)) (app (app (app (app (app '|eqE2| (app '|ksnd| (app (app '|kpair| (fst '3)) (fst '1)))) (fst '1)) (app '|in| '5)) (app (app '|ksndpairEq| (fst '3)) (fst '1))) (snd '1)))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodsnd| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|cartprod| '1) '0))) (dclass (app '|in| '1))))) (lam (lam (lam (pair (app '|ksnd| (app (app (app '|cartprodmempairc| '2) '1) '0)) (app (app (app '|cartprodsndin| '2) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodpairin| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (pf (app (app '|in| (app (app '|cartprod| '3) '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) (lam (lam (lam (lam (app (app (app (app '|cartprod#F| '3) '2) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '2)) (fst '1)))))) (app (app (app (app '|dsetconstrI| (app '|powerset| (app '|powerset| (app (app '|binunion| '3) '2)))) (lam (app (app '|dex| '4) (lam (app (app '|dex| '4) (lam (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))) (pair (fst (app (app '|kpair| (fst '1)) (fst '0))) (app (app (app (app '|ubforcartprodlem3| '3) '2) '1) '0))) (app (app (app (app '|dexI| '3) (lam (app (app '|dex| '3) (lam (app (app '|eq| (fst (app (app '|kpair| (fst '3)) (fst '2)))) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) '1) (app (app (app (app '|dexI| '2) (lam (app (app '|eq| (fst (app (app '|kpair| (fst '2)) (fst '1)))) (fst (app (app '|kpair| (fst '2)) (fst '0)))))) '0) (app '|eqI| (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodpair| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (dclass (app '|in| (app (app '|cartprod| '3) '2))))))) (lam (lam (lam (lam (pair (fst (app (app '|kpair| (fst '1)) (fst '0))) (app (app (app (app '|cartprodpairin| '3) '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodmempaircEq| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (pf (app (app '|eq| (fst (app (app (app '|cartprodmempairc| '3) '2) (app (app (app (app '|cartprodpair| '3) '2) '1) '0)))) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) (lam (lam (lam (lam (app (app (app (app (app '|cartprodmempairc#F| '3) '2) (app (app (app (app '|cartprodpair| '3) '2) '1) '0)) (lam (app (app '|eq| '0) (fst (app (app '|kpair| (fst '2)) (fst '1)))))) (app (app (app (app (app (app '|cartprodpair#F| '3) '2) '1) '0) (lam (app (app '|eq| '0) (fst (app (app '|kpair| (fst '2)) (fst '1)))))) (app '|eqI| (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodfstpairEq| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (pf (app (app '|eq| (fst (app (app (app '|cartprodfst| '3) '2) (app (app (app (app '|cartprodpair| '3) '2) '1) '0)))) (fst '1))))))) (lam (lam (lam (lam (app (app (app (app (app '|cartprodfst#F| '3) '2) (app (app (app (app '|cartprodpair| '3) '2) '1) '0)) (lam (app (app '|eq| '0) (fst '2)))) (app (app (app (app (app (app '|eqCE2| '|iskpair|) (app (app (app '|cartprodmempairc| '3) '2) (app (app (app (app '|cartprodpair| '3) '2) '1) '0))) (app (app '|kpair| (fst '1)) (fst '0))) (lam (app (app '|eq| (app '|kfst| '0)) (fst '2)))) (app (app (app (app '|cartprodmempaircEq| '3) '2) '1) '0)) (app (app '|kfstpairEq| (fst '1)) (fst '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodsndpairEq| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (pf (app (app '|eq| (fst (app (app (app '|cartprodsnd| '3) '2) (app (app (app (app '|cartprodpair| '3) '2) '1) '0)))) (fst '0))))))) (lam (lam (lam (lam (app (app (app (app (app '|cartprodsnd#F| '3) '2) (app (app (app (app '|cartprodpair| '3) '2) '1) '0)) (lam (app (app '|eq| '0) (fst '1)))) (app (app (app (app (app (app '|eqCE2| '|iskpair|) (app (app (app '|cartprodmempairc| '3) '2) (app (app (app (app '|cartprodpair| '3) '2) '1) '0))) (app (app '|kpair| (fst '1)) (fst '0))) (lam (app (app '|eq| (app '|ksnd| '0)) (fst '1)))) (app (app (app (app '|cartprodmempaircEq| '3) '2) '1) '0)) (app (app '|ksndpairEq| (fst '1)) (fst '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|cartprodpairsurjEq| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|cartprod| '1) '0))) (pf (app (app '|eq| (fst (app (app (app (app '|cartprodpair| '2) '1) (app (app (app '|cartprodfst| '2) '1) '0)) (app (app (app '|cartprodsnd| '2) '1) '0)))) (fst '0)))))) (lam (lam (lam (app (app (app (app (app '|dexE| '2) (lam (app (app '|dex| '2) (lam (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (app (app (app '|cartprodmempair1| '2) '1) '0)) (app (app '|eq| (fst (app (app (app (app '|cartprodpair| '2) '1) (app (app (app '|cartprodfst| '2) '1) '0)) (app (app (app '|cartprodsnd| '2) '1) '0)))) (fst '0))) (lam (lam (app (app (app (app (app '|dexE| '3) (lam (app (app '|eq| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '0)))))) '0) (app (app '|eq| (fst (app (app (app (app '|cartprodpair| '4) '3) (app (app (app '|cartprodfst| '4) '3) '2)) (app (app (app '|cartprodsnd| '4) '3) '2)))) (fst '2))) (lam (lam (app (app (app (app (app (app '|eqCE| (app '|in| (app (app '|cartprod| '6) '5))) (app (app (app (app '|cartprodpair| '6) '5) '3) '1)) '4) (lam (app (app '|eq| (fst (app (app (app (app '|cartprodpair| '7) '6) (app (app (app '|cartprodfst| '7) '6) '0)) (app (app (app '|cartprodsnd| '7) '6) '0)))) (fst '0)))) (app (app (app (app (app '|symtrans1eq| (fst (app (app (app (app '|cartprodpair| '6) '5) '3) '1))) (fst (app (app '|kpair| (fst '3)) (fst '1)))) (fst '4)) (app (app (app (app (app (app '|cartprodpair#F| '6) '5) '3) '1) (lam (app (app '|eq| '0) (fst (app (app '|kpair| (fst '4)) (fst '2)))))) (app '|eqI| (fst (app (app '|kpair| (fst '3)) (fst '1)))))) '0)) (app (app (app (app (app (app '|eqCE2| (app '|in| '5)) (app (app (app '|cartprodsnd| '6) '5) (app (app (app (app '|cartprodpair| '6) '5) '3) '1))) '1) (lam (app (app '|eq| (fst (app (app (app (app '|cartprodpair| '7) '6) (app (app (app '|cartprodfst| '7) '6) (app (app (app (app '|cartprodpair| '7) '6) '4) '2))) '0))) (fst (app (app (app (app '|cartprodpair| '7) '6) '4) '2))))) (app (app (app (app '|cartprodsndpairEq| '6) '5) '3) '1)) (app (app (app (app (app (app '|eqCE2| (app '|in| '6)) (app (app (app '|cartprodfst| '6) '5) (app (app (app (app '|cartprodpair| '6) '5) '3) '1))) '3) (lam (app (app '|eq| (fst (app (app (app (app '|cartprodpair| '7) '6) '0) '2))) (fst (app (app (app (app '|cartprodpair| '7) '6) '4) '2))))) (app (app (app (app '|cartprodfstpairEq| '6) '5) '3) '1)) (app '|eqI| (fst (app (app (app (app '|cartprodpair| '6) '5) '3) '1))))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dpsetconstr| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (prop))) (obj)))) (lam (lam (lam (app (app '|dsetconstr| (app (app '|cartprod| '2) '1)) (lam (app (app '|dex| '3) (lam (app (app '|dex| '3) (lam (app (app '|and| (app (app '3 '1) '0)) (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dpsetconstrSub| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (prop))) (pf (app (app '|subset| (app (app (app '|dpsetconstr| '2) '1) '0)) (app (app '|cartprod| '2) '1)))))) (lam (lam (lam (app (app (app '|subsetI2| (app (app (app '|dpsetconstr| '2) '1) '0)) (app (app '|cartprod| '2) '1)) (lam (lam (app (app (app (app '|dsetconstrEL| (app (app '|cartprod| '4) '3)) (lam (app (app '|dex| '5) (lam (app (app '|dex| '5) (lam (app (app '|and| (app (app '5 '1) '0)) (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))))) '1) (app (app (app (app (app '|dpsetconstr#U| '4) '3) '2) (lam (app (app '|in| '0) '2))) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dpsetconstrI| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (prop))) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '2)) (dpi (pf (app (app '2 '1) '0)) (pf (app (app '|in| (app (app (app '|dpsetconstr| '5) '4) '3)) (fst (app (app '|kpair| (fst '2)) (fst '1))))))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app '|dpsetconstr#F| '5) '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '3)) (fst '2)))))) (app (app (app (app '|dsetconstrI| (app (app '|cartprod| '5) '4)) (lam (app (app '|dex| '6) (lam (app (app '|dex| '6) (lam (app (app '|and| (app (app '6 '1) '0)) (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))))) (pair (fst (app (app '|kpair| (fst '2)) (fst '1))) (app (app (app (app '|cartprodpairin| '5) '4) '2) '1))) (app (app (app (app '|dexI| '5) (lam (app (app '|dex| '5) (lam (app (app '|and| (app (app '5 '1) '0)) (app (app '|eq| (fst (app (app '|kpair| (fst '4)) (fst '3)))) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) '2) (app (app (app (app '|dexI| '4) (lam (app (app '|and| (app (app '4 '3) '0)) (app (app '|eq| (fst (app (app '|kpair| (fst '3)) (fst '2)))) (fst (app (app '|kpair| (fst '3)) (fst '0))))))) '1) (app (app (app (app '|andI| (app (app '3 '2) '1)) (app (app '|eq| (fst (app (app '|kpair| (fst '2)) (fst '1)))) (fst (app (app '|kpair| (fst '2)) (fst '1))))) '0) (app (app (app (app '|setext| (fst (app (app '|kpair| (fst '2)) (fst '1)))) (fst (app (app '|kpair| (fst '2)) (fst '1)))) (lam (lam '0))) (lam (lam '0)))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dpsetconstrEL1| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (prop))) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app (app '|dpsetconstr| '4) '3) '2)) (fst (app (app '|kpair| '1) '0)))) (pf (app (app '|in| '5) '2)))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app '|cartprodpairmemEL| '5) '4) '2) '1) (app (app (app (app '|dsetconstrEL| (app (app '|cartprod| '5) '4)) (lam (app (app '|dex| '6) (lam (app (app '|dex| '6) (lam (app (app '|and| (app (app '6 '1) '0)) (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))))) (fst (app (app '|kpair| '2) '1))) (app (app (app (app (app '|dpsetconstr#U| '5) '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| '3) '2))))) '0))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dpsetconstrEL2| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (prop))) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app (app '|dpsetconstr| '4) '3) '2)) (fst (app (app '|kpair| '1) '0)))) (pf (app (app '|in| '4) '1)))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app '|cartprodpairmemER| '5) '4) '2) '1) (app (app (app (app '|dsetconstrEL| (app (app '|cartprod| '5) '4)) (lam (app (app '|dex| '6) (lam (app (app '|dex| '6) (lam (app (app '|and| (app (app '6 '1) '0)) (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))))) (fst (app (app '|kpair| '2) '1))) (app (app (app (app (app '|dpsetconstr#U| '5) '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| '3) '2))))) '0))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|dpsetconstrER| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (prop))) (dpi (obj) (dpi (obj) (dpi (pf (app (app '|in| (app (app (app '|dpsetconstr| '4) '3) '2)) (fst (app (app '|kpair| '1) '0)))) (pf (app (app '3 (pair '2 (app (app (app (app (app (app '|dpsetconstrEL1| '5) '4) '3) '2) '1) '0))) (pair '1 (app (app (app (app (app (app '|dpsetconstrEL2| '5) '4) '3) '2) '1) '0)))))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app '|dexE| '5) (lam (app (app '|dex| '5) (lam (app (app '|and| (app (app '5 '1) '0)) (app (app '|eq| (fst (app (app '|kpair| '4) '3))) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) (app (app (app (app '|dsetconstrER| (app (app '|cartprod| '5) '4)) (lam (app (app '|dex| '6) (lam (app (app '|dex| '6) (lam (app (app '|and| (app (app '6 '1) '0)) (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))))) (fst (app (app '|kpair| '2) '1))) (app (app (app (app (app '|dpsetconstr#U| '5) '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| '3) '2))))) '0))) (app (app '3 (pair '2 (app (app (app (app (app (app '|dpsetconstrEL1| '5) '4) '3) '2) '1) '0))) (pair '1 (app (app (app (app (app (app '|dpsetconstrEL2| '5) '4) '3) '2) '1) '0)))) (lam (lam (app (app (app (app (app '|dexE| '6) (lam (app (app '|and| (app (app '6 '2) '0)) (app (app '|eq| (fst (app (app '|kpair| '5) '4))) (fst (app (app '|kpair| (fst '2)) (fst '0))))))) '0) (app (app '5 (pair '4 (app (app (app (app (app (app '|dpsetconstrEL1| '7) '6) '5) '4) '3) '2))) (pair '3 (app (app (app (app (app (app '|dpsetconstrEL2| '7) '6) '5) '4) '3) '2)))) (lam (lam (app (app (app (app (app (app '|eqCE2| (app '|in| '8)) (pair '5 (app (app (app (app (app (app '|dpsetconstrEL2| '9) '8) '7) '6) '5) '4))) '1) (app '7 (pair '6 (app (app (app (app (app (app '|dpsetconstrEL1| '9) '8) '7) '6) '5) '4)))) (app (app (app (app (app '|setukpairinjR| '6) '5) (fst '3)) (fst '1)) (app (app (app '|andER| (app (app '7 '3) '1)) (app (app '|eq| (fst (app (app '|kpair| '6) '5))) (fst (app (app '|kpair| (fst '3)) (fst '1))))) '0))) (app (app (app (app (app (app '|eqCE2| (app '|in| '9)) (pair '6 (app (app (app (app (app (app '|dpsetconstrEL1| '9) '8) '7) '6) '5) '4))) '3) (lam (app (app '8 '0) '2))) (app (app (app (app (app '|setukpairinjL| '6) '5) (fst '3)) (fst '1)) (app (app (app '|andER| (app (app '7 '3) '1)) (app (app '|eq| (fst (app (app '|kpair| '6) '5))) (fst (app (app '|kpair| (fst '3)) (fst '1))))) '0))) (app (app (app '|andEL| (app (app '7 '3) '1)) (app (app '|eq| (fst (app (app '|kpair| '6) '5))) (fst (app (app '|kpair| (fst '3)) (fst '1))))) '0))))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln| (dpi (obj) (dpi (obj) (dpi (obj) (prop)))) (lam (lam (lam (app (app '|subset| '0) (app (app '|cartprod| '2) '1))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setOfPairsIsBReln| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '1)) (prop))) (pf (app (app (app '|breln| '2) '1) (app (app (app '|dpsetconstr| '2) '1) '0)))))) (lam (lam (lam (app (app (app (app '|breln#F| '2) '1) (app (app (app '|dpsetconstr| '2) '1) '0)) (app (app (app '|dpsetconstrSub| '2) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|brelnall1| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|breln| '1) '0)) (dpi (dpi (obj) (prop)) (dpi (dpi (dclass (app '|in| '3)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app '3 (fst (app (app '|kpair| (fst '2)) (fst '1)))))))) (pf (app (app '|dall| (fst '2)) (lam (app '2 (fst '0)))))))))) (lam (lam (lam (lam (lam (app (app (app '|dallI| (fst '2)) (lam (app '2 (fst '0)))) (lam (app (app (app (app (app '|dexE| '5) (lam (app (app '|dex| '5) (lam (app (app '|eq| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (app (app (app '|cartprodmempair1| '5) '4) (pair (fst '0) (app (app (app (app (app '|subsetE| (fst '3)) (app (app '|cartprod| '5) '4)) (fst '0)) (app (app (app (app '|breln#U| '5) '4) (fst '3)) (snd '3))) (snd '0))))) (app '2 (fst '0))) (lam (lam (app (app (app (app (app '|dexE| '6) (lam (app (app '|eq| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '0)))))) '0) (app '4 (fst '2))) (lam (lam (app (app (app (app (app '|eqE2| (fst '4)) (fst (app (app '|kpair| (fst '3)) (fst '1)))) '6) '0) (app (app (app '5 '3) '1) (app (app (app (app (app '|eqE| (fst '4)) (fst (app (app '|kpair| (fst '3)) (fst '1)))) (app '|in| (fst '7))) '0) (snd '4))))))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|brelnall2| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|breln| '1) '0)) (dpi (dpi (obj) (prop)) (dpi (pf (app (app '|dall| '3) (lam (app (app '|dall| '3) (lam (app (app '|imp| (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (app '2 (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))) (pf (app (app '|dall| (fst '2)) (lam (app '2 (fst '0)))))))))) (lam (lam (lam (lam (lam (app (app (app (app (app '|brelnall1| '4) '3) '2) '1) (lam (lam (app (app (app '|impE| (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (app '3 (fst (app (app '|kpair| (fst '1)) (fst '0))))) (app (app (app (app '|dallE| '5) (lam (app (app '|imp| (app (app '|in| (fst '5)) (fst (app (app '|kpair| (fst '2)) (fst '0))))) (app '4 (fst (app (app '|kpair| (fst '2)) (fst '0))))))) (app (app (app (app '|dallE| '6) (lam (app (app '|dall| '6) (lam (app (app '|imp| (app (app '|in| (fst '6)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (app '5 (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) '2) '1)) '0)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|subbreln| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|breln| '1) '0)) (dpi (dclass (app (app '|breln| '2) '1)) (dpi (dpi (dclass (app '|in| '3)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1)))))))) (pf (app (app '|subset| (fst '2)) (fst '1)))))))) (lam (lam (lam (lam (lam (app (app (app '|subsetI1| (fst '2)) (fst '1)) (app (app (app '|dallE| (fst '2)) (lam (app (app '|in| (fst '2)) (fst '0)))) (app (app (app (app (app '|brelnall1| '4) '3) '2) (app '|in| (fst '1))) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqbreln| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|breln| '1) '0)) (dpi (dclass (app (app '|breln| '2) '1)) (dpi (dpi (dclass (app '|in| '3)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1)))))))) (dpi (dpi (dclass (app '|in| '4)) (dpi (dclass (app '|in| '4)) (dpi (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|in| (fst '5)) (fst (app (app '|kpair| (fst '2)) (fst '1)))))))) (pf (app (app '|eq| (fst '3)) (fst '2))))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app '|setextsub| (fst '3)) (fst '2)) (app (app (app (app (app '|subbreln| '5) '4) '3) '2) '1)) (app (app (app (app (app '|subbreln| '5) '4) '2) '3) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1| (dpi (obj) (dpi (obj) (prop))) (lam (app (app '|breln| '0) '0)) '("AUTO") '("Chad Edward Brown"))

(newabbrev '|breln12breln| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dclass (app (app '|breln| '1) '1)))) (lam (lam (pair (fst '0) (app (app (app '|breln1#U| '1) (fst '0)) (snd '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|setOfPairsIsBReln1| (dpi (obj) (dpi (dpi (dclass (app '|in| '0)) (dpi (dclass (app '|in| '1)) (prop))) (pf (app (app '|breln1| '1) (app (app (app '|dpsetconstr| '1) '1) '0))))) (lam (lam (app (app (app '|breln1#F| '1) (app (app (app '|dpsetconstr| '1) '1) '0)) (app (app (app '|setOfPairsIsBReln| '1) '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1all1| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dpi (obj) (prop)) (dpi (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app '3 (fst (app (app '|kpair| (fst '2)) (fst '1)))))))) (pf (app (app '|dall| (fst '2)) (lam (app '2 (fst '0))))))))) (lam (lam (app (app (app '|brelnall1| '1) '1) (pair (fst '0) (app (app (app '|breln1#U| '1) (fst '0)) (snd '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1all2| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dpi (obj) (prop)) (dpi (pf (app (app '|dall| '2) (lam (app (app '|dall| '3) (lam (app (app '|imp| (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (app '2 (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))) (pf (app (app '|dall| (fst '2)) (lam (app '2 (fst '0))))))))) (lam (lam (app (app (app '|brelnall2| '1) '1) (pair (fst '0) (app (app (app '|breln1#U| '1) (fst '0)) (snd '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|subbreln1| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dpi (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1)))))))) (pf (app (app '|subset| (fst '2)) (fst '1))))))) (lam (lam (lam (app (app (app (app '|subbreln| '2) '2) (pair (fst '1) (app (app (app '|breln1#U| '2) (fst '1)) (snd '1)))) (pair (fst '0) (app (app (app '|breln1#U| '2) (fst '0)) (snd '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eqbreln1| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dpi (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1)))))))) (dpi (dpi (dclass (app '|in| '3)) (dpi (dclass (app '|in| '4)) (dpi (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|in| (fst '5)) (fst (app (app '|kpair| (fst '2)) (fst '1)))))))) (pf (app (app '|eq| (fst '3)) (fst '2)))))))) (lam (lam (lam (app (app (app (app '|eqbreln| '2) '2) (pair (fst '1) (app (app (app '|breln1#U| '2) (fst '1)) (snd '1)))) (pair (fst '0) (app (app (app '|breln1#U| '2) (fst '0)) (snd '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1invset| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (obj))) (lam (lam (app (app (app '|dpsetconstr| '1) '1) (lam (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '0)) (fst '1))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1invprop| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (pf (app (app '|breln1| '1) (app (app '|breln1invset| '1) '0))))) (lam (lam (app (app (app (app '|breln1invset#F| '1) '0) (app '|breln1| '1)) (app (app '|setOfPairsIsBReln1| '1) (lam (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '0)) (fst '1)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1inv| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dclass (app '|breln1| '1)))) (lam (lam (pair (app (app '|breln1invset| '1) '0) (app (app '|breln1invprop| '1) '0)))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1invI| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '2)) (dpi (pf (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|in| (fst (app (app '|breln1inv| '4) '3))) (fst (app (app '|kpair| (fst '1)) (fst '2)))))))))) (lam (lam (lam (lam (lam (app (app (app (app '|breln1inv#F| '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '2)) (fst '3)))))) (app (app (app (app '|breln1invset#F| '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '2)) (fst '3)))))) (app (app (app (app (app (app '|dpsetconstrI| '4) '4) (lam (lam (app (app '|in| (fst '5)) (fst (app (app '|kpair| (fst '0)) (fst '1))))))) '1) '2) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1invE| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|in| '1)) (dpi (dclass (app '|in| '2)) (dpi (pf (app (app '|in| (fst (app (app '|breln1inv| '3) '2))) (fst (app (app '|kpair| (fst '0)) (fst '1))))) (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1)))))))))) (lam (lam (lam (lam (lam (app (app (app (app (app (app '|dpsetconstrER| '4) '4) (lam (lam (app (app '|in| (fst '5)) (fst (app (app '|kpair| (fst '0)) (fst '1))))))) (fst '1)) (fst '2)) (app (app (app (app '|breln1invset#U| '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '2)) (fst '3)))))) (app (app (app (app '|breln1inv#U| '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '2)) (fst '3)))))) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1compset| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (obj)))) (lam (lam (lam (app (app (app '|dpsetconstr| '2) '2) (lam (lam (app (app '|dex| '4) (lam (app (app '|and| (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '2)) (fst '0))))) (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '0)) (fst '1))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1compprop| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (pf (app (app '|breln1| '2) (app (app (app '|breln1compset| '2) '1) '0)))))) (lam (lam (lam (app (app (app (app (app '|breln1compset#F| '2) '1) '0) (app '|breln1| '2)) (app (app '|setOfPairsIsBReln1| '2) (lam (lam (app (app '|dex| '4) (lam (app (app '|and| (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '2)) (fst '0))))) (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '0)) (fst '1)))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1comp| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dclass (app '|breln1| '2))))) (lam (lam (lam (pair (app (app (app '|breln1compset| '2) '1) '0) (app (app (app '|breln1compprop| '2) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1compI| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (dclass (app '|in| '4)) (dpi (pf (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '2)) (fst '0))))) (dpi (pf (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '1)) (fst '2))))) (pf (app (app '|in| (fst (app (app (app '|breln1comp| '7) '6) '5))) (fst (app (app '|kpair| (fst '4)) (fst '3))))))))))))) (lam (lam (lam (lam (lam (lam (lam (lam (app (app (app (app (app '|breln1comp#F| '7) '6) '5) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '5)) (fst '4)))))) (app (app (app (app (app '|breln1compset#F| '7) '6) '5) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '5)) (fst '4)))))) (app (app (app (app (app (app '|dpsetconstrI| '7) '7) (lam (lam (app (app '|dex| '9) (lam (app (app '|and| (app (app '|in| (fst '9)) (fst (app (app '|kpair| (fst '2)) (fst '0))))) (app (app '|in| (fst '8)) (fst (app (app '|kpair| (fst '0)) (fst '1)))))))))) '4) '3) (app (app (app (app '|dexI| '7) (lam (app (app '|and| (app (app '|in| (fst '7)) (fst (app (app '|kpair| (fst '5)) (fst '0))))) (app (app '|in| (fst '6)) (fst (app (app '|kpair| (fst '0)) (fst '4))))))) '2) (app (app (app (app '|andI| (app (app '|in| (fst '6)) (fst (app (app '|kpair| (fst '4)) (fst '2))))) (app (app '|in| (fst '5)) (fst (app (app '|kpair| (fst '2)) (fst '3))))) '1) '0))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1compE| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst (app (app (app '|breln1comp| '4) '3) '2))) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|dex| '5) (lam (app (app '|and| (app (app '|in| (fst '5)) (fst (app (app '|kpair| (fst '3)) (fst '0))))) (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '0)) (fst '2)))))))))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app (app '|dpsetconstrER| '5) '5) (lam (lam (app (app '|dex| '7) (lam (app (app '|and| (app (app '|in| (fst '7)) (fst (app (app '|kpair| (fst '2)) (fst '0))))) (app (app '|in| (fst '6)) (fst (app (app '|kpair| (fst '0)) (fst '1)))))))))) (fst '2)) (fst '1)) (app (app (app (app (app '|breln1compset#U| '5) '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '3)) (fst '2)))))) (app (app (app (app (app '|breln1comp#U| '5) '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '3)) (fst '2)))))) '0))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1compEex| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst (app (app (app '|breln1comp| '4) '3) '2))) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (dpi (prop) (dpi (dpi (dclass (app '|in| '6)) (dpi (pf (app (app '|in| (fst '6)) (fst (app (app '|kpair| (fst '4)) (fst '0))))) (dpi (pf (app (app '|in| (fst '6)) (fst (app (app '|kpair| (fst '1)) (fst '4))))) (pf '3)))) (pf '1))))))))) (lam (lam (lam (lam (lam (lam (lam (lam (app (app (app (app (app '|dexE| '7) (lam (app (app '|and| (app (app '|in| (fst '7)) (fst (app (app '|kpair| (fst '5)) (fst '0))))) (app (app '|in| (fst '6)) (fst (app (app '|kpair| (fst '0)) (fst '4))))))) (app (app (app (app (app (app '|breln1compE| '7) '6) '5) '4) '3) '2)) '1) (lam (lam (app (app (app '2 '1) (app (app (app '|andEL| (app (app '|in| (fst '8)) (fst (app (app '|kpair| (fst '6)) (fst '1))))) (app (app '|in| (fst '7)) (fst (app (app '|kpair| (fst '1)) (fst '5))))) '0)) (app (app (app '|andER| (app (app '|in| (fst '8)) (fst (app (app '|kpair| (fst '6)) (fst '1))))) (app (app '|in| (fst '7)) (fst (app (app '|kpair| (fst '1)) (fst '5))))) '0))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1unionprop| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (pf (app (app '|breln1| '2) (app (app '|binunion| (fst '1)) (fst '0))))))) (lam (lam (lam (app (app (app '|breln1#F| '2) (app (app '|binunion| (fst '1)) (fst '0))) (app (app (app (app '|breln#F| '2) '2) (app (app '|binunion| (fst '1)) (fst '0))) (app (app (app '|subsetI2| (app (app '|binunion| (fst '1)) (fst '0))) (app (app '|cartprod| '2) '2)) (lam (lam (app (app (app (app (app (app '|orE| (app (app '|in| (fst '3)) '1)) (app (app '|in| (fst '2)) '1)) (app (app (app (app '|binunionE| (fst '3)) (fst '2)) '1) '0)) (app (app '|in| (app (app '|cartprod| '4) '4)) '1)) (app (app (app (app '|subsetE| (fst '3)) (app (app '|cartprod| '4) '4)) '1) (app (app (app (app '|breln#U| '4) '4) (fst '3)) (app (app (app '|breln1#U| '4) (fst '3)) (snd '3))))) (app (app (app (app '|subsetE| (fst '2)) (app (app '|cartprod| '4) '4)) '1) (app (app (app (app '|breln#U| '4) '4) (fst '2)) (app (app (app '|breln1#U| '4) (fst '2)) (snd '2))))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1union| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dclass (app '|breln1| '2))))) (lam (lam (lam (pair (app (app '|binunion| (fst '1)) (fst '0)) (app (app (app '|breln1unionprop| '2) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1unionIL| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|in| (fst (app (app (app '|breln1union| '5) '4) '3))) (fst (app (app '|kpair| (fst '2)) (fst '1))))))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app '|breln1union#F| '5) '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '3)) (fst '2)))))) (app (app (app (app '|binunionIL| (fst '4)) (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1)))) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1unionIR| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|in| (fst (app (app (app '|breln1union| '5) '4) '3))) (fst (app (app '|kpair| (fst '2)) (fst '1))))))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app '|breln1union#F| '5) '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '3)) (fst '2)))))) (app (app (app (app '|binunionIR| (fst '4)) (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1)))) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1unionI| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|or| (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))) (pf (app (app '|in| (fst (app (app (app '|breln1union| '5) '4) '3))) (fst (app (app '|kpair| (fst '2)) (fst '1))))))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app (app '|orE| (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '2)) (fst '1))))) (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1))))) '0) (app (app '|in| (fst (app (app (app '|breln1union| '5) '4) '3))) (fst (app (app '|kpair| (fst '2)) (fst '1))))) (app (app (app (app (app '|breln1unionIL| '5) '4) '3) '2) '1)) (app (app (app (app (app '|breln1unionIR| '5) '4) '3) '2) '1)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1unionE| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst (app (app (app '|breln1union| '4) '3) '2))) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|or| (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '2)) (fst '1))))) (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1)))))))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app '|binunionE| (fst '4)) (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1)))) (app (app (app (app (app '|breln1union#U| '5) '4) '3) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '3)) (fst '2)))))) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|breln1unionEcases| (dpi (obj) (dpi (dclass (app '|breln1| '0)) (dpi (dclass (app '|breln1| '1)) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|in| (fst (app (app (app '|breln1union| '4) '3) '2))) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (dpi (prop) (dpi (dpi (pf (app (app '|in| (fst '5)) (fst (app (app '|kpair| (fst '3)) (fst '2))))) (pf '1)) (dpi (dpi (pf (app (app '|in| (fst '5)) (fst (app (app '|kpair| (fst '4)) (fst '3))))) (pf '2)) (pf '2)))))))))) (lam (lam (lam (lam (lam (lam (app (app (app '|orE| (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '2)) (fst '1))))) (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '1))))) (app (app (app (app (app (app '|breln1unionE| '5) '4) '3) '2) '1) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|func| (dpi (obj) (dpi (obj) (dpi (obj) (prop)))) (lam (lam (lam (app (app '|and| (app (app (app '|breln| '2) '1) '0)) (app (app '|dall| '2) (lam (app (app '|ex1| '2) (lam (app (app '|in| '2) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|funcImageSingleton| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|func| '1) '0)) (dpi (dclass (app '|in| '2)) (pf (app '|singleton| (app (app '|dsetconstr| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))))))) (lam (lam (lam (lam (app (app (app '|ex1#U| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))) (app (app (app (app '|dallE| '3) (lam (app (app '|ex1| '3) (lam (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (app (app (app '|andER| (app (app (app '|breln| '3) '2) (fst '1))) (app (app '|dall| '3) (lam (app (app '|ex1| '3) (lam (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) (app (app (app (app '|func#U| '3) '2) (fst '1)) (snd '1)))) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|apProp| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|func| '1) '0)) (dpi (dclass (app '|in| '2)) (pf (app (app '|in| '2) (fst (app '|the| (pair (app (app '|dsetconstr| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))) (app (app (app (app '|funcImageSingleton| '3) '2) '1) '0)))))))))) (lam (lam (lam (lam (app (app (app (app '|dsetconstrEL| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))) (fst (app '|the| (pair (app (app '|dsetconstr| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))) (app (app (app (app '|funcImageSingleton| '3) '2) '1) '0))))) (snd (app '|the| (pair (app (app '|dsetconstr| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))) (app (app (app (app '|funcImageSingleton| '3) '2) '1) '0))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ap| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|func| '1) '0)) (dpi (dclass (app '|in| '2)) (dclass (app '|in| '2)))))) (lam (lam (lam (lam (pair (fst (app '|the| (pair (app (app '|dsetconstr| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))) (app (app (app (app '|funcImageSingleton| '3) '2) '1) '0)))) (app (app (app (app '|apProp| '3) '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|lamProp| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dclass (app '|in| '1))) (pf (app (app (app '|func| '2) '1) (app (app (app '|dpsetconstr| '2) '1) (lam (lam (app (app '|eq| (fst (app '2 '1))) (fst '0)))))))))) (lam (lam (lam (app (app (app (app '|func#F| '2) '1) (app (app (app '|dpsetconstr| '2) '1) (lam (lam (app (app '|eq| (fst (app '2 '1))) (fst '0)))))) (app (app (app (app '|andI| (app (app (app '|breln| '2) '1) (app (app (app '|dpsetconstr| '2) '1) (lam (lam (app (app '|eq| (fst (app '2 '1))) (fst '0))))))) (app (app '|dall| '2) (lam (app (app '|ex1| '2) (lam (app (app '|in| (app (app (app '|dpsetconstr| '4) '3) (lam (lam (app (app '|eq| (fst (app '4 '1))) (fst '0)))))) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) (app (app (app '|setOfPairsIsBReln| '2) '1) (lam (lam (app (app '|eq| (fst (app '2 '1))) (fst '0)))))) (app (app (app '|dallI| '2) (lam (app (app '|ex1| '2) (lam (app (app '|in| (app (app (app '|dpsetconstr| '4) '3) (lam (lam (app (app '|eq| (fst (app '4 '1))) (fst '0)))))) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (lam (app (app (app (app (app '|ex1I| '2) (lam (app (app '|in| (app (app (app '|dpsetconstr| '4) '3) (lam (lam (app (app '|eq| (fst (app '4 '1))) (fst '0)))))) (fst (app (app '|kpair| (fst '1)) (fst '0)))))) (app '1 '0)) (app (app (app (app (app (app '|dpsetconstrI| '3) '2) (lam (lam (app (app '|eq| (fst (app '3 '1))) (fst '0))))) '0) (app '1 '0)) (app '|eqI| (fst (app '1 '0))))) (lam (lam (app (app (app '|symeq| (fst (app '3 '2))) (fst '1)) (app (app (app (app (app (app '|dpsetconstrER| '5) '4) (lam (lam (app (app '|eq| (fst (app '5 '1))) (fst '0))))) (fst '2)) (fst '1)) '0)))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|lam| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dclass (app '|in| '1))) (dclass (app (app '|func| '2) '1))))) (lam (lam (lam (pair (app (app (app '|dpsetconstr| '2) '1) (lam (lam (app (app '|eq| (fst (app '2 '1))) (fst '0))))) (app (app (app '|lamProp| '2) '1) '0))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|funcSet| (dpi (obj) (dpi (obj) (obj))) (lam (lam (app (app '|dsetconstr| (app '|powerset| (app (app '|cartprod| '1) '0))) (lam (app (app (app '|func| '2) '1) (fst '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|funcinfuncset| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|func| '1) '0)) (pf (app (app '|in| (app (app '|funcSet| '2) '1)) (fst '0)))))) (lam (lam (lam (app (app (app (app '|funcSet#F| '2) '1) (lam (app (app '|in| '0) (fst '1)))) (app (app (app (app '|dsetconstrI| (app '|powerset| (app (app '|cartprod| '2) '1))) (lam (app (app (app '|func| '3) '2) (fst '0)))) (pair (fst '0) (app (app (app '|powersetI1| (app (app '|cartprod| '2) '1)) (fst '0)) (app (app (app (app '|breln#U| '2) '1) (fst '0)) (app (app (app '|andEL| (app (app (app '|breln| '2) '1) (fst '0))) (app (app '|dall| '2) (lam (app (app '|ex1| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) (app (app (app (app '|func#U| '2) '1) (fst '0)) (snd '0))))))) (snd '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|infuncsetfunc| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '1) '0))) (pf (app (app (app '|func| '2) '1) (fst '0)))))) (lam (lam (lam (app (app (app (app '|dsetconstrER| (app '|powerset| (app (app '|cartprod| '2) '1))) (lam (app (app (app '|func| '3) '2) (fst '0)))) (fst '0)) (app (app (app (app '|funcSet#U| '2) '1) (lam (app (app '|in| '0) (fst '1)))) (snd '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ap2| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '1) '0))) (dpi (dclass (app '|in| '2)) (dclass (app '|in| '2)))))) (lam (lam (lam (app (app (app '|ap| '2) '1) (pair (fst '0) (app (app (app '|infuncsetfunc| '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ap2apEq1| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '1) '0))) (dpi (dclass (app '|in| '2)) (pf (app (app '|eq| (fst (app (app (app (app '|ap2| '3) '2) '1) '0))) (fst (app (app (app (app '|ap| '3) '2) (pair (fst '1) (app (app (app '|infuncsetfunc| '3) '2) '1))) '0)))))))) (lam (lam (lam (lam (app (app (app (app (app (app '|ap2#F| '3) '2) '1) '0) (lam (app (app '|eq| '0) (fst (app (app (app (app '|ap| '4) '3) (pair (fst '2) (app (app (app '|infuncsetfunc| '4) '3) '2))) '1))))) (app '|eqI| (fst (app (app (app (app '|ap| '3) '2) (pair (fst '1) (app (app (app '|infuncsetfunc| '3) '2) '1))) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|ap2apEq2| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|func| '1) '0)) (dpi (dclass (app '|in| '2)) (pf (app (app '|eq| (fst (app (app (app (app '|ap2| '3) '2) (pair (fst '1) (app (app (app '|funcinfuncset| '3) '2) '1))) '0))) (fst (app (app (app (app '|ap| '3) '2) '1) '0)))))))) (lam (lam (lam (lam (app (app (app (app (app (app '|ap2#F| '3) '2) (pair (fst '1) (app (app (app '|funcinfuncset| '3) '2) '1))) '0) (lam (app (app '|eq| '0) (fst (app (app (app (app '|ap| '4) '3) '2) '1))))) (app '|eqI| (fst (app (app (app (app '|ap| '3) '2) '1) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|lam2| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dclass (app '|in| '1))) (dclass (app '|in| (app (app '|funcSet| '2) '1)))))) (lam (lam (lam (pair (fst (app (app (app '|lam| '2) '1) '0)) (app (app (app '|funcinfuncset| '2) '1) (app (app (app '|lam| '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|lam2lamEq| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dclass (app '|in| '1))) (pf (app (app '|eq| (fst (app (app (app '|lam2| '2) '1) '0))) (fst (app (app (app '|lam| '2) '1) '0))))))) (lam (lam (lam (app (app (app (app (app '|lam2#F| '2) '1) '0) (lam (app (app '|eq| '0) (fst (app (app (app '|lam| '3) '2) '1))))) (app '|eqI| (fst (app (app (app '|lam| '2) '1) '0))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|funcGraphProp1| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|func| '1) '0)) (dpi (dclass (app '|in| '2)) (pf (app (app '|in| (fst '1)) (fst (app (app '|kpair| (fst '0)) (fst (app (app (app (app '|ap| '3) '2) '1) '0)))))))))) (lam (lam (lam (lam (app (app (app (app '|dsetconstrER| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))) (fst (app (app (app (app '|ap| '3) '2) '1) '0))) (app (app (app (app (app (app '|ap#F| '3) '2) '1) '0) (app '|in| (app (app '|dsetconstr| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (snd (app '|the| (pair (app (app '|dsetconstr| '2) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))) (app (app (app (app '|funcImageSingleton| '3) '2) '1) '0)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|funcGraphProp2| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|func| '1) '0)) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '2)) (dpi (pf (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|eq| (fst (app (app (app (app '|ap| '5) '4) '3) '2))) (fst '1))))))))) (lam (lam (lam (lam (lam (app (app (app (app (app (app '|ex1E2| '3) (lam (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '2)) (fst '0)))))) (app (app (app (app '|dallE| '4) (lam (app (app '|ex1| '4) (lam (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '1)) (fst '0)))))))) (app (app (app '|andER| (app (app (app '|breln| '4) '3) (fst '2))) (app (app '|dall| '4) (lam (app (app '|ex1| '4) (lam (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) (app (app (app (app '|func#U| '4) '3) (fst '2)) (snd '2)))) '1)) (app (app (app (app '|ap| '4) '3) '2) '1)) '0) (app (app (app (app '|funcGraphProp1| '4) '3) '2) '1))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|funcGraphProp3| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '1) '0))) (dpi (dclass (app '|in| '2)) (pf (app (app '|in| (fst '1)) (fst (app (app '|kpair| (fst '0)) (fst (app (app (app (app '|ap2| '3) '2) '1) '0)))))))))) (lam (lam (lam (lam (app (app (app (app (app (app '|ap2#F| '3) '2) '1) '0) (lam (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) '0))))) (app (app (app (app '|funcGraphProp1| '3) '2) (pair (fst '1) (app (app (app '|infuncsetfunc| '3) '2) '1))) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|funcGraphProp4| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '1) '0))) (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '2)) (dpi (pf (app (app '|in| (fst '2)) (fst (app (app '|kpair| (fst '1)) (fst '0))))) (pf (app (app '|eq| (fst (app (app (app (app '|ap2| '5) '4) '3) '2))) (fst '1))))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app (app (app '|ap2#F| '5) '4) '3) '2) (lam (app (app '|eq| '0) (fst '2)))) (app (app (app (app (app (app '|funcGraphProp2| '5) '4) (pair (fst '3) (app (app (app '|infuncsetfunc| '5) '4) '3))) '2) '1) '0)))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|funcext| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|func| '1) '0)) (dpi (dclass (app (app '|func| '2) '1)) (dpi (dpi (dclass (app '|in| '3)) (pf (app (app '|eq| (fst (app (app (app (app '|ap| '4) '3) '2) '0))) (fst (app (app (app (app '|ap| '4) '3) '1) '0))))) (pf (app (app '|eq| (fst '2)) (fst '1)))))))) (lam (lam (lam (lam (lam (app (app (app (app (app (app '|eqbreln| '4) '3) (pair (fst '2) (app (app (app '|andEL| (app (app (app '|breln| '4) '3) (fst '2))) (app (app '|dall| '4) (lam (app (app '|ex1| '4) (lam (app (app '|in| (fst '4)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) (app (app (app (app '|func#U| '4) '3) (fst '2)) (snd '2))))) (pair (fst '1) (app (app (app '|andEL| (app (app (app '|breln| '4) '3) (fst '1))) (app (app '|dall| '4) (lam (app (app '|ex1| '4) (lam (app (app '|in| (fst '3)) (fst (app (app '|kpair| (fst '1)) (fst '0))))))))) (app (app (app (app '|func#U| '4) '3) (fst '1)) (snd '1))))) (lam (lam (lam (app (app (app (app (app '|eqE| (fst (app (app (app (app '|ap| '7) '6) '4) '2))) (fst '1)) (lam (app (app '|in| (fst '5)) (fst (app (app '|kpair| (fst '3)) '0))))) (app (app (app (app (app '|transeq| (fst (app (app (app (app '|ap| '7) '6) '4) '2))) (fst (app (app (app (app '|ap| '7) '6) '5) '2))) (fst '1)) (app (app (app '|symeq| (fst (app (app (app (app '|ap| '7) '6) '5) '2))) (fst (app (app (app (app '|ap| '7) '6) '4) '2))) (app '3 '2))) (app (app (app (app (app (app '|funcGraphProp2| '7) '6) '5) '2) '1) '0))) (app (app (app (app '|funcGraphProp1| '7) '6) '4) '2)))))) (lam (lam (lam (app (app (app (app (app '|eqE| (fst (app (app (app (app '|ap| '7) '6) '5) '2))) (fst '1)) (lam (app (app '|in| (fst '6)) (fst (app (app '|kpair| (fst '3)) '0))))) (app (app (app (app (app '|transeq| (fst (app (app (app (app '|ap| '7) '6) '5) '2))) (fst (app (app (app (app '|ap| '7) '6) '4) '2))) (fst '1)) (app '3 '2)) (app (app (app (app (app (app '|funcGraphProp2| '7) '6) '4) '2) '1) '0))) (app (app (app (app '|funcGraphProp1| '7) '6) '5) '2))))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|funcext2| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '1) '0))) (dpi (dclass (app '|in| (app (app '|funcSet| '2) '1))) (dpi (dpi (dclass (app '|in| '3)) (pf (app (app '|eq| (fst (app (app (app (app '|ap2| '4) '3) '2) '0))) (fst (app (app (app (app '|ap2| '4) '3) '1) '0))))) (pf (app (app '|eq| (fst '2)) (fst '1)))))))) (lam (lam (lam (lam (lam (app (app (app (app (app '|funcext| '4) '3) (pair (fst '2) (app (app (app '|infuncsetfunc| '4) '3) '2))) (pair (fst '1) (app (app (app '|infuncsetfunc| '4) '3) '1))) (lam (app (app (app (app (app (app '|ap2#U| '5) '4) '2) '0) (app '|eq| (fst (app (app (app (app '|ap| '5) '4) (pair (fst '3) (app (app (app '|infuncsetfunc| '5) '4) '3))) '0)))) (app (app (app (app (app (app '|ap2#U| '5) '4) '3) '0) (lam (app (app '|eq| '0) (fst (app (app (app (app '|ap2| '6) '5) '3) '1))))) (app '1 '0)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|beta1| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dclass (app '|in| '1))) (dpi (dclass (app '|in| '2)) (pf (app (app '|eq| (fst (app (app (app (app '|ap| '3) '2) (app (app (app '|lam| '3) '2) '1)) '0))) (fst (app '1 '0)))))))) (lam (lam (lam (lam (app (app (app (app (app (app '|funcGraphProp2| '3) '2) (app (app (app '|lam| '3) '2) '1)) '0) (app '1 '0)) (app (app (app (app (app '|lam#F| '3) '2) '1) (lam (app (app '|in| '0) (fst (app (app '|kpair| (fst '1)) (fst (app '2 '1))))))) (app (app (app (app (app (app '|dpsetconstrI| '3) '2) (lam (lam (app (app '|eq| (fst (app '3 '1))) (fst '0))))) '0) (app '1 '0)) (app '|eqI| (fst (app '1 '0)))))))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|beta2| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dclass (app '|in| '1))) (dpi (dclass (app '|in| '2)) (pf (app (app '|eq| (fst (app (app (app (app '|ap2| '3) '2) (app (app (app '|lam2| '3) '2) '1)) '0))) (fst (app '1 '0)))))))) (lam (lam (lam (lam (app (app (app (app (app '|transeq| (fst (app (app (app (app '|ap2| '3) '2) (app (app (app '|lam2| '3) '2) '1)) '0))) (fst (app (app (app (app '|ap| '3) '2) (app (app (app '|lam| '3) '2) '1)) '0))) (fst (app '1 '0))) (app (app (app (app (app (app '|eqCE| (app (app '|func| '3) '2)) (pair (fst (app (app (app '|lam2| '3) '2) '1)) (app (app (app '|infuncsetfunc| '3) '2) (app (app (app '|lam2| '3) '2) '1)))) (app (app (app '|lam| '3) '2) '1)) (lam (app (app '|eq| (fst (app (app (app (app '|ap2| '4) '3) (app (app (app '|lam2| '4) '3) '2)) '1))) (fst (app (app (app (app '|ap| '4) '3) '0) '1))))) (app (app (app '|lam2lamEq| '3) '2) '1)) (app (app (app (app '|ap2apEq1| '3) '2) (app (app (app '|lam2| '3) '2) '1)) '0))) (app (app (app (app '|beta1| '3) '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eta1| (dpi (obj) (dpi (obj) (dpi (dclass (app (app '|func| '1) '0)) (pf (app (app '|eq| (fst (app (app (app '|lam| '2) '1) (app (app (app '|ap| '2) '1) '0)))) (fst '0)))))) (lam (lam (lam (app (app (app (app (app '|funcext| '2) '1) (app (app (app '|lam| '2) '1) (app (app (app '|ap| '2) '1) '0))) '0) (app (app (app '|beta1| '2) '1) (app (app (app '|ap| '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|eta2| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '1) '0))) (pf (app (app '|eq| (fst (app (app (app '|lam2| '2) '1) (app (app (app '|ap2| '2) '1) '0)))) (fst '0)))))) (lam (lam (lam (app (app (app (app (app '|funcext2| '2) '1) (app (app (app '|lam2| '2) '1) (app (app (app '|ap2| '2) '1) '0))) '0) (app (app (app '|beta2| '2) '1) (app (app (app '|ap2| '2) '1) '0)))))) '("Chad Edward Brown") '("Chad Edward Brown"))

(newabbrev '|surjective| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '1) '0))) (prop)))) (lam (lam (lam (app (app '|dall| '1) (lam (app (app '|dex| '3) (lam (app (app '|eq| (fst (app (app (app (app '|ap2| '4) '3) '2) '0))) (fst '1))))))))) 'NIL 'NIL)

(newabbrev '|surjFuncSet| (dpi (obj) (dpi (obj) (obj))) (lam (lam (app (app '|dsetconstr| (app (app '|funcSet| '1) '0)) (app (app '|surjective| '1) '0)))) 'NIL 'NIL)

(newabbrev '|surjFuncSetFuncIn| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|surjFuncSet| '1) '0))) (pf (app (app '|in| (app (app '|funcSet| '2) '1)) (fst '0)))))) (lam (lam (lam (app (app (app (app '|dsetconstrEL| (app (app '|funcSet| '2) '1)) (app (app '|surjective| '2) '1)) (fst '0)) (app (app (app (app '|surjFuncSet#U| '2) '1) (lam (app (app '|in| '0) (fst '1)))) (snd '0)))))) 'NIL 'NIL)

(newabbrev '|surjFuncSetFuncSurj| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|surjFuncSet| '1) '0))) (pf (app (app (app '|surjective| '2) '1) (pair (fst '0) (app (app (app '|surjFuncSetFuncIn| '2) '1) '0))))))) (lam (lam (lam (app (app (app (app '|dsetconstrER| (app (app '|funcSet| '2) '1)) (app (app '|surjective| '2) '1)) (fst '0)) (app (app (app (app '|surjFuncSet#U| '2) '1) (lam (app (app '|in| '0) (fst '1)))) (snd '0)))))) 'NIL 'NIL)

(newabbrev '|surjCantorThm| (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '0) (app '|powerset| '0)))) (pf (app '|not| (app (app (app '|surjective| '1) (app '|powerset| '1)) '0))))) (lam (lam (app (app '|notI| (app (app (app '|surjective| '1) (app '|powerset| '1)) '0)) (lam (app (app (app (app (app '|dexE| '2) (lam (app (app '|eq| (fst (app (app (app (app '|ap2| '3) (app '|powerset| '3)) '2) '0))) (app (app '|dsetconstr| '3) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '4) (app '|powerset| '4)) '3) '0))) (fst '0)))))))) (app (app (app (app '|dallE| (app '|powerset| '2)) (lam (app (app '|dex| '3) (lam (app (app '|eq| (fst (app (app (app (app '|ap2| '4) (app '|powerset| '4)) '3) '0))) (fst '1)))))) (app (app (app (app '|surjective#U| '2) (app '|powerset| '2)) '1) '0)) (pair (app (app '|dsetconstr| '2) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '3) (app '|powerset| '3)) '2) '0))) (fst '0))))) (app (app (app '|powersetI| '2) (app (app '|dsetconstr| '2) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '3) (app '|powerset| '3)) '2) '0))) (fst '0)))))) (app (app '|dsetconstrEL| '2) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '3) (app '|powerset| '3)) '2) '0))) (fst '0))))))))) '|false|) (lam (lam (app (app (app (app '|xmcases| (app (app '|in| (fst (app (app (app (app '|ap2| '4) (app '|powerset| '4)) '3) '1))) (fst '1))) '|false|) (lam (app (app (app (app '|notE| (app (app '|in| (fst (app (app (app (app '|ap2| '5) (app '|powerset| '5)) '4) '2))) (fst '2))) '|false|) '0) (app (app (app (app '|dsetconstrER| '5) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '6) (app '|powerset| '6)) '5) '0))) (fst '0))))) (fst '2)) (app (app (app (app (app '|eqE| (fst (app (app (app (app '|ap2| '5) (app '|powerset| '5)) '4) '2))) (app (app '|dsetconstr| '5) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '6) (app '|powerset| '6)) '5) '0))) (fst '0)))))) (lam (app (app '|in| '0) (fst '3)))) '1) '0))))) (lam (app (app (app (app '|notE| (app (app '|in| (fst (app (app (app (app '|ap2| '5) (app '|powerset| '5)) '4) '2))) (fst '2))) '|false|) (app (app (app (app (app '|eqE2| (fst (app (app (app (app '|ap2| '5) (app '|powerset| '5)) '4) '2))) (app (app '|dsetconstr| '5) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '6) (app '|powerset| '6)) '5) '0))) (fst '0)))))) (lam (app (app '|in| '0) (fst '3)))) '1) (app (app (app (app '|dsetconstrI| '5) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '6) (app '|powerset| '6)) '5) '0))) (fst '0))))) '2) '0))) (app (app (app (app '|dsetconstrER| '5) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '6) (app '|powerset| '6)) '5) '0))) (fst '0))))) (fst '2)) (app (app (app (app (app '|eqE| (fst (app (app (app (app '|ap2| '5) (app '|powerset| '5)) '4) '2))) (app (app '|dsetconstr| '5) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '6) (app '|powerset| '6)) '5) '0))) (fst '0)))))) (lam (app (app '|in| '0) (fst '3)))) '1) (app (app (app (app (app '|eqE2| (fst (app (app (app (app '|ap2| '5) (app '|powerset| '5)) '4) '2))) (app (app '|dsetconstr| '5) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '6) (app '|powerset| '6)) '5) '0))) (fst '0)))))) (lam (app (app '|in| '0) (fst '3)))) '1) (app (app (app (app '|dsetconstrI| '5) (lam (app '|not| (app (app '|in| (fst (app (app (app (app '|ap2| '6) (app '|powerset| '6)) '5) '0))) (fst '0))))) '2) '0)))))))))))))) 'NIL 'NIL)

(newabbrev '|injective| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '1) '0))) (prop)))) (lam (lam (lam (app (app '|dall| '2) (lam (app (app '|dall| '3) (lam (app (app '|imp| (app (app '|eq| (fst (app (app (app (app '|ap2| '4) '3) '2) '1))) (fst (app (app (app (app '|ap2| '4) '3) '2) '0)))) (app (app '|eq| (fst '1)) (fst '0)))))))))) 'NIL 'NIL)

(newabbrev '|injFuncSet| (dpi (obj) (dpi (obj) (obj))) (lam (lam (app (app '|dsetconstr| (app (app '|funcSet| '1) '0)) (app (app '|injective| '1) '0)))) 'NIL 'NIL)

(newabbrev '|injFuncSetFuncIn| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|injFuncSet| '1) '0))) (pf (app (app '|in| (app (app '|funcSet| '2) '1)) (fst '0)))))) (lam (lam (lam (app (app (app (app '|dsetconstrEL| (app (app '|funcSet| '2) '1)) (app (app '|injective| '2) '1)) (fst '0)) (app (app (app (app '|injFuncSet#U| '2) '1) (lam (app (app '|in| '0) (fst '1)))) (snd '0)))))) 'NIL 'NIL)

(newabbrev '|injFuncSetFuncInj| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|injFuncSet| '1) '0))) (pf (app (app (app '|injective| '2) '1) (pair (fst '0) (app (app (app '|injFuncSetFuncIn| '2) '1) '0))))))) (lam (lam (lam (app (app (app (app '|dsetconstrER| (app (app '|funcSet| '2) '1)) (app (app '|injective| '2) '1)) (fst '0)) (app (app (app (app '|injFuncSet#U| '2) '1) (lam (app (app '|in| '0) (fst '1)))) (snd '0)))))) 'NIL 'NIL)

(newabbrev '|injFuncInInjFuncSet| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| '1) '0))) (dpi (pf (app (app (app '|injective| '2) '1) '0)) (pf (app (app '|in| (app (app '|injFuncSet| '3) '2)) (fst '1))))))) (lam (lam (lam (lam (app (app (app (app '|injFuncSet#F| '3) '2) (lam (app (app '|in| '0) (fst '2)))) (app (app (app (app '|dsetconstrI| (app (app '|funcSet| '3) '2)) (app (app '|injective| '3) '2)) '1) '0)))))) 'NIL 'NIL)

(newabbrev '|leftInvIsSurj| (dpi (obj) (dpi (obj) (dpi (dpi (dclass (app '|in| '1)) (dclass (app '|in| '1))) (dpi (dpi (dclass (app '|in| '2)) (dpi (dclass (app '|in| '3)) (dpi (pf (app (app '|eq| (fst '1)) (fst '0))) (pf (app (app '|eq| (fst (app '3 '2))) (fst (app '3 '1))))))) (dpi (dclass (app '|in| (app (app '|funcSet| '2) '3))) (dpi (pf (app (app '|dall| '4) (lam (app (app '|eq| (fst (app (app (app (app '|ap2| '4) '5) '1) (app '3 '0)))) (fst '0))))) (pf (app (app (app '|surjective| '4) '5) '1)))))))) (lam (lam (lam (lam (lam (lam (app (app (app (app '|surjective#F| '4) '5) '1) (app (app (app '|dallI| '5) (lam (app (app '|dex| '5) (lam (app (app '|eq| (fst (app (app (app (app '|ap2| '6) '7) '3) '0))) (fst '1)))))) (lam (app (app (app (app '|dexI| '5) (lam (app (app '|eq| (fst (app (app (app (app '|ap2| '6) '7) '3) '0))) (fst '1)))) (app '4 '0)) (app (app (app (app '|dallE| '6) (lam (app (app '|eq| (fst (app (app (app (app '|ap2| '6) '7) '3) (app '5 '0)))) (fst '0)))) '1) '0))))))))))) 'NIL 'NIL)

(newclaim '|leftInvOfInjProp| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|injFuncSet| '1) '0))) (dpi (dclass (app '|in| '2)) (pf (app (app '|in| (app (app '|surjFuncSet| '2) '3)) (app (app (app '|dpsetconstr| '2) '3) (lam (lam (app (app '|or| (app (app '|eq| (fst (app (app (app (app '|ap2| '5) '4) (pair (fst '3) (app (app (app '|injFuncSetFuncIn| '5) '4) '3))) '0))) (fst '1))) (app (app '|and| (app '|not| (app (app '|dex| '5) (lam (app (app '|eq| (fst (app (app (app (app '|ap2| '6) '5) (pair (fst '4) (app (app (app '|injFuncSetFuncIn| '6) '5) '4))) '0))) (fst '2)))))) (app (app '|eq| (fst '0)) (fst '2))))))))))))) 'NIL)

(newabbrev '|leftInvOfInj| (dpi (obj) (dpi (obj) (dpi (dclass (app '|in| (app (app '|injFuncSet| '1) '0))) (dpi (dclass (app '|in| '2)) (dclass (app '|in| (app (app '|surjFuncSet| '2) '3))))))) (lam (lam (lam (lam (pair (app (app (app '|dpsetconstr| '2) '3) (lam (lam (app (app '|or| (app (app '|eq| (fst (app (app (app (app '|ap2| '5) '4) (pair (fst '3) (app (app (app '|injFuncSetFuncIn| '5) '4) '3))) '0))) (fst '1))) (app (app '|and| (app '|not| (app (app '|dex| '5) (lam (app (app '|eq| (fst (app (app (app (app '|ap2| '6) '5) (pair (fst '4) (app (app (app '|injFuncSetFuncIn| '6) '5) '4))) '0))) (fst '2)))))) (app (app '|eq| (fst '0)) (fst '2))))))) (app (app (app (app '|leftInvOfInjProp| '3) '2) '1) '0)))))) 'NIL 'NIL)

(newabbrev '|emptyInPowerset| (dpi (obj) (pf (app (app '|in| (app '|powerset| '0)) '|emptyset|))) (lam (app (app (app '|powersetI| '0) '|emptyset|) (lam (lam (app (app (app '|emptysetE| '1) '0) (app (app '|in| '2) '1)))))) 'NIL 'NIL)

(newabbrev '|inPowerset| (dpi (obj) (pf (app (app '|in| (app '|powerset| '0)) '0))) (lam (app (app (app '|powersetI1| '0) '0) (app '|subsetRefl| '0))) 'NIL 'NIL)

(newabbrev '|powersetNonempty| (dpi (obj) (pf (app '|nonempty| (app '|powerset| '0)))) (lam (app (app (app '|witnessnonempty| (app '|powerset| '0)) '0) (app '|inPowerset| '0))) 'NIL 'NIL)

(newclaim '|injCantorThm| (dpi (obj) (dpi (dclass (app '|in| (app (app '|funcSet| (app '|powerset| '0)) '0))) (pf (app '|not| (app (app (app '|injective| (app '|powerset| '1)) '1) '0))))) 'NIL)

(claim2abbrev '|leftInvOfInjProp|
'(LAM LAM LAM LAM APP
     (APP (APP (APP |surjFuncSet#F| . 2) . 3) LAM APP (APP |in| . 0)
          APP (APP (APP |dpsetconstr| . 3) . 4) LAM LAM APP
          (APP |or| APP
               (APP |eq| FST APP
                    (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4) APP
                         (APP (APP |injFuncSetFuncIn| . 6) . 5) . 4)
                    . 0)
               FST . 1)
          APP
          (APP |and| APP |not| APP (APP |dex| . 6) LAM APP
               (APP |eq| FST APP
                    (APP (APP (APP |ap2| . 7) . 6) PAIR (FST . 5) APP
                         (APP (APP |injFuncSetFuncIn| . 7) . 6) . 5)
                    . 0)
               FST . 2)
          APP (APP |eq| FST . 0) FST . 3)
     APP
     (APP (APP (APP |dsetconstrI| APP (APP |funcSet| . 2) . 3) APP
               (APP |surjective| . 2) . 3)
          PAIR
          (APP (APP (APP |dpsetconstr| . 2) . 3) LAM LAM APP
               (APP |or| APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 5) . 4) PAIR (FST . 3)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 5) . 4)
                              . 3)
                         . 0)
                    FST . 1)
               APP
               (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 6) . 5)
                              . 4)
                         . 0)
                    FST . 2)
               APP (APP |eq| FST . 0) FST . 2)
          APP
          (APP (APP (APP |funcSet#F| . 2) . 3) LAM APP (APP |in| . 0)
               APP (APP (APP |dpsetconstr| . 3) . 4) LAM LAM APP
               (APP |or| APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 6) . 5)
                              . 4)
                         . 0)
                    FST . 1)
               APP
               (APP |and| APP |not| APP (APP |dex| . 6) LAM APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 7) . 6) PAIR (FST . 5)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 7) . 6)
                              . 5)
                         . 0)
                    FST . 2)
               APP (APP |eq| FST . 0) FST . 3)
          APP
          (APP (APP (APP |dsetconstrI| APP |powerset| APP
                         (APP |cartprod| . 2) . 3)
                    LAM APP (APP (APP |func| . 3) . 4) FST . 0)
               PAIR
               (APP (APP (APP |dpsetconstr| . 2) . 3) LAM LAM APP
                    (APP |or| APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 5) . 4) PAIR
                                   (FST . 3) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 5)
                                    . 4)
                                   . 3)
                              . 0)
                         FST . 1)
                    APP
                    (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 6) . 5) PAIR
                                   (FST . 4) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 6)
                                    . 5)
                                   . 4)
                              . 0)
                         FST . 2)
                    APP (APP |eq| FST . 0) FST . 2)
               APP
               (APP (APP |powersetI1| APP (APP |cartprod| . 2) . 3) APP
                    (APP (APP |dpsetconstr| . 2) . 3) LAM LAM APP
                    (APP |or| APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 5) . 4) PAIR
                                   (FST . 3) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 5)
                                    . 4)
                                   . 3)
                              . 0)
                         FST . 1)
                    APP
                    (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 6) . 5) PAIR
                                   (FST . 4) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 6)
                                    . 5)
                                   . 4)
                              . 0)
                         FST . 2)
                    APP (APP |eq| FST . 0) FST . 2)
               APP (APP (APP |dpsetconstrSub| . 2) . 3) LAM LAM APP
               (APP |or| APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 5) . 4) PAIR (FST . 3)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 5) . 4)
                              . 3)
                         . 0)
                    FST . 1)
               APP
               (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 6) . 5)
                              . 4)
                         . 0)
                    FST . 2)
               APP (APP |eq| FST . 0) FST . 2)
          APP
          (APP (APP (APP |func#F| . 2) . 3) APP
               (APP (APP |dpsetconstr| . 2) . 3) LAM LAM APP
               (APP |or| APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 5) . 4) PAIR (FST . 3)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 5) . 4)
                              . 3)
                         . 0)
                    FST . 1)
               APP
               (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 6) . 5)
                              . 4)
                         . 0)
                    FST . 2)
               APP (APP |eq| FST . 0) FST . 2)
          APP
          (APP (APP (APP |andI| APP (APP (APP |breln| . 2) . 3) APP
                         (APP (APP |dpsetconstr| . 2) . 3) LAM LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 5) . 4)
                                    PAIR
                                    (FST . 3)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 5)
                                     . 4)
                                    . 3)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 5) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 6) . 5)
                                    PAIR
                                    (FST . 4)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 6)
                                     . 5)
                                    . 4)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 2)
                    APP (APP |dall| . 2) LAM APP (APP |ex1| . 4) LAM
                    APP
                    (APP |in| APP (APP (APP |dpsetconstr| . 4) . 5) LAM
                         LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 4)
                    FST APP (APP |kpair| FST . 1) FST . 0)
               APP (APP (APP |setOfPairsIsBReln| . 2) . 3) LAM LAM APP
               (APP |or| APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 5) . 4) PAIR (FST . 3)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 5) . 4)
                              . 3)
                         . 0)
                    FST . 1)
               APP
               (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 6) . 5)
                              . 4)
                         . 0)
                    FST . 2)
               APP (APP |eq| FST . 0) FST . 2)
          APP
          (APP (APP |dallI| . 2) LAM APP (APP |ex1| . 4) LAM APP
               (APP |in| APP (APP (APP |dpsetconstr| . 4) . 5) LAM LAM
                    APP
                    (APP |or| APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 7) . 6) PAIR
                                   (FST . 5) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 7)
                                    . 6)
                                   . 5)
                              . 0)
                         FST . 1)
                    APP
                    (APP |and| APP |not| APP (APP |dex| . 7) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 8) . 7) PAIR
                                   (FST . 6) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 8)
                                    . 7)
                                   . 6)
                              . 0)
                         FST . 2)
                    APP (APP |eq| FST . 0) FST . 4)
               FST APP (APP |kpair| FST . 1) FST . 0)
          LAM APP
          (APP (APP (APP |xmcases| APP (APP |dex| . 4) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 5) . 4) PAIR
                                   (FST . 3) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 5)
                                    . 4)
                                   . 3)
                              . 0)
                         FST . 1)
                    APP (APP |ex1| . 4) LAM APP
                    (APP |in| APP (APP (APP |dpsetconstr| . 4) . 5) LAM
                         LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 4)
                    FST APP (APP |kpair| FST . 1) FST . 0)
               LAM APP
               (APP (APP (APP (APP |dexE| . 5) LAM APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 6) . 5)
                                    PAIR
                                    (FST . 4)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 6)
                                     . 5)
                                    . 4)
                                   . 0)
                              FST . 2)
                         . 0)
                    APP (APP |ex1| . 5) LAM APP
                    (APP |in| APP (APP (APP |dpsetconstr| . 5) . 6) LAM
                         LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 8) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 9) . 8)
                                    PAIR
                                    (FST . 7)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 9)
                                     . 8)
                                    . 7)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 5)
                    FST APP (APP |kpair| FST . 2) FST . 0)
               LAM LAM APP
               (APP (APP (APP (APP |ex1I| . 7) LAM APP
                              (APP |in| APP
                                   (APP (APP |dpsetconstr| . 7) . 8)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 10)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 11) . 10)
                                      PAIR
                                      (FST . 9)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 11)
                                       . 10)
                                      . 9)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 7)
                              FST APP (APP |kpair| FST . 4) FST . 0)
                         . 1)
                    APP
                    (APP (APP (APP (APP (APP |dpsetconstrI| . 6) . 7)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 6)
                              . 3)
                         . 1)
                    APP
                    (APP (APP |orIL| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 1)
                              FST . 3)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 4)
                         APP (APP |eq| FST . 1) FST . 4)
                    . 0)
               LAM LAM APP
               (APP (APP (APP (APP (APP
                                    |orE|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     PAIR
                                     (FST . 1)
                                     APP
                                     (APP
                                      (APP
                                       (APP
                                        (APP
                                         (APP |dpsetconstrEL2| . 8)
                                         . 9)
                                        LAM
                                        LAM
                                        APP
                                        (APP
                                         |or|
                                         APP
                                         (APP
                                          |eq|
                                          FST
                                          APP
                                          (APP
                                           (APP (APP |ap2| . 11) . 10)
                                           PAIR
                                           (FST . 9)
                                           APP
                                           (APP
                                            (APP
                                             |injFuncSetFuncIn|
                                             . 11)
                                            . 10)
                                           . 9)
                                          . 0)
                                         FST
                                         . 1)
                                        APP
                                        (APP
                                         |and|
                                         APP
                                         |not|
                                         APP
                                         (APP |dex| . 11)
                                         LAM
                                         APP
                                         (APP
                                          |eq|
                                          FST
                                          APP
                                          (APP
                                           (APP (APP |ap2| . 12) . 11)
                                           PAIR
                                           (FST . 10)
                                           APP
                                           (APP
                                            (APP
                                             |injFuncSetFuncIn|
                                             . 12)
                                            . 11)
                                           . 10)
                                          . 0)
                                         FST
                                         . 2)
                                        APP
                                        (APP |eq| FST . 0)
                                        FST
                                        . 8)
                                       FST
                                       . 5)
                                      FST
                                      . 1)
                                     . 0)
                                    FST
                                    . 5)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 6)
                                   APP (APP |eq| FST . 1) FST . 6)
                              APP
                              (APP (APP
                                    (APP
                                     (APP
                                      (APP |dpsetconstrER| . 8)
                                      . 9)
                                     LAM
                                     LAM
                                     APP
                                     (APP
                                      |or|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 11) . 10)
                                        PAIR
                                        (FST . 9)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 11)
                                         . 10)
                                        . 9)
                                       . 0)
                                      FST
                                      . 1)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 11)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 12) . 11)
                                        PAIR
                                        (FST . 10)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 12)
                                         . 11)
                                        . 10)
                                       . 0)
                                      FST
                                      . 2)
                                     APP
                                     (APP |eq| FST . 0)
                                     FST
                                     . 8)
                                    FST
                                    . 5)
                                   FST . 1)
                              . 0)
                         APP (APP |eq| FST . 1) FST . 3)
                    LAM APP
                    (APP (APP (APP |impE| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 10) . 9)
                                     PAIR
                                     (FST . 8)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 10)
                                      . 9)
                                     . 8)
                                    . 2)
                                   FST APP
                                   (APP
                                    (APP (APP |ap2| . 10) . 9)
                                    PAIR
                                    (FST . 8)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 10)
                                     . 9)
                                    . 8)
                                   . 4)
                              APP (APP |eq| FST . 2) FST . 4)
                         APP
                         (APP (APP (APP |dallE| . 10) LAM APP
                                   (APP
                                    |imp|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 11) . 10)
                                      PAIR
                                      (FST . 9)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 11)
                                       . 10)
                                      . 9)
                                     . 3)
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 11) . 10)
                                     PAIR
                                     (FST . 9)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 11)
                                      . 10)
                                     . 9)
                                    . 0)
                                   APP (APP |eq| FST . 3) FST . 0)
                              APP
                              (APP (APP
                                    (APP |dallE| . 10)
                                    LAM
                                    APP
                                    (APP |dall| . 11)
                                    LAM
                                    APP
                                    (APP
                                     |imp|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 12) . 11)
                                       PAIR
                                       (FST . 10)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 12)
                                        . 11)
                                       . 10)
                                      . 1)
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 12) . 11)
                                      PAIR
                                      (FST . 10)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 12)
                                       . 11)
                                      . 10)
                                     . 0)
                                    APP
                                    (APP |eq| FST . 1)
                                    FST
                                    . 0)
                                   APP
                                   (APP
                                    (APP (APP |injective#U| . 10) . 9)
                                    PAIR
                                    (FST . 8)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 10)
                                     . 9)
                                    . 8)
                                   APP
                                   (APP
                                    (APP |injFuncSetFuncInj| . 10)
                                    . 9)
                                   . 8)
                              . 2)
                         . 4)
                    APP
                    (APP (APP (APP (APP
                                    |symtrans2eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 10) . 9)
                                     PAIR
                                     (FST . 8)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 10)
                                      . 9)
                                     . 8)
                                    . 4)
                                   FST . 6)
                              FST APP
                              (APP (APP (APP |ap2| . 10) . 9) PAIR
                                   (FST . 8) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 10)
                                    . 9)
                                   . 8)
                              . 2)
                         . 3)
                    . 0)
               LAM APP
               (APP (APP (APP |notE| APP (APP |dex| . 10) LAM APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 11) . 10)
                                    PAIR
                                    (FST . 9)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 11)
                                     . 10)
                                    . 9)
                                   . 0)
                              FST . 7)
                         APP (APP |eq| FST . 2) FST . 4)
                    . 5)
               APP
               (APP (APP |andEL| APP |not| APP (APP |dex| . 10) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 11) . 10) PAIR
                                   (FST . 9) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 11)
                                    . 10)
                                   . 9)
                              . 0)
                         FST . 7)
                    APP (APP |eq| FST . 2) FST . 7)
               . 0)
          LAM APP
          (APP (APP (APP (APP |ex1I| . 5) LAM APP
                         (APP |in| APP
                              (APP (APP |dpsetconstr| . 5) . 6) LAM LAM
                              APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 8)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 9) . 8)
                                     PAIR
                                     (FST . 7)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 9)
                                      . 8)
                                     . 7)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 5)
                         FST APP (APP |kpair| FST . 2) FST . 0)
                    . 2)
               APP
               (APP (APP (APP (APP (APP |dpsetconstrI| . 4) . 5) LAM
                              LAM APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 4)
                         . 1)
                    . 2)
               APP
               (APP (APP |orIR| APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 5) . 4) PAIR
                                   (FST . 3) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 5)
                                    . 4)
                                   . 3)
                              . 2)
                         FST . 1)
                    APP
                    (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 6) . 5) PAIR
                                   (FST . 4) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 6)
                                    . 5)
                                   . 4)
                              . 0)
                         FST . 2)
                    APP (APP |eq| FST . 2) FST . 2)
               APP
               (APP (APP (APP |andI| APP |not| APP (APP |dex| . 5) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 6) . 5)
                                    PAIR
                                    (FST . 4)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 6)
                                     . 5)
                                    . 4)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 2) FST . 2)
                    . 0)
               APP |eqI| FST . 2)
          LAM LAM APP
          (APP (APP (APP (APP (APP |orE| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 1)
                                   FST . 3)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 4)
                              APP (APP |eq| FST . 1) FST . 4)
                         APP
                         (APP (APP (APP
                                    (APP (APP |dpsetconstrER| . 6) . 7)
                                    LAM
                                    LAM
                                    APP
                                    (APP
                                     |or|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 9) . 8)
                                       PAIR
                                       (FST . 7)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 9)
                                        . 8)
                                       . 7)
                                      . 0)
                                     FST
                                     . 1)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 9)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 10) . 9)
                                       PAIR
                                       (FST . 8)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 10)
                                        . 9)
                                       . 8)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 0)
                                    FST
                                    . 6)
                                   FST . 3)
                              FST . 1)
                         . 0)
                    APP (APP |eq| FST . 1) FST . 4)
               LAM APP (APP |falseE| APP (APP |eq| FST . 2) FST . 5)
               APP
               (APP (APP (APP |notE| APP (APP |dex| . 8) LAM APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 9) . 8)
                                    PAIR
                                    (FST . 7)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 9)
                                     . 8)
                                    . 7)
                                   . 0)
                              FST . 5)
                         . |false|)
                    APP
                    (APP (APP (APP |dexI| . 8) LAM APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 9) . 8)
                                    PAIR
                                    (FST . 7)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 9)
                                     . 8)
                                    . 7)
                                   . 0)
                              FST . 5)
                         . 2)
                    . 0)
               . 3)
          APP
          (APP |andER| APP |not| APP (APP |dex| . 7) LAM APP
               (APP |eq| FST APP
                    (APP (APP (APP |ap2| . 8) . 7) PAIR (FST . 6) APP
                         (APP (APP |injFuncSetFuncIn| . 8) . 7) . 6)
                    . 0)
               FST . 4)
          APP (APP |eq| FST . 1) FST . 4)
     APP
     (APP (APP (APP |surjective#F| . 2) . 3) PAIR
          (APP (APP (APP |dpsetconstr| . 2) . 3) LAM LAM APP
               (APP |or| APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 5) . 4) PAIR (FST . 3)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 5) . 4)
                              . 3)
                         . 0)
                    FST . 1)
               APP
               (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 6) . 5)
                              . 4)
                         . 0)
                    FST . 2)
               APP (APP |eq| FST . 0) FST . 2)
          APP
          (APP (APP (APP |funcSet#F| . 2) . 3) LAM APP (APP |in| . 0)
               APP (APP (APP |dpsetconstr| . 3) . 4) LAM LAM APP
               (APP |or| APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 6) . 5)
                              . 4)
                         . 0)
                    FST . 1)
               APP
               (APP |and| APP |not| APP (APP |dex| . 6) LAM APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 7) . 6) PAIR (FST . 5)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 7) . 6)
                              . 5)
                         . 0)
                    FST . 2)
               APP (APP |eq| FST . 0) FST . 3)
          APP
          (APP (APP (APP |dsetconstrI| APP |powerset| APP
                         (APP |cartprod| . 2) . 3)
                    LAM APP (APP (APP |func| . 3) . 4) FST . 0)
               PAIR
               (APP (APP (APP |dpsetconstr| . 2) . 3) LAM LAM APP
                    (APP |or| APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 5) . 4) PAIR
                                   (FST . 3) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 5)
                                    . 4)
                                   . 3)
                              . 0)
                         FST . 1)
                    APP
                    (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 6) . 5) PAIR
                                   (FST . 4) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 6)
                                    . 5)
                                   . 4)
                              . 0)
                         FST . 2)
                    APP (APP |eq| FST . 0) FST . 2)
               APP
               (APP (APP |powersetI1| APP (APP |cartprod| . 2) . 3) APP
                    (APP (APP |dpsetconstr| . 2) . 3) LAM LAM APP
                    (APP |or| APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 5) . 4) PAIR
                                   (FST . 3) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 5)
                                    . 4)
                                   . 3)
                              . 0)
                         FST . 1)
                    APP
                    (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 6) . 5) PAIR
                                   (FST . 4) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 6)
                                    . 5)
                                   . 4)
                              . 0)
                         FST . 2)
                    APP (APP |eq| FST . 0) FST . 2)
               APP (APP (APP |dpsetconstrSub| . 2) . 3) LAM LAM APP
               (APP |or| APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 5) . 4) PAIR (FST . 3)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 5) . 4)
                              . 3)
                         . 0)
                    FST . 1)
               APP
               (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 6) . 5)
                              . 4)
                         . 0)
                    FST . 2)
               APP (APP |eq| FST . 0) FST . 2)
          APP
          (APP (APP (APP |func#F| . 2) . 3) APP
               (APP (APP |dpsetconstr| . 2) . 3) LAM LAM APP
               (APP |or| APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 5) . 4) PAIR (FST . 3)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 5) . 4)
                              . 3)
                         . 0)
                    FST . 1)
               APP
               (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 6) . 5)
                              . 4)
                         . 0)
                    FST . 2)
               APP (APP |eq| FST . 0) FST . 2)
          APP
          (APP (APP (APP |andI| APP (APP (APP |breln| . 2) . 3) APP
                         (APP (APP |dpsetconstr| . 2) . 3) LAM LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 5) . 4)
                                    PAIR
                                    (FST . 3)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 5)
                                     . 4)
                                    . 3)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 5) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 6) . 5)
                                    PAIR
                                    (FST . 4)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 6)
                                     . 5)
                                    . 4)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 2)
                    APP (APP |dall| . 2) LAM APP (APP |ex1| . 4) LAM
                    APP
                    (APP |in| APP (APP (APP |dpsetconstr| . 4) . 5) LAM
                         LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 4)
                    FST APP (APP |kpair| FST . 1) FST . 0)
               APP (APP (APP |setOfPairsIsBReln| . 2) . 3) LAM LAM APP
               (APP |or| APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 5) . 4) PAIR (FST . 3)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 5) . 4)
                              . 3)
                         . 0)
                    FST . 1)
               APP
               (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                    (APP |eq| FST APP
                         (APP (APP (APP |ap2| . 6) . 5) PAIR (FST . 4)
                              APP
                              (APP (APP |injFuncSetFuncIn| . 6) . 5)
                              . 4)
                         . 0)
                    FST . 2)
               APP (APP |eq| FST . 0) FST . 2)
          APP
          (APP (APP |dallI| . 2) LAM APP (APP |ex1| . 4) LAM APP
               (APP |in| APP (APP (APP |dpsetconstr| . 4) . 5) LAM LAM
                    APP
                    (APP |or| APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 7) . 6) PAIR
                                   (FST . 5) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 7)
                                    . 6)
                                   . 5)
                              . 0)
                         FST . 1)
                    APP
                    (APP |and| APP |not| APP (APP |dex| . 7) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 8) . 7) PAIR
                                   (FST . 6) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 8)
                                    . 7)
                                   . 6)
                              . 0)
                         FST . 2)
                    APP (APP |eq| FST . 0) FST . 4)
               FST APP (APP |kpair| FST . 1) FST . 0)
          LAM APP
          (APP (APP (APP |xmcases| APP (APP |dex| . 4) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 5) . 4) PAIR
                                   (FST . 3) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 5)
                                    . 4)
                                   . 3)
                              . 0)
                         FST . 1)
                    APP (APP |ex1| . 4) LAM APP
                    (APP |in| APP (APP (APP |dpsetconstr| . 4) . 5) LAM
                         LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 4)
                    FST APP (APP |kpair| FST . 1) FST . 0)
               LAM APP
               (APP (APP (APP (APP |dexE| . 5) LAM APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 6) . 5)
                                    PAIR
                                    (FST . 4)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 6)
                                     . 5)
                                    . 4)
                                   . 0)
                              FST . 2)
                         . 0)
                    APP (APP |ex1| . 5) LAM APP
                    (APP |in| APP (APP (APP |dpsetconstr| . 5) . 6) LAM
                         LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 8) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 9) . 8)
                                    PAIR
                                    (FST . 7)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 9)
                                     . 8)
                                    . 7)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 5)
                    FST APP (APP |kpair| FST . 2) FST . 0)
               LAM LAM APP
               (APP (APP (APP (APP |ex1I| . 7) LAM APP
                              (APP |in| APP
                                   (APP (APP |dpsetconstr| . 7) . 8)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 10)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 11) . 10)
                                      PAIR
                                      (FST . 9)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 11)
                                       . 10)
                                      . 9)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 7)
                              FST APP (APP |kpair| FST . 4) FST . 0)
                         . 1)
                    APP
                    (APP (APP (APP (APP (APP |dpsetconstrI| . 6) . 7)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 6)
                              . 3)
                         . 1)
                    APP
                    (APP (APP |orIL| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 1)
                              FST . 3)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 4)
                         APP (APP |eq| FST . 1) FST . 4)
                    . 0)
               LAM LAM APP
               (APP (APP (APP (APP (APP
                                    |orE|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     PAIR
                                     (FST . 1)
                                     APP
                                     (APP
                                      (APP
                                       (APP
                                        (APP
                                         (APP |dpsetconstrEL2| . 8)
                                         . 9)
                                        LAM
                                        LAM
                                        APP
                                        (APP
                                         |or|
                                         APP
                                         (APP
                                          |eq|
                                          FST
                                          APP
                                          (APP
                                           (APP (APP |ap2| . 11) . 10)
                                           PAIR
                                           (FST . 9)
                                           APP
                                           (APP
                                            (APP
                                             |injFuncSetFuncIn|
                                             . 11)
                                            . 10)
                                           . 9)
                                          . 0)
                                         FST
                                         . 1)
                                        APP
                                        (APP
                                         |and|
                                         APP
                                         |not|
                                         APP
                                         (APP |dex| . 11)
                                         LAM
                                         APP
                                         (APP
                                          |eq|
                                          FST
                                          APP
                                          (APP
                                           (APP (APP |ap2| . 12) . 11)
                                           PAIR
                                           (FST . 10)
                                           APP
                                           (APP
                                            (APP
                                             |injFuncSetFuncIn|
                                             . 12)
                                            . 11)
                                           . 10)
                                          . 0)
                                         FST
                                         . 2)
                                        APP
                                        (APP |eq| FST . 0)
                                        FST
                                        . 8)
                                       FST
                                       . 5)
                                      FST
                                      . 1)
                                     . 0)
                                    FST
                                    . 5)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 6)
                                   APP (APP |eq| FST . 1) FST . 6)
                              APP
                              (APP (APP
                                    (APP
                                     (APP
                                      (APP |dpsetconstrER| . 8)
                                      . 9)
                                     LAM
                                     LAM
                                     APP
                                     (APP
                                      |or|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 11) . 10)
                                        PAIR
                                        (FST . 9)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 11)
                                         . 10)
                                        . 9)
                                       . 0)
                                      FST
                                      . 1)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 11)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 12) . 11)
                                        PAIR
                                        (FST . 10)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 12)
                                         . 11)
                                        . 10)
                                       . 0)
                                      FST
                                      . 2)
                                     APP
                                     (APP |eq| FST . 0)
                                     FST
                                     . 8)
                                    FST
                                    . 5)
                                   FST . 1)
                              . 0)
                         APP (APP |eq| FST . 1) FST . 3)
                    LAM APP
                    (APP (APP (APP |impE| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 10) . 9)
                                     PAIR
                                     (FST . 8)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 10)
                                      . 9)
                                     . 8)
                                    . 2)
                                   FST APP
                                   (APP
                                    (APP (APP |ap2| . 10) . 9)
                                    PAIR
                                    (FST . 8)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 10)
                                     . 9)
                                    . 8)
                                   . 4)
                              APP (APP |eq| FST . 2) FST . 4)
                         APP
                         (APP (APP (APP |dallE| . 10) LAM APP
                                   (APP
                                    |imp|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 11) . 10)
                                      PAIR
                                      (FST . 9)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 11)
                                       . 10)
                                      . 9)
                                     . 3)
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 11) . 10)
                                     PAIR
                                     (FST . 9)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 11)
                                      . 10)
                                     . 9)
                                    . 0)
                                   APP (APP |eq| FST . 3) FST . 0)
                              APP
                              (APP (APP
                                    (APP |dallE| . 10)
                                    LAM
                                    APP
                                    (APP |dall| . 11)
                                    LAM
                                    APP
                                    (APP
                                     |imp|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 12) . 11)
                                       PAIR
                                       (FST . 10)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 12)
                                        . 11)
                                       . 10)
                                      . 1)
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 12) . 11)
                                      PAIR
                                      (FST . 10)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 12)
                                       . 11)
                                      . 10)
                                     . 0)
                                    APP
                                    (APP |eq| FST . 1)
                                    FST
                                    . 0)
                                   APP
                                   (APP
                                    (APP (APP |injective#U| . 10) . 9)
                                    PAIR
                                    (FST . 8)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 10)
                                     . 9)
                                    . 8)
                                   APP
                                   (APP
                                    (APP |injFuncSetFuncInj| . 10)
                                    . 9)
                                   . 8)
                              . 2)
                         . 4)
                    APP
                    (APP (APP (APP (APP
                                    |symtrans2eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 10) . 9)
                                     PAIR
                                     (FST . 8)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 10)
                                      . 9)
                                     . 8)
                                    . 4)
                                   FST . 6)
                              FST APP
                              (APP (APP (APP |ap2| . 10) . 9) PAIR
                                   (FST . 8) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 10)
                                    . 9)
                                   . 8)
                              . 2)
                         . 3)
                    . 0)
               LAM APP
               (APP (APP (APP |notE| APP (APP |dex| . 10) LAM APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 11) . 10)
                                    PAIR
                                    (FST . 9)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 11)
                                     . 10)
                                    . 9)
                                   . 0)
                              FST . 7)
                         APP (APP |eq| FST . 2) FST . 4)
                    . 5)
               APP
               (APP (APP |andEL| APP |not| APP (APP |dex| . 10) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 11) . 10) PAIR
                                   (FST . 9) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 11)
                                    . 10)
                                   . 9)
                              . 0)
                         FST . 7)
                    APP (APP |eq| FST . 2) FST . 7)
               . 0)
          LAM APP
          (APP (APP (APP (APP |ex1I| . 5) LAM APP
                         (APP |in| APP
                              (APP (APP |dpsetconstr| . 5) . 6) LAM LAM
                              APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 8)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 9) . 8)
                                     PAIR
                                     (FST . 7)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 9)
                                      . 8)
                                     . 7)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 5)
                         FST APP (APP |kpair| FST . 2) FST . 0)
                    . 2)
               APP
               (APP (APP (APP (APP (APP |dpsetconstrI| . 4) . 5) LAM
                              LAM APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 4)
                         . 1)
                    . 2)
               APP
               (APP (APP |orIR| APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 5) . 4) PAIR
                                   (FST . 3) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 5)
                                    . 4)
                                   . 3)
                              . 2)
                         FST . 1)
                    APP
                    (APP |and| APP |not| APP (APP |dex| . 5) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 6) . 5) PAIR
                                   (FST . 4) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 6)
                                    . 5)
                                   . 4)
                              . 0)
                         FST . 2)
                    APP (APP |eq| FST . 2) FST . 2)
               APP
               (APP (APP (APP |andI| APP |not| APP (APP |dex| . 5) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 6) . 5)
                                    PAIR
                                    (FST . 4)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 6)
                                     . 5)
                                    . 4)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 2) FST . 2)
                    . 0)
               APP |eqI| FST . 2)
          LAM LAM APP
          (APP (APP (APP (APP (APP |orE| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 1)
                                   FST . 3)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 4)
                              APP (APP |eq| FST . 1) FST . 4)
                         APP
                         (APP (APP (APP
                                    (APP (APP |dpsetconstrER| . 6) . 7)
                                    LAM
                                    LAM
                                    APP
                                    (APP
                                     |or|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 9) . 8)
                                       PAIR
                                       (FST . 7)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 9)
                                        . 8)
                                       . 7)
                                      . 0)
                                     FST
                                     . 1)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 9)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 10) . 9)
                                       PAIR
                                       (FST . 8)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 10)
                                        . 9)
                                       . 8)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 0)
                                    FST
                                    . 6)
                                   FST . 3)
                              FST . 1)
                         . 0)
                    APP (APP |eq| FST . 1) FST . 4)
               LAM APP (APP |falseE| APP (APP |eq| FST . 2) FST . 5)
               APP
               (APP (APP (APP |notE| APP (APP |dex| . 8) LAM APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 9) . 8)
                                    PAIR
                                    (FST . 7)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 9)
                                     . 8)
                                    . 7)
                                   . 0)
                              FST . 5)
                         . |false|)
                    APP
                    (APP (APP (APP |dexI| . 8) LAM APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 9) . 8)
                                    PAIR
                                    (FST . 7)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 9)
                                     . 8)
                                    . 7)
                                   . 0)
                              FST . 5)
                         . 2)
                    . 0)
               . 3)
          APP
          (APP |andER| APP |not| APP (APP |dex| . 7) LAM APP
               (APP |eq| FST APP
                    (APP (APP (APP |ap2| . 8) . 7) PAIR (FST . 6) APP
                         (APP (APP |injFuncSetFuncIn| . 8) . 7) . 6)
                    . 0)
               FST . 4)
          APP (APP |eq| FST . 1) FST . 4)
     APP
     (APP (APP |dallI| . 3) LAM APP (APP |dex| . 3) LAM APP
          (APP |eq| FST APP
               (APP (APP (APP |ap2| . 4) . 5) PAIR
                    (APP (APP (APP |dpsetconstr| . 4) . 5) LAM LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 4)
                    APP
                    (APP (APP (APP |funcSet#F| . 4) . 5) LAM APP
                         (APP |in| . 0) APP
                         (APP (APP |dpsetconstr| . 5) . 6) LAM LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 8) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 9) . 8)
                                    PAIR
                                    (FST . 7)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 9)
                                     . 8)
                                    . 7)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 5)
                    APP
                    (APP (APP (APP |dsetconstrI| APP |powerset| APP
                                   (APP |cartprod| . 4) . 5)
                              LAM APP (APP (APP |func| . 5) . 6) FST
                              . 0)
                         PAIR
                         (APP (APP (APP |dpsetconstr| . 4) . 5) LAM LAM
                              APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 4)
                         APP
                         (APP (APP |powersetI1| APP
                                   (APP |cartprod| . 4) . 5)
                              APP (APP (APP |dpsetconstr| . 4) . 5) LAM
                              LAM APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 4)
                         APP (APP (APP |dpsetconstrSub| . 4) . 5) LAM
                         LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 4)
                    APP
                    (APP (APP (APP |func#F| . 4) . 5) APP
                         (APP (APP |dpsetconstr| . 4) . 5) LAM LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 4)
                    APP
                    (APP (APP (APP |andI| APP
                                   (APP (APP |breln| . 4) . 5) APP
                                   (APP (APP |dpsetconstr| . 4) . 5)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 7) . 6)
                                      PAIR
                                      (FST . 5)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 7)
                                       . 6)
                                      . 5)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 7)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 8) . 7)
                                      PAIR
                                      (FST . 6)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 8)
                                       . 7)
                                      . 6)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 4)
                              APP (APP |dall| . 4) LAM APP
                              (APP |ex1| . 6) LAM APP
                              (APP |in| APP
                                   (APP (APP |dpsetconstr| . 6) . 7)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 6)
                              FST APP (APP |kpair| FST . 1) FST . 0)
                         APP (APP (APP |setOfPairsIsBReln| . 4) . 5)
                         LAM LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 4)
                    APP
                    (APP (APP |dallI| . 4) LAM APP (APP |ex1| . 6) LAM
                         APP
                         (APP |in| APP
                              (APP (APP |dpsetconstr| . 6) . 7) LAM LAM
                              APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 9) . 8)
                                     PAIR
                                     (FST . 7)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 9)
                                      . 8)
                                     . 7)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 9)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 10) . 9)
                                     PAIR
                                     (FST . 8)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 10)
                                      . 9)
                                     . 8)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 6)
                         FST APP (APP |kpair| FST . 1) FST . 0)
                    LAM APP
                    (APP (APP (APP |xmcases| APP (APP |dex| . 6) LAM
                                   APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 1)
                              APP (APP |ex1| . 6) LAM APP
                              (APP |in| APP
                                   (APP (APP |dpsetconstr| . 6) . 7)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 6)
                              FST APP (APP |kpair| FST . 1) FST . 0)
                         LAM APP
                         (APP (APP (APP
                                    (APP |dexE| . 7)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 8) . 7)
                                      PAIR
                                      (FST . 6)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 8)
                                       . 7)
                                      . 6)
                                     . 0)
                                    FST
                                    . 2)
                                   . 0)
                              APP (APP |ex1| . 7) LAM APP
                              (APP |in| APP
                                   (APP (APP |dpsetconstr| . 7) . 8)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 10)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 11) . 10)
                                      PAIR
                                      (FST . 9)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 11)
                                       . 10)
                                      . 9)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 7)
                              FST APP (APP |kpair| FST . 2) FST . 0)
                         LAM LAM APP
                         (APP (APP (APP
                                    (APP |ex1I| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |in|
                                     APP
                                     (APP (APP |dpsetconstr| . 9) . 10)
                                     LAM
                                     LAM
                                     APP
                                     (APP
                                      |or|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 12) . 11)
                                        PAIR
                                        (FST . 10)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 12)
                                         . 11)
                                        . 10)
                                       . 0)
                                      FST
                                      . 1)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 12)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 13) . 12)
                                        PAIR
                                        (FST . 11)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 13)
                                         . 12)
                                        . 11)
                                       . 0)
                                      FST
                                      . 2)
                                     APP
                                     (APP |eq| FST . 0)
                                     FST
                                     . 9)
                                    FST
                                    APP
                                    (APP |kpair| FST . 4)
                                    FST
                                    . 0)
                                   . 1)
                              APP
                              (APP (APP
                                    (APP
                                     (APP (APP |dpsetconstrI| . 8) . 9)
                                     LAM
                                     LAM
                                     APP
                                     (APP
                                      |or|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 11) . 10)
                                        PAIR
                                        (FST . 9)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 11)
                                         . 10)
                                        . 9)
                                       . 0)
                                      FST
                                      . 1)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 11)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 12) . 11)
                                        PAIR
                                        (FST . 10)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 12)
                                         . 11)
                                        . 10)
                                       . 0)
                                      FST
                                      . 2)
                                     APP
                                     (APP |eq| FST . 0)
                                     FST
                                     . 8)
                                    . 3)
                                   . 1)
                              APP
                              (APP (APP
                                    |orIL|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     . 1)
                                    FST
                                    . 3)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 4)
                                   APP (APP |eq| FST . 1) FST . 6)
                              . 0)
                         LAM LAM APP
                         (APP (APP (APP
                                    (APP
                                     (APP
                                      |orE|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 11) . 10)
                                        PAIR
                                        (FST . 9)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 11)
                                         . 10)
                                        . 9)
                                       PAIR
                                       (FST . 1)
                                       APP
                                       (APP
                                        (APP
                                         (APP
                                          (APP
                                           (APP |dpsetconstrEL2| . 10)
                                           . 11)
                                          LAM
                                          LAM
                                          APP
                                          (APP
                                           |or|
                                           APP
                                           (APP
                                            |eq|
                                            FST
                                            APP
                                            (APP
                                             (APP
                                              (APP |ap2| . 13)
                                              . 12)
                                             PAIR
                                             (FST . 11)
                                             APP
                                             (APP
                                              (APP
                                               |injFuncSetFuncIn|
                                               . 13)
                                              . 12)
                                             . 11)
                                            . 0)
                                           FST
                                           . 1)
                                          APP
                                          (APP
                                           |and|
                                           APP
                                           |not|
                                           APP
                                           (APP |dex| . 13)
                                           LAM
                                           APP
                                           (APP
                                            |eq|
                                            FST
                                            APP
                                            (APP
                                             (APP
                                              (APP |ap2| . 14)
                                              . 13)
                                             PAIR
                                             (FST . 12)
                                             APP
                                             (APP
                                              (APP
                                               |injFuncSetFuncIn|
                                               . 14)
                                              . 13)
                                             . 12)
                                            . 0)
                                           FST
                                           . 2)
                                          APP
                                          (APP |eq| FST . 0)
                                          FST
                                          . 10)
                                         FST
                                         . 5)
                                        FST
                                        . 1)
                                       . 0)
                                      FST
                                      . 5)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 11)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 12) . 11)
                                        PAIR
                                        (FST . 10)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 12)
                                         . 11)
                                        . 10)
                                       . 0)
                                      FST
                                      . 6)
                                     APP
                                     (APP |eq| FST . 1)
                                     FST
                                     . 8)
                                    APP
                                    (APP
                                     (APP
                                      (APP
                                       (APP
                                        (APP |dpsetconstrER| . 10)
                                        . 11)
                                       LAM
                                       LAM
                                       APP
                                       (APP
                                        |or|
                                        APP
                                        (APP
                                         |eq|
                                         FST
                                         APP
                                         (APP
                                          (APP (APP |ap2| . 13) . 12)
                                          PAIR
                                          (FST . 11)
                                          APP
                                          (APP
                                           (APP
                                            |injFuncSetFuncIn|
                                            . 13)
                                           . 12)
                                          . 11)
                                         . 0)
                                        FST
                                        . 1)
                                       APP
                                       (APP
                                        |and|
                                        APP
                                        |not|
                                        APP
                                        (APP |dex| . 13)
                                        LAM
                                        APP
                                        (APP
                                         |eq|
                                         FST
                                         APP
                                         (APP
                                          (APP (APP |ap2| . 14) . 13)
                                          PAIR
                                          (FST . 12)
                                          APP
                                          (APP
                                           (APP
                                            |injFuncSetFuncIn|
                                            . 14)
                                           . 13)
                                          . 12)
                                         . 0)
                                        FST
                                        . 2)
                                       APP
                                       (APP |eq| FST . 0)
                                       FST
                                       . 10)
                                      FST
                                      . 5)
                                     FST
                                     . 1)
                                    . 0)
                                   APP (APP |eq| FST . 1) FST . 3)
                              LAM APP
                              (APP (APP
                                    (APP
                                     |impE|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 12) . 11)
                                       PAIR
                                       (FST . 10)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 12)
                                        . 11)
                                       . 10)
                                      . 2)
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 12) . 11)
                                      PAIR
                                      (FST . 10)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 12)
                                       . 11)
                                      . 10)
                                     . 4)
                                    APP
                                    (APP |eq| FST . 2)
                                    FST
                                    . 4)
                                   APP
                                   (APP
                                    (APP
                                     (APP |dallE| . 12)
                                     LAM
                                     APP
                                     (APP
                                      |imp|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 13) . 12)
                                        PAIR
                                        (FST . 11)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 13)
                                         . 12)
                                        . 11)
                                       . 3)
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 13) . 12)
                                       PAIR
                                       (FST . 11)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 13)
                                        . 12)
                                       . 11)
                                      . 0)
                                     APP
                                     (APP |eq| FST . 3)
                                     FST
                                     . 0)
                                    APP
                                    (APP
                                     (APP
                                      (APP |dallE| . 12)
                                      LAM
                                      APP
                                      (APP |dall| . 13)
                                      LAM
                                      APP
                                      (APP
                                       |imp|
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 14) . 13)
                                         PAIR
                                         (FST . 12)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 14)
                                          . 13)
                                         . 12)
                                        . 1)
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 14) . 13)
                                        PAIR
                                        (FST . 12)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 14)
                                         . 13)
                                        . 12)
                                       . 0)
                                      APP
                                      (APP |eq| FST . 1)
                                      FST
                                      . 0)
                                     APP
                                     (APP
                                      (APP
                                       (APP |injective#U| . 12)
                                       . 11)
                                      PAIR
                                      (FST . 10)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 12)
                                       . 11)
                                      . 10)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncInj| . 12)
                                      . 11)
                                     . 10)
                                    . 2)
                                   . 4)
                              APP
                              (APP (APP
                                    (APP
                                     (APP
                                      |symtrans2eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 12) . 11)
                                       PAIR
                                       (FST . 10)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 12)
                                        . 11)
                                       . 10)
                                      . 4)
                                     FST
                                     . 6)
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 12) . 11)
                                     PAIR
                                     (FST . 10)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 12)
                                      . 11)
                                     . 10)
                                    . 2)
                                   . 3)
                              . 0)
                         LAM APP
                         (APP (APP (APP
                                    |notE|
                                    APP
                                    (APP |dex| . 12)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 13) . 12)
                                      PAIR
                                      (FST . 11)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 13)
                                       . 12)
                                      . 11)
                                     . 0)
                                    FST
                                    . 7)
                                   APP (APP |eq| FST . 2) FST . 4)
                              . 5)
                         APP
                         (APP (APP |andEL| APP |not| APP
                                   (APP |dex| . 12) LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 13) . 12)
                                     PAIR
                                     (FST . 11)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 13)
                                      . 12)
                                     . 11)
                                    . 0)
                                   FST . 7)
                              APP (APP |eq| FST . 2) FST . 9)
                         . 0)
                    LAM APP
                    (APP (APP (APP (APP |ex1I| . 7) LAM APP
                                   (APP
                                    |in|
                                    APP
                                    (APP (APP |dpsetconstr| . 7) . 8)
                                    LAM
                                    LAM
                                    APP
                                    (APP
                                     |or|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 10) . 9)
                                       PAIR
                                       (FST . 8)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 10)
                                        . 9)
                                       . 8)
                                      . 0)
                                     FST
                                     . 1)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 10)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 11) . 10)
                                       PAIR
                                       (FST . 9)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 11)
                                        . 10)
                                       . 9)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 0)
                                    FST
                                    . 7)
                                   FST APP (APP |kpair| FST . 2) FST
                                   . 0)
                              . 4)
                         APP
                         (APP (APP (APP
                                    (APP (APP |dpsetconstrI| . 6) . 7)
                                    LAM
                                    LAM
                                    APP
                                    (APP
                                     |or|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 9) . 8)
                                       PAIR
                                       (FST . 7)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 9)
                                        . 8)
                                       . 7)
                                      . 0)
                                     FST
                                     . 1)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 9)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 10) . 9)
                                       PAIR
                                       (FST . 8)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 10)
                                        . 9)
                                       . 8)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 0)
                                    FST
                                    . 6)
                                   . 1)
                              . 4)
                         APP
                         (APP (APP |orIR| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 4)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 4) FST . 4)
                         APP
                         (APP (APP (APP
                                    |andI|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 7)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 8) . 7)
                                      PAIR
                                      (FST . 6)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 8)
                                       . 7)
                                      . 6)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 4) FST . 4)
                              . 0)
                         APP |eqI| FST . 4)
                    LAM LAM APP
                    (APP (APP (APP (APP
                                    (APP
                                     |orE|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 9) . 8)
                                       PAIR
                                       (FST . 7)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 9)
                                        . 8)
                                       . 7)
                                      . 1)
                                     FST
                                     . 3)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 9)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 10) . 9)
                                       PAIR
                                       (FST . 8)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 10)
                                        . 9)
                                       . 8)
                                      . 0)
                                     FST
                                     . 4)
                                    APP
                                    (APP |eq| FST . 1)
                                    FST
                                    . 6)
                                   APP
                                   (APP
                                    (APP
                                     (APP
                                      (APP
                                       (APP |dpsetconstrER| . 8)
                                       . 9)
                                      LAM
                                      LAM
                                      APP
                                      (APP
                                       |or|
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 11) . 10)
                                         PAIR
                                         (FST . 9)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 11)
                                          . 10)
                                         . 9)
                                        . 0)
                                       FST
                                       . 1)
                                      APP
                                      (APP
                                       |and|
                                       APP
                                       |not|
                                       APP
                                       (APP |dex| . 11)
                                       LAM
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 12) . 11)
                                         PAIR
                                         (FST . 10)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 12)
                                          . 11)
                                         . 10)
                                        . 0)
                                       FST
                                       . 2)
                                      APP
                                      (APP |eq| FST . 0)
                                      FST
                                      . 8)
                                     FST
                                     . 3)
                                    FST
                                    . 1)
                                   . 0)
                              APP (APP |eq| FST . 1) FST . 6)
                         LAM APP
                         (APP |falseE| APP (APP |eq| FST . 2) FST . 7)
                         APP
                         (APP (APP (APP
                                    |notE|
                                    APP
                                    (APP |dex| . 10)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 11) . 10)
                                      PAIR
                                      (FST . 9)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 11)
                                       . 10)
                                      . 9)
                                     . 0)
                                    FST
                                    . 5)
                                   . |false|)
                              APP
                              (APP (APP
                                    (APP |dexI| . 10)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 11) . 10)
                                      PAIR
                                      (FST . 9)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 11)
                                       . 10)
                                      . 9)
                                     . 0)
                                    FST
                                    . 5)
                                   . 2)
                              . 0)
                         . 3)
                    APP
                    (APP |andER| APP |not| APP (APP |dex| . 9) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 10) . 9) PAIR
                                   (FST . 8) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 10)
                                    . 9)
                                   . 8)
                              . 0)
                         FST . 4)
                    APP (APP |eq| FST . 1) FST . 6)
               . 0)
          FST . 1)
     LAM APP
     (APP (APP (APP |dexI| . 3) LAM APP
               (APP |eq| FST APP
                    (APP (APP (APP |ap2| . 4) . 5) PAIR
                         (APP (APP (APP |dpsetconstr| . 4) . 5) LAM LAM
                              APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 4)
                         APP
                         (APP (APP (APP |funcSet#F| . 4) . 5) LAM APP
                              (APP |in| . 0) APP
                              (APP (APP |dpsetconstr| . 5) . 6) LAM LAM
                              APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 8)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 9) . 8)
                                     PAIR
                                     (FST . 7)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 9)
                                      . 8)
                                     . 7)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 5)
                         APP
                         (APP (APP (APP
                                    |dsetconstrI|
                                    APP
                                    |powerset|
                                    APP
                                    (APP |cartprod| . 4)
                                    . 5)
                                   LAM APP (APP (APP |func| . 5) . 6)
                                   FST . 0)
                              PAIR
                              (APP (APP (APP |dpsetconstr| . 4) . 5)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 7) . 6)
                                      PAIR
                                      (FST . 5)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 7)
                                       . 6)
                                      . 5)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 7)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 8) . 7)
                                      PAIR
                                      (FST . 6)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 8)
                                       . 7)
                                      . 6)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 4)
                              APP
                              (APP (APP
                                    |powersetI1|
                                    APP
                                    (APP |cartprod| . 4)
                                    . 5)
                                   APP
                                   (APP (APP |dpsetconstr| . 4) . 5)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 7) . 6)
                                      PAIR
                                      (FST . 5)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 7)
                                       . 6)
                                      . 5)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 7)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 8) . 7)
                                      PAIR
                                      (FST . 6)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 8)
                                       . 7)
                                      . 6)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 4)
                              APP (APP (APP |dpsetconstrSub| . 4) . 5)
                              LAM LAM APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 4)
                         APP
                         (APP (APP (APP |func#F| . 4) . 5) APP
                              (APP (APP |dpsetconstr| . 4) . 5) LAM LAM
                              APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 4)
                         APP
                         (APP (APP (APP
                                    |andI|
                                    APP
                                    (APP (APP |breln| . 4) . 5)
                                    APP
                                    (APP (APP |dpsetconstr| . 4) . 5)
                                    LAM
                                    LAM
                                    APP
                                    (APP
                                     |or|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 7) . 6)
                                       PAIR
                                       (FST . 5)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 7)
                                        . 6)
                                       . 5)
                                      . 0)
                                     FST
                                     . 1)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 7)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 8) . 7)
                                       PAIR
                                       (FST . 6)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 8)
                                        . 7)
                                       . 6)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 0)
                                    FST
                                    . 4)
                                   APP (APP |dall| . 4) LAM APP
                                   (APP |ex1| . 6) LAM APP
                                   (APP
                                    |in|
                                    APP
                                    (APP (APP |dpsetconstr| . 6) . 7)
                                    LAM
                                    LAM
                                    APP
                                    (APP
                                     |or|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 9) . 8)
                                       PAIR
                                       (FST . 7)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 9)
                                        . 8)
                                       . 7)
                                      . 0)
                                     FST
                                     . 1)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 9)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 10) . 9)
                                       PAIR
                                       (FST . 8)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 10)
                                        . 9)
                                       . 8)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 0)
                                    FST
                                    . 6)
                                   FST APP (APP |kpair| FST . 1) FST
                                   . 0)
                              APP
                              (APP (APP |setOfPairsIsBReln| . 4) . 5)
                              LAM LAM APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 7)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 4)
                         APP
                         (APP (APP |dallI| . 4) LAM APP (APP |ex1| . 6)
                              LAM APP
                              (APP |in| APP
                                   (APP (APP |dpsetconstr| . 6) . 7)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 6)
                              FST APP (APP |kpair| FST . 1) FST . 0)
                         LAM APP
                         (APP (APP (APP
                                    |xmcases|
                                    APP
                                    (APP |dex| . 6)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 7) . 6)
                                      PAIR
                                      (FST . 5)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 7)
                                       . 6)
                                      . 5)
                                     . 0)
                                    FST
                                    . 1)
                                   APP (APP |ex1| . 6) LAM APP
                                   (APP
                                    |in|
                                    APP
                                    (APP (APP |dpsetconstr| . 6) . 7)
                                    LAM
                                    LAM
                                    APP
                                    (APP
                                     |or|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 9) . 8)
                                       PAIR
                                       (FST . 7)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 9)
                                        . 8)
                                       . 7)
                                      . 0)
                                     FST
                                     . 1)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 9)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 10) . 9)
                                       PAIR
                                       (FST . 8)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 10)
                                        . 9)
                                       . 8)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 0)
                                    FST
                                    . 6)
                                   FST APP (APP |kpair| FST . 1) FST
                                   . 0)
                              LAM APP
                              (APP (APP
                                    (APP
                                     (APP |dexE| . 7)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 8) . 7)
                                       PAIR
                                       (FST . 6)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 8)
                                        . 7)
                                       . 6)
                                      . 0)
                                     FST
                                     . 2)
                                    . 0)
                                   APP (APP |ex1| . 7) LAM APP
                                   (APP
                                    |in|
                                    APP
                                    (APP (APP |dpsetconstr| . 7) . 8)
                                    LAM
                                    LAM
                                    APP
                                    (APP
                                     |or|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 10) . 9)
                                       PAIR
                                       (FST . 8)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 10)
                                        . 9)
                                       . 8)
                                      . 0)
                                     FST
                                     . 1)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 10)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 11) . 10)
                                       PAIR
                                       (FST . 9)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 11)
                                        . 10)
                                       . 9)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 0)
                                    FST
                                    . 7)
                                   FST APP (APP |kpair| FST . 2) FST
                                   . 0)
                              LAM LAM APP
                              (APP (APP
                                    (APP
                                     (APP |ex1I| . 9)
                                     LAM
                                     APP
                                     (APP
                                      |in|
                                      APP
                                      (APP
                                       (APP |dpsetconstr| . 9)
                                       . 10)
                                      LAM
                                      LAM
                                      APP
                                      (APP
                                       |or|
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 12) . 11)
                                         PAIR
                                         (FST . 10)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 12)
                                          . 11)
                                         . 10)
                                        . 0)
                                       FST
                                       . 1)
                                      APP
                                      (APP
                                       |and|
                                       APP
                                       |not|
                                       APP
                                       (APP |dex| . 12)
                                       LAM
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 13) . 12)
                                         PAIR
                                         (FST . 11)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 13)
                                          . 12)
                                         . 11)
                                        . 0)
                                       FST
                                       . 2)
                                      APP
                                      (APP |eq| FST . 0)
                                      FST
                                      . 9)
                                     FST
                                     APP
                                     (APP |kpair| FST . 4)
                                     FST
                                     . 0)
                                    . 1)
                                   APP
                                   (APP
                                    (APP
                                     (APP
                                      (APP
                                       (APP |dpsetconstrI| . 8)
                                       . 9)
                                      LAM
                                      LAM
                                      APP
                                      (APP
                                       |or|
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 11) . 10)
                                         PAIR
                                         (FST . 9)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 11)
                                          . 10)
                                         . 9)
                                        . 0)
                                       FST
                                       . 1)
                                      APP
                                      (APP
                                       |and|
                                       APP
                                       |not|
                                       APP
                                       (APP |dex| . 11)
                                       LAM
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 12) . 11)
                                         PAIR
                                         (FST . 10)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 12)
                                          . 11)
                                         . 10)
                                        . 0)
                                       FST
                                       . 2)
                                      APP
                                      (APP |eq| FST . 0)
                                      FST
                                      . 8)
                                     . 3)
                                    . 1)
                                   APP
                                   (APP
                                    (APP
                                     |orIL|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 9) . 8)
                                       PAIR
                                       (FST . 7)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 9)
                                        . 8)
                                       . 7)
                                      . 1)
                                     FST
                                     . 3)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 9)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 10) . 9)
                                       PAIR
                                       (FST . 8)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 10)
                                        . 9)
                                       . 8)
                                      . 0)
                                     FST
                                     . 4)
                                    APP
                                    (APP |eq| FST . 1)
                                    FST
                                    . 6)
                                   . 0)
                              LAM LAM APP
                              (APP (APP
                                    (APP
                                     (APP
                                      (APP
                                       |orE|
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 11) . 10)
                                         PAIR
                                         (FST . 9)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 11)
                                          . 10)
                                         . 9)
                                        PAIR
                                        (FST . 1)
                                        APP
                                        (APP
                                         (APP
                                          (APP
                                           (APP
                                            (APP |dpsetconstrEL2| . 10)
                                            . 11)
                                           LAM
                                           LAM
                                           APP
                                           (APP
                                            |or|
                                            APP
                                            (APP
                                             |eq|
                                             FST
                                             APP
                                             (APP
                                              (APP
                                               (APP |ap2| . 13)
                                               . 12)
                                              PAIR
                                              (FST . 11)
                                              APP
                                              (APP
                                               (APP
                                                |injFuncSetFuncIn|
                                                . 13)
                                               . 12)
                                              . 11)
                                             . 0)
                                            FST
                                            . 1)
                                           APP
                                           (APP
                                            |and|
                                            APP
                                            |not|
                                            APP
                                            (APP |dex| . 13)
                                            LAM
                                            APP
                                            (APP
                                             |eq|
                                             FST
                                             APP
                                             (APP
                                              (APP
                                               (APP |ap2| . 14)
                                               . 13)
                                              PAIR
                                              (FST . 12)
                                              APP
                                              (APP
                                               (APP
                                                |injFuncSetFuncIn|
                                                . 14)
                                               . 13)
                                              . 12)
                                             . 0)
                                            FST
                                            . 2)
                                           APP
                                           (APP |eq| FST . 0)
                                           FST
                                           . 10)
                                          FST
                                          . 5)
                                         FST
                                         . 1)
                                        . 0)
                                       FST
                                       . 5)
                                      APP
                                      (APP
                                       |and|
                                       APP
                                       |not|
                                       APP
                                       (APP |dex| . 11)
                                       LAM
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 12) . 11)
                                         PAIR
                                         (FST . 10)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 12)
                                          . 11)
                                         . 10)
                                        . 0)
                                       FST
                                       . 6)
                                      APP
                                      (APP |eq| FST . 1)
                                      FST
                                      . 8)
                                     APP
                                     (APP
                                      (APP
                                       (APP
                                        (APP
                                         (APP |dpsetconstrER| . 10)
                                         . 11)
                                        LAM
                                        LAM
                                        APP
                                        (APP
                                         |or|
                                         APP
                                         (APP
                                          |eq|
                                          FST
                                          APP
                                          (APP
                                           (APP (APP |ap2| . 13) . 12)
                                           PAIR
                                           (FST . 11)
                                           APP
                                           (APP
                                            (APP
                                             |injFuncSetFuncIn|
                                             . 13)
                                            . 12)
                                           . 11)
                                          . 0)
                                         FST
                                         . 1)
                                        APP
                                        (APP
                                         |and|
                                         APP
                                         |not|
                                         APP
                                         (APP |dex| . 13)
                                         LAM
                                         APP
                                         (APP
                                          |eq|
                                          FST
                                          APP
                                          (APP
                                           (APP (APP |ap2| . 14) . 13)
                                           PAIR
                                           (FST . 12)
                                           APP
                                           (APP
                                            (APP
                                             |injFuncSetFuncIn|
                                             . 14)
                                            . 13)
                                           . 12)
                                          . 0)
                                         FST
                                         . 2)
                                        APP
                                        (APP |eq| FST . 0)
                                        FST
                                        . 10)
                                       FST
                                       . 5)
                                      FST
                                      . 1)
                                     . 0)
                                    APP
                                    (APP |eq| FST . 1)
                                    FST
                                    . 3)
                                   LAM APP
                                   (APP
                                    (APP
                                     (APP
                                      |impE|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 12) . 11)
                                        PAIR
                                        (FST . 10)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 12)
                                         . 11)
                                        . 10)
                                       . 2)
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 12) . 11)
                                       PAIR
                                       (FST . 10)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 12)
                                        . 11)
                                       . 10)
                                      . 4)
                                     APP
                                     (APP |eq| FST . 2)
                                     FST
                                     . 4)
                                    APP
                                    (APP
                                     (APP
                                      (APP |dallE| . 12)
                                      LAM
                                      APP
                                      (APP
                                       |imp|
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 13) . 12)
                                         PAIR
                                         (FST . 11)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 13)
                                          . 12)
                                         . 11)
                                        . 3)
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 13) . 12)
                                        PAIR
                                        (FST . 11)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 13)
                                         . 12)
                                        . 11)
                                       . 0)
                                      APP
                                      (APP |eq| FST . 3)
                                      FST
                                      . 0)
                                     APP
                                     (APP
                                      (APP
                                       (APP |dallE| . 12)
                                       LAM
                                       APP
                                       (APP |dall| . 13)
                                       LAM
                                       APP
                                       (APP
                                        |imp|
                                        APP
                                        (APP
                                         |eq|
                                         FST
                                         APP
                                         (APP
                                          (APP (APP |ap2| . 14) . 13)
                                          PAIR
                                          (FST . 12)
                                          APP
                                          (APP
                                           (APP
                                            |injFuncSetFuncIn|
                                            . 14)
                                           . 13)
                                          . 12)
                                         . 1)
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 14) . 13)
                                         PAIR
                                         (FST . 12)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 14)
                                          . 13)
                                         . 12)
                                        . 0)
                                       APP
                                       (APP |eq| FST . 1)
                                       FST
                                       . 0)
                                      APP
                                      (APP
                                       (APP
                                        (APP |injective#U| . 12)
                                        . 11)
                                       PAIR
                                       (FST . 10)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 12)
                                        . 11)
                                       . 10)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncInj| . 12)
                                       . 11)
                                      . 10)
                                     . 2)
                                    . 4)
                                   APP
                                   (APP
                                    (APP
                                     (APP
                                      (APP
                                       |symtrans2eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 12) . 11)
                                        PAIR
                                        (FST . 10)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 12)
                                         . 11)
                                        . 10)
                                       . 4)
                                      FST
                                      . 6)
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 12) . 11)
                                      PAIR
                                      (FST . 10)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 12)
                                       . 11)
                                      . 10)
                                     . 2)
                                    . 3)
                                   . 0)
                              LAM APP
                              (APP (APP
                                    (APP
                                     |notE|
                                     APP
                                     (APP |dex| . 12)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 13) . 12)
                                       PAIR
                                       (FST . 11)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 13)
                                        . 12)
                                       . 11)
                                      . 0)
                                     FST
                                     . 7)
                                    APP
                                    (APP |eq| FST . 2)
                                    FST
                                    . 4)
                                   . 5)
                              APP
                              (APP (APP
                                    |andEL|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 12)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 13) . 12)
                                      PAIR
                                      (FST . 11)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 13)
                                       . 12)
                                      . 11)
                                     . 0)
                                    FST
                                    . 7)
                                   APP (APP |eq| FST . 2) FST . 9)
                              . 0)
                         LAM APP
                         (APP (APP (APP
                                    (APP |ex1I| . 7)
                                    LAM
                                    APP
                                    (APP
                                     |in|
                                     APP
                                     (APP (APP |dpsetconstr| . 7) . 8)
                                     LAM
                                     LAM
                                     APP
                                     (APP
                                      |or|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 10) . 9)
                                        PAIR
                                        (FST . 8)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 10)
                                         . 9)
                                        . 8)
                                       . 0)
                                      FST
                                      . 1)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 10)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 11) . 10)
                                        PAIR
                                        (FST . 9)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 11)
                                         . 10)
                                        . 9)
                                       . 0)
                                      FST
                                      . 2)
                                     APP
                                     (APP |eq| FST . 0)
                                     FST
                                     . 7)
                                    FST
                                    APP
                                    (APP |kpair| FST . 2)
                                    FST
                                    . 0)
                                   . 4)
                              APP
                              (APP (APP
                                    (APP
                                     (APP (APP |dpsetconstrI| . 6) . 7)
                                     LAM
                                     LAM
                                     APP
                                     (APP
                                      |or|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 9) . 8)
                                        PAIR
                                        (FST . 7)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 9)
                                         . 8)
                                        . 7)
                                       . 0)
                                      FST
                                      . 1)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 9)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 10) . 9)
                                        PAIR
                                        (FST . 8)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 10)
                                         . 9)
                                        . 8)
                                       . 0)
                                      FST
                                      . 2)
                                     APP
                                     (APP |eq| FST . 0)
                                     FST
                                     . 6)
                                    . 1)
                                   . 4)
                              APP
                              (APP (APP
                                    |orIR|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 7) . 6)
                                      PAIR
                                      (FST . 5)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 7)
                                       . 6)
                                      . 5)
                                     . 4)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 7)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 8) . 7)
                                      PAIR
                                      (FST . 6)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 8)
                                       . 7)
                                      . 6)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 4) FST . 4)
                              APP
                              (APP (APP
                                    (APP
                                     |andI|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 7)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 8) . 7)
                                       PAIR
                                       (FST . 6)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 8)
                                        . 7)
                                       . 6)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 4)
                                    FST
                                    . 4)
                                   . 0)
                              APP |eqI| FST . 4)
                         LAM LAM APP
                         (APP (APP (APP
                                    (APP
                                     (APP
                                      |orE|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 9) . 8)
                                        PAIR
                                        (FST . 7)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 9)
                                         . 8)
                                        . 7)
                                       . 1)
                                      FST
                                      . 3)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 9)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 10) . 9)
                                        PAIR
                                        (FST . 8)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 10)
                                         . 9)
                                        . 8)
                                       . 0)
                                      FST
                                      . 4)
                                     APP
                                     (APP |eq| FST . 1)
                                     FST
                                     . 6)
                                    APP
                                    (APP
                                     (APP
                                      (APP
                                       (APP
                                        (APP |dpsetconstrER| . 8)
                                        . 9)
                                       LAM
                                       LAM
                                       APP
                                       (APP
                                        |or|
                                        APP
                                        (APP
                                         |eq|
                                         FST
                                         APP
                                         (APP
                                          (APP (APP |ap2| . 11) . 10)
                                          PAIR
                                          (FST . 9)
                                          APP
                                          (APP
                                           (APP
                                            |injFuncSetFuncIn|
                                            . 11)
                                           . 10)
                                          . 9)
                                         . 0)
                                        FST
                                        . 1)
                                       APP
                                       (APP
                                        |and|
                                        APP
                                        |not|
                                        APP
                                        (APP |dex| . 11)
                                        LAM
                                        APP
                                        (APP
                                         |eq|
                                         FST
                                         APP
                                         (APP
                                          (APP (APP |ap2| . 12) . 11)
                                          PAIR
                                          (FST . 10)
                                          APP
                                          (APP
                                           (APP
                                            |injFuncSetFuncIn|
                                            . 12)
                                           . 11)
                                          . 10)
                                         . 0)
                                        FST
                                        . 2)
                                       APP
                                       (APP |eq| FST . 0)
                                       FST
                                       . 8)
                                      FST
                                      . 3)
                                     FST
                                     . 1)
                                    . 0)
                                   APP (APP |eq| FST . 1) FST . 6)
                              LAM APP
                              (APP |falseE| APP (APP |eq| FST . 2) FST
                                   . 7)
                              APP
                              (APP (APP
                                    (APP
                                     |notE|
                                     APP
                                     (APP |dex| . 10)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 11) . 10)
                                       PAIR
                                       (FST . 9)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 11)
                                        . 10)
                                       . 9)
                                      . 0)
                                     FST
                                     . 5)
                                    . |false|)
                                   APP
                                   (APP
                                    (APP
                                     (APP |dexI| . 10)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 11) . 10)
                                       PAIR
                                       (FST . 9)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 11)
                                        . 10)
                                       . 9)
                                      . 0)
                                     FST
                                     . 5)
                                    . 2)
                                   . 0)
                              . 3)
                         APP
                         (APP |andER| APP |not| APP (APP |dex| . 9) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 10) . 9)
                                    PAIR
                                    (FST . 8)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 10)
                                     . 9)
                                    . 8)
                                   . 0)
                              FST . 4)
                         APP (APP |eq| FST . 1) FST . 6)
                    . 0)
               FST . 1)
          APP
          (APP (APP (APP |ap2| . 4) . 3) PAIR (FST . 2) APP
               (APP (APP |injFuncSetFuncIn| . 4) . 3) . 2)
          . 0)
     APP
     (APP (APP (APP (APP (APP |funcGraphProp4| . 3) . 4) PAIR
                    (APP (APP (APP |dpsetconstr| . 3) . 4) LAM LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 6) . 5)
                                    PAIR
                                    (FST . 4)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 6)
                                     . 5)
                                    . 4)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 6) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 3)
                    APP
                    (APP (APP (APP |funcSet#F| . 3) . 4) LAM APP
                         (APP |in| . 0) APP
                         (APP (APP |dpsetconstr| . 4) . 5) LAM LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 7) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 8) . 7)
                                    PAIR
                                    (FST . 6)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 8)
                                     . 7)
                                    . 6)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 4)
                    APP
                    (APP (APP (APP |dsetconstrI| APP |powerset| APP
                                   (APP |cartprod| . 3) . 4)
                              LAM APP (APP (APP |func| . 4) . 5) FST
                              . 0)
                         PAIR
                         (APP (APP (APP |dpsetconstr| . 3) . 4) LAM LAM
                              APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 6) . 5)
                                     PAIR
                                     (FST . 4)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 6)
                                      . 5)
                                     . 4)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 6)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 3)
                         APP
                         (APP (APP |powersetI1| APP
                                   (APP |cartprod| . 3) . 4)
                              APP (APP (APP |dpsetconstr| . 3) . 4) LAM
                              LAM APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 6) . 5)
                                     PAIR
                                     (FST . 4)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 6)
                                      . 5)
                                     . 4)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 6)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 3)
                         APP (APP (APP |dpsetconstrSub| . 3) . 4) LAM
                         LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 6) . 5)
                                    PAIR
                                    (FST . 4)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 6)
                                     . 5)
                                    . 4)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 6) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 3)
                    APP
                    (APP (APP (APP |func#F| . 3) . 4) APP
                         (APP (APP |dpsetconstr| . 3) . 4) LAM LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 6) . 5)
                                    PAIR
                                    (FST . 4)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 6)
                                     . 5)
                                    . 4)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 6) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 3)
                    APP
                    (APP (APP (APP |andI| APP
                                   (APP (APP |breln| . 3) . 4) APP
                                   (APP (APP |dpsetconstr| . 3) . 4)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 6) . 5)
                                      PAIR
                                      (FST . 4)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 6)
                                       . 5)
                                      . 4)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 6)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 7) . 6)
                                      PAIR
                                      (FST . 5)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 7)
                                       . 6)
                                      . 5)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 3)
                              APP (APP |dall| . 3) LAM APP
                              (APP |ex1| . 5) LAM APP
                              (APP |in| APP
                                   (APP (APP |dpsetconstr| . 5) . 6)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 8) . 7)
                                      PAIR
                                      (FST . 6)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 8)
                                       . 7)
                                      . 6)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 8)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 5)
                              FST APP (APP |kpair| FST . 1) FST . 0)
                         APP (APP (APP |setOfPairsIsBReln| . 3) . 4)
                         LAM LAM APP
                         (APP |or| APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 6) . 5)
                                    PAIR
                                    (FST . 4)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 6)
                                     . 5)
                                    . 4)
                                   . 0)
                              FST . 1)
                         APP
                         (APP |and| APP |not| APP (APP |dex| . 6) LAM
                              APP
                              (APP |eq| FST APP
                                   (APP
                                    (APP (APP |ap2| . 7) . 6)
                                    PAIR
                                    (FST . 5)
                                    APP
                                    (APP
                                     (APP |injFuncSetFuncIn| . 7)
                                     . 6)
                                    . 5)
                                   . 0)
                              FST . 2)
                         APP (APP |eq| FST . 0) FST . 3)
                    APP
                    (APP (APP |dallI| . 3) LAM APP (APP |ex1| . 5) LAM
                         APP
                         (APP |in| APP
                              (APP (APP |dpsetconstr| . 5) . 6) LAM LAM
                              APP
                              (APP |or| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 8) . 7)
                                     PAIR
                                     (FST . 6)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 8)
                                      . 7)
                                     . 6)
                                    . 0)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 8)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 9) . 8)
                                     PAIR
                                     (FST . 7)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 9)
                                      . 8)
                                     . 7)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 0) FST . 5)
                         FST APP (APP |kpair| FST . 1) FST . 0)
                    LAM APP
                    (APP (APP (APP |xmcases| APP (APP |dex| . 5) LAM
                                   APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 6) . 5)
                                     PAIR
                                     (FST . 4)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 6)
                                      . 5)
                                     . 4)
                                    . 0)
                                   FST . 1)
                              APP (APP |ex1| . 5) LAM APP
                              (APP |in| APP
                                   (APP (APP |dpsetconstr| . 5) . 6)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 8) . 7)
                                      PAIR
                                      (FST . 6)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 8)
                                       . 7)
                                      . 6)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 8)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 5)
                              FST APP (APP |kpair| FST . 1) FST . 0)
                         LAM APP
                         (APP (APP (APP
                                    (APP |dexE| . 6)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 7) . 6)
                                      PAIR
                                      (FST . 5)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 7)
                                       . 6)
                                      . 5)
                                     . 0)
                                    FST
                                    . 2)
                                   . 0)
                              APP (APP |ex1| . 6) LAM APP
                              (APP |in| APP
                                   (APP (APP |dpsetconstr| . 6) . 7)
                                   LAM LAM APP
                                   (APP
                                    |or|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     . 0)
                                    FST
                                    . 1)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 0) FST . 6)
                              FST APP (APP |kpair| FST . 2) FST . 0)
                         LAM LAM APP
                         (APP (APP (APP
                                    (APP |ex1I| . 8)
                                    LAM
                                    APP
                                    (APP
                                     |in|
                                     APP
                                     (APP (APP |dpsetconstr| . 8) . 9)
                                     LAM
                                     LAM
                                     APP
                                     (APP
                                      |or|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 11) . 10)
                                        PAIR
                                        (FST . 9)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 11)
                                         . 10)
                                        . 9)
                                       . 0)
                                      FST
                                      . 1)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 11)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 12) . 11)
                                        PAIR
                                        (FST . 10)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 12)
                                         . 11)
                                        . 10)
                                       . 0)
                                      FST
                                      . 2)
                                     APP
                                     (APP |eq| FST . 0)
                                     FST
                                     . 8)
                                    FST
                                    APP
                                    (APP |kpair| FST . 4)
                                    FST
                                    . 0)
                                   . 1)
                              APP
                              (APP (APP
                                    (APP
                                     (APP (APP |dpsetconstrI| . 7) . 8)
                                     LAM
                                     LAM
                                     APP
                                     (APP
                                      |or|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 10) . 9)
                                        PAIR
                                        (FST . 8)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 10)
                                         . 9)
                                        . 8)
                                       . 0)
                                      FST
                                      . 1)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 10)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 11) . 10)
                                        PAIR
                                        (FST . 9)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 11)
                                         . 10)
                                        . 9)
                                       . 0)
                                      FST
                                      . 2)
                                     APP
                                     (APP |eq| FST . 0)
                                     FST
                                     . 7)
                                    . 3)
                                   . 1)
                              APP
                              (APP (APP
                                    |orIL|
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 8) . 7)
                                      PAIR
                                      (FST . 6)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 8)
                                       . 7)
                                      . 6)
                                     . 1)
                                    FST
                                    . 3)
                                   APP
                                   (APP
                                    |and|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 8)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 9) . 8)
                                      PAIR
                                      (FST . 7)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 9)
                                       . 8)
                                      . 7)
                                     . 0)
                                    FST
                                    . 4)
                                   APP (APP |eq| FST . 1) FST . 5)
                              . 0)
                         LAM LAM APP
                         (APP (APP (APP
                                    (APP
                                     (APP
                                      |orE|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 10) . 9)
                                        PAIR
                                        (FST . 8)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 10)
                                         . 9)
                                        . 8)
                                       PAIR
                                       (FST . 1)
                                       APP
                                       (APP
                                        (APP
                                         (APP
                                          (APP
                                           (APP |dpsetconstrEL2| . 9)
                                           . 10)
                                          LAM
                                          LAM
                                          APP
                                          (APP
                                           |or|
                                           APP
                                           (APP
                                            |eq|
                                            FST
                                            APP
                                            (APP
                                             (APP
                                              (APP |ap2| . 12)
                                              . 11)
                                             PAIR
                                             (FST . 10)
                                             APP
                                             (APP
                                              (APP
                                               |injFuncSetFuncIn|
                                               . 12)
                                              . 11)
                                             . 10)
                                            . 0)
                                           FST
                                           . 1)
                                          APP
                                          (APP
                                           |and|
                                           APP
                                           |not|
                                           APP
                                           (APP |dex| . 12)
                                           LAM
                                           APP
                                           (APP
                                            |eq|
                                            FST
                                            APP
                                            (APP
                                             (APP
                                              (APP |ap2| . 13)
                                              . 12)
                                             PAIR
                                             (FST . 11)
                                             APP
                                             (APP
                                              (APP
                                               |injFuncSetFuncIn|
                                               . 13)
                                              . 12)
                                             . 11)
                                            . 0)
                                           FST
                                           . 2)
                                          APP
                                          (APP |eq| FST . 0)
                                          FST
                                          . 9)
                                         FST
                                         . 5)
                                        FST
                                        . 1)
                                       . 0)
                                      FST
                                      . 5)
                                     APP
                                     (APP
                                      |and|
                                      APP
                                      |not|
                                      APP
                                      (APP |dex| . 10)
                                      LAM
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 11) . 10)
                                        PAIR
                                        (FST . 9)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 11)
                                         . 10)
                                        . 9)
                                       . 0)
                                      FST
                                      . 6)
                                     APP
                                     (APP |eq| FST . 1)
                                     FST
                                     . 7)
                                    APP
                                    (APP
                                     (APP
                                      (APP
                                       (APP
                                        (APP |dpsetconstrER| . 9)
                                        . 10)
                                       LAM
                                       LAM
                                       APP
                                       (APP
                                        |or|
                                        APP
                                        (APP
                                         |eq|
                                         FST
                                         APP
                                         (APP
                                          (APP (APP |ap2| . 12) . 11)
                                          PAIR
                                          (FST . 10)
                                          APP
                                          (APP
                                           (APP
                                            |injFuncSetFuncIn|
                                            . 12)
                                           . 11)
                                          . 10)
                                         . 0)
                                        FST
                                        . 1)
                                       APP
                                       (APP
                                        |and|
                                        APP
                                        |not|
                                        APP
                                        (APP |dex| . 12)
                                        LAM
                                        APP
                                        (APP
                                         |eq|
                                         FST
                                         APP
                                         (APP
                                          (APP (APP |ap2| . 13) . 12)
                                          PAIR
                                          (FST . 11)
                                          APP
                                          (APP
                                           (APP
                                            |injFuncSetFuncIn|
                                            . 13)
                                           . 12)
                                          . 11)
                                         . 0)
                                        FST
                                        . 2)
                                       APP
                                       (APP |eq| FST . 0)
                                       FST
                                       . 9)
                                      FST
                                      . 5)
                                     FST
                                     . 1)
                                    . 0)
                                   APP (APP |eq| FST . 1) FST . 3)
                              LAM APP
                              (APP (APP
                                    (APP
                                     |impE|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 11) . 10)
                                       PAIR
                                       (FST . 9)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 11)
                                        . 10)
                                       . 9)
                                      . 2)
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 11) . 10)
                                      PAIR
                                      (FST . 9)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 11)
                                       . 10)
                                      . 9)
                                     . 4)
                                    APP
                                    (APP |eq| FST . 2)
                                    FST
                                    . 4)
                                   APP
                                   (APP
                                    (APP
                                     (APP |dallE| . 11)
                                     LAM
                                     APP
                                     (APP
                                      |imp|
                                      APP
                                      (APP
                                       |eq|
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 12) . 11)
                                        PAIR
                                        (FST . 10)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 12)
                                         . 11)
                                        . 10)
                                       . 3)
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 12) . 11)
                                       PAIR
                                       (FST . 10)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 12)
                                        . 11)
                                       . 10)
                                      . 0)
                                     APP
                                     (APP |eq| FST . 3)
                                     FST
                                     . 0)
                                    APP
                                    (APP
                                     (APP
                                      (APP |dallE| . 11)
                                      LAM
                                      APP
                                      (APP |dall| . 12)
                                      LAM
                                      APP
                                      (APP
                                       |imp|
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 13) . 12)
                                         PAIR
                                         (FST . 11)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 13)
                                          . 12)
                                         . 11)
                                        . 1)
                                       FST
                                       APP
                                       (APP
                                        (APP (APP |ap2| . 13) . 12)
                                        PAIR
                                        (FST . 11)
                                        APP
                                        (APP
                                         (APP |injFuncSetFuncIn| . 13)
                                         . 12)
                                        . 11)
                                       . 0)
                                      APP
                                      (APP |eq| FST . 1)
                                      FST
                                      . 0)
                                     APP
                                     (APP
                                      (APP
                                       (APP |injective#U| . 11)
                                       . 10)
                                      PAIR
                                      (FST . 9)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 11)
                                       . 10)
                                      . 9)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncInj| . 11)
                                      . 10)
                                     . 9)
                                    . 2)
                                   . 4)
                              APP
                              (APP (APP
                                    (APP
                                     (APP
                                      |symtrans2eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 11) . 10)
                                       PAIR
                                       (FST . 9)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 11)
                                        . 10)
                                       . 9)
                                      . 4)
                                     FST
                                     . 6)
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 11) . 10)
                                     PAIR
                                     (FST . 9)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 11)
                                      . 10)
                                     . 9)
                                    . 2)
                                   . 3)
                              . 0)
                         LAM APP
                         (APP (APP (APP
                                    |notE|
                                    APP
                                    (APP |dex| . 11)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 12) . 11)
                                      PAIR
                                      (FST . 10)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 12)
                                       . 11)
                                      . 10)
                                     . 0)
                                    FST
                                    . 7)
                                   APP (APP |eq| FST . 2) FST . 4)
                              . 5)
                         APP
                         (APP (APP |andEL| APP |not| APP
                                   (APP |dex| . 11) LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 12) . 11)
                                     PAIR
                                     (FST . 10)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 12)
                                      . 11)
                                     . 10)
                                    . 0)
                                   FST . 7)
                              APP (APP |eq| FST . 2) FST . 8)
                         . 0)
                    LAM APP
                    (APP (APP (APP (APP |ex1I| . 6) LAM APP
                                   (APP
                                    |in|
                                    APP
                                    (APP (APP |dpsetconstr| . 6) . 7)
                                    LAM
                                    LAM
                                    APP
                                    (APP
                                     |or|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 9) . 8)
                                       PAIR
                                       (FST . 7)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 9)
                                        . 8)
                                       . 7)
                                      . 0)
                                     FST
                                     . 1)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 9)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 10) . 9)
                                       PAIR
                                       (FST . 8)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 10)
                                        . 9)
                                       . 8)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 0)
                                    FST
                                    . 6)
                                   FST APP (APP |kpair| FST . 2) FST
                                   . 0)
                              . 3)
                         APP
                         (APP (APP (APP
                                    (APP (APP |dpsetconstrI| . 5) . 6)
                                    LAM
                                    LAM
                                    APP
                                    (APP
                                     |or|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 8) . 7)
                                       PAIR
                                       (FST . 6)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 8)
                                        . 7)
                                       . 6)
                                      . 0)
                                     FST
                                     . 1)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 8)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 9) . 8)
                                       PAIR
                                       (FST . 7)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 9)
                                        . 8)
                                       . 7)
                                      . 0)
                                     FST
                                     . 2)
                                    APP
                                    (APP |eq| FST . 0)
                                    FST
                                    . 5)
                                   . 1)
                              . 3)
                         APP
                         (APP (APP |orIR| APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 6) . 5)
                                     PAIR
                                     (FST . 4)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 6)
                                      . 5)
                                     . 4)
                                    . 3)
                                   FST . 1)
                              APP
                              (APP |and| APP |not| APP (APP |dex| . 6)
                                   LAM APP
                                   (APP
                                    |eq|
                                    FST
                                    APP
                                    (APP
                                     (APP (APP |ap2| . 7) . 6)
                                     PAIR
                                     (FST . 5)
                                     APP
                                     (APP
                                      (APP |injFuncSetFuncIn| . 7)
                                      . 6)
                                     . 5)
                                    . 0)
                                   FST . 2)
                              APP (APP |eq| FST . 3) FST . 3)
                         APP
                         (APP (APP (APP
                                    |andI|
                                    APP
                                    |not|
                                    APP
                                    (APP |dex| . 6)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 7) . 6)
                                      PAIR
                                      (FST . 5)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 7)
                                       . 6)
                                      . 5)
                                     . 0)
                                    FST
                                    . 2)
                                   APP (APP |eq| FST . 3) FST . 3)
                              . 0)
                         APP |eqI| FST . 3)
                    LAM LAM APP
                    (APP (APP (APP (APP
                                    (APP
                                     |orE|
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 8) . 7)
                                       PAIR
                                       (FST . 6)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 8)
                                        . 7)
                                       . 6)
                                      . 1)
                                     FST
                                     . 3)
                                    APP
                                    (APP
                                     |and|
                                     APP
                                     |not|
                                     APP
                                     (APP |dex| . 8)
                                     LAM
                                     APP
                                     (APP
                                      |eq|
                                      FST
                                      APP
                                      (APP
                                       (APP (APP |ap2| . 9) . 8)
                                       PAIR
                                       (FST . 7)
                                       APP
                                       (APP
                                        (APP |injFuncSetFuncIn| . 9)
                                        . 8)
                                       . 7)
                                      . 0)
                                     FST
                                     . 4)
                                    APP
                                    (APP |eq| FST . 1)
                                    FST
                                    . 5)
                                   APP
                                   (APP
                                    (APP
                                     (APP
                                      (APP
                                       (APP |dpsetconstrER| . 7)
                                       . 8)
                                      LAM
                                      LAM
                                      APP
                                      (APP
                                       |or|
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 10) . 9)
                                         PAIR
                                         (FST . 8)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 10)
                                          . 9)
                                         . 8)
                                        . 0)
                                       FST
                                       . 1)
                                      APP
                                      (APP
                                       |and|
                                       APP
                                       |not|
                                       APP
                                       (APP |dex| . 10)
                                       LAM
                                       APP
                                       (APP
                                        |eq|
                                        FST
                                        APP
                                        (APP
                                         (APP (APP |ap2| . 11) . 10)
                                         PAIR
                                         (FST . 9)
                                         APP
                                         (APP
                                          (APP |injFuncSetFuncIn| . 11)
                                          . 10)
                                         . 9)
                                        . 0)
                                       FST
                                       . 2)
                                      APP
                                      (APP |eq| FST . 0)
                                      FST
                                      . 7)
                                     FST
                                     . 3)
                                    FST
                                    . 1)
                                   . 0)
                              APP (APP |eq| FST . 1) FST . 5)
                         LAM APP
                         (APP |falseE| APP (APP |eq| FST . 2) FST . 6)
                         APP
                         (APP (APP (APP
                                    |notE|
                                    APP
                                    (APP |dex| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 5)
                                   . |false|)
                              APP
                              (APP (APP
                                    (APP |dexI| . 9)
                                    LAM
                                    APP
                                    (APP
                                     |eq|
                                     FST
                                     APP
                                     (APP
                                      (APP (APP |ap2| . 10) . 9)
                                      PAIR
                                      (FST . 8)
                                      APP
                                      (APP
                                       (APP |injFuncSetFuncIn| . 10)
                                       . 9)
                                      . 8)
                                     . 0)
                                    FST
                                    . 5)
                                   . 2)
                              . 0)
                         . 3)
                    APP
                    (APP |andER| APP |not| APP (APP |dex| . 8) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 9) . 8) PAIR
                                   (FST . 7) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 9)
                                    . 8)
                                   . 7)
                              . 0)
                         FST . 4)
                    APP (APP |eq| FST . 1) FST . 5)
               APP
               (APP (APP (APP |ap2| . 4) . 3) PAIR (FST . 2) APP
                    (APP (APP |injFuncSetFuncIn| . 4) . 3) . 2)
               . 0)
          . 0)
     APP
     (APP (APP (APP (APP (APP |dpsetconstrI| . 3) . 4) LAM LAM APP
                    (APP |or| APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 6) . 5) PAIR
                                   (FST . 4) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 6)
                                    . 5)
                                   . 4)
                              . 0)
                         FST . 1)
                    APP
                    (APP |and| APP |not| APP (APP |dex| . 6) LAM APP
                         (APP |eq| FST APP
                              (APP (APP (APP |ap2| . 7) . 6) PAIR
                                   (FST . 5) APP
                                   (APP
                                    (APP |injFuncSetFuncIn| . 7)
                                    . 6)
                                   . 5)
                              . 0)
                         FST . 2)
                    APP (APP |eq| FST . 0) FST . 3)
               APP
               (APP (APP (APP |ap2| . 4) . 3) PAIR (FST . 2) APP
                    (APP (APP |injFuncSetFuncIn| . 4) . 3) . 2)
               . 0)
          . 0)
     APP
     (APP (APP |orIL| APP
               (APP |eq| FST APP
                    (APP (APP (APP |ap2| . 4) . 3) PAIR (FST . 2) APP
                         (APP (APP |injFuncSetFuncIn| . 4) . 3) . 2)
                    . 0)
               FST APP
               (APP (APP (APP |ap2| . 4) . 3) PAIR (FST . 2) APP
                    (APP (APP |injFuncSetFuncIn| . 4) . 3) . 2)
               . 0)
          APP
          (APP |and| APP |not| APP (APP |dex| . 4) LAM APP
               (APP |eq| FST APP
                    (APP (APP (APP |ap2| . 5) . 4) PAIR (FST . 3) APP
                         (APP (APP |injFuncSetFuncIn| . 5) . 4) . 3)
                    . 0)
               FST APP
               (APP (APP (APP |ap2| . 5) . 4) PAIR (FST . 3) APP
                    (APP (APP |injFuncSetFuncIn| . 5) . 4) . 3)
               . 1)
          APP (APP |eq| FST . 0) FST . 1)
     APP |eqI| FST APP
     (APP (APP (APP |ap2| . 4) . 3) PAIR (FST . 2) APP
          (APP (APP |injFuncSetFuncIn| . 4) . 3) . 2)
     . 0))
