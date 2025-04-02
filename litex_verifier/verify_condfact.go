package litexverifier

import parser "golitex/litex_parser"

func (ver *Verifier) CondFact(stmt *parser.CondFactStmt, state VerState) (bool, error) {
	ok, err := ver.CondFactSpec(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if !ver.round1() {
		return false, nil
	}

	// TODO

	return ver.CondFactCond(stmt, state)

	// TODO: CondFactUni
}

func (ver *Verifier) CondFactSpec(stmt *parser.CondFactStmt, state VerState) (bool, error) {
	ver.newEnv(nil, nil)
	defer ver.parentEnv() // 万一cond里有condFact，那要保证能回到原来的环境

	for _, condFact := range stmt.CondFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		ok, err := ver.FactStmt(&thenFact, state.spec())
		if err != nil {
			return false, err
		}
		if !ok {
			if ver.round1() {
				ver.unknownWithMsg("%v is unknown: %v is unknown", stmt, thenFact)
				return false, nil
			} else {
				// ver.unknownNoMsg()
				return false, nil
			}
		}
	}

	if ver.round1() {
		ver.successWithMsg("%v is true", stmt.String())
		return true, nil
	} else {
		ver.successNoMsg()
		return true, nil
	}
}

func (ver *Verifier) CondFactCond(stmt *parser.CondFactStmt, state VerState) (bool, error) {
	// TODO
	return false, nil
}
