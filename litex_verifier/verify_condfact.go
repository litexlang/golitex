package litexverifier

import parser "golitex/litex_parser"

func (ver *Verifier) CondFact(stmt *parser.CondFactStmt) (bool, error) {
	ok, err := ver.CondFactSpec(stmt)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if !ver.round1() {
		return false, nil
	}

	return ver.CondFactCond(stmt)

	// TODO: CondFactUni
}

func (ver *Verifier) CondFactSpec(stmt *parser.CondFactStmt) (bool, error) {
	ver.newEnv(nil, nil)
	defer ver.deleteEnv()

	for _, condFact := range stmt.CondFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		ok, err := ver.FactStmt(&thenFact)
		if err != nil {
			return false, err
		}
		if !ok {
			if ver.round1() {
				ver.unknownWithMsg("%v is unknown: %v is unknown", stmt, thenFact)
				return false, nil
			} else {
				ver.unknownNoMsg()
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

func (ver *Verifier) CondFactCond(stmt *parser.CondFactStmt) (bool, error) {
	// TODO
	return false, nil
}
