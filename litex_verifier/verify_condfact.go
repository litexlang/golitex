package litexverifier

import parser "golitex/litex_parser"

func (verifier *Verifier) CondFact(stmt *parser.CondFactStmt) (bool, error) {
	ok, err := verifier.CondFactSpec(stmt)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if !verifier.round1() {
		return false, nil
	}

	return verifier.CondFactCond(stmt)

	// TODO: CondFactUni
}

func (verifier *Verifier) CondFactSpec(stmt *parser.CondFactStmt) (bool, error) {
	verifier.newEnv()
	defer verifier.deleteEnv()

	for _, condFact := range stmt.CondFacts {
		err := verifier.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		ok, err := verifier.FactStmt(thenFact)
		if err != nil {
			return false, err
		}
		if !ok {
			if verifier.round1() {
				verifier.unknownWithMsg("%v is unknown: %v is unknown", stmt, thenFact)
				return false, nil
			} else {
				verifier.unknownNoMsg()
				return false, nil
			}
		}
	}

	if verifier.round1() {
		verifier.successWithMsg("%v is true", stmt.String())
		return true, nil
	} else {
		verifier.successNoMsg()
		return true, nil
	}
}

func (verifier *Verifier) CondFactCond(stmt *parser.CondFactStmt) (bool, error) {
	// TODO
	return false, nil
}
