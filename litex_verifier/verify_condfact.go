package litexverifier

import parser "golitex/litex_parser"

func (verifier *Verifier) CondFact(stmt *parser.CondFactStmt) error {
	err := verifier.CondFactSpec(stmt)
	if err != nil {
		return err
	}
	if verifier.true() {
		return nil
	}

	if !verifier.round1() {
		return nil
	}

	return verifier.CondFactCond(stmt)

	// TODO: CondFactUni
}

func (verifier *Verifier) CondFactSpec(stmt *parser.CondFactStmt) error {
	verifier.newEnv()
	defer verifier.deleteEnv()

	for _, condFact := range stmt.CondFacts {
		err := verifier.env.NewFact(condFact)
		if err != nil {
			return err
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		err := verifier.FactStmt(thenFact)
		if err != nil {
			return err
		}
		if !verifier.true() {
			if verifier.round1() {
				verifier.unknownWithMsg("%v is unknown: %v is unknown", stmt, thenFact)
				return nil
			} else {
				verifier.unknownNoMsg()
				return nil
			}
		}
	}

	if verifier.round1() {
		verifier.successWithMsg("%v is true", stmt.String())
	} else {
		verifier.successNoMsg()
	}

	return nil
}

func (verifier *Verifier) CondFactCond(stmt *parser.CondFactStmt) error {
	// TODO
	return nil
}
