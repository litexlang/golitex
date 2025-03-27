package litexverifier

import parser "golitex/litex_parser"

func (verifier *Verifier) CondFact(stmt *parser.CondFactStmt) error {
	verifier.roundAddOne()
	defer verifier.roundMinusOne()

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
			verifier.unknown("%v is unknown: %v is unknown", stmt, thenFact)
			return nil
		}
	}

	verifier.success("%v is true", stmt.String())

	return nil
}

func (verifier *Verifier) CondFactCond(stmt *parser.CondFactStmt) error {
	// TODO
	return nil
}
