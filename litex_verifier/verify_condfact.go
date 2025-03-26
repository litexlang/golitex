package litexverifier

import parser "golitex/litex_parser"

func (verifier *Verifier) verifyCondFact(stmt *parser.ConditionalFactStmt) error {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	return verifier.verifyCondFactLiterally(stmt)
}

func (verifier *Verifier) verifyCondFactLiterally(stmt *parser.ConditionalFactStmt) error {
	verifier.newEnv()
	defer verifier.deleteEnv()

	err := verifier.env.NewKnownFact(&parser.KnowStmt{Facts: stmt.CondFacts})
	if err != nil {
		return err
	}

	for _, thenFact := range stmt.ThenFacts {
		err := verifier.VerifyFactStmt(thenFact)
		if err != nil {
			return err
		}
		if !verifier.true() {
			return nil
		} else {
			verifier.unknown("%v is unknown: %v is unknown", stmt, thenFact)
		}
	}

	verifier.success("%v is true", stmt)

	return nil
}
