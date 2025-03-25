package litexverifier

import parser "golitex/litex_parser"

func (verifier *Verifier) verifyCondFact(stmt *parser.ConditionalFactStmt) error {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	return verifier.verifyCondFactLiterally(stmt)
}

func (exec *Verifier) verifyCondFactLiterally(stmt *parser.ConditionalFactStmt) error {
	exec.newEnv()
	defer exec.deleteEnv()

	err := exec.env.NewKnownFact(&parser.KnowStmt{Facts: stmt.CondFacts})
	if err != nil {
		return err
	}

	for _, thenFact := range stmt.ThenFacts {
		err := exec.VerifyFactStmt(thenFact)
		if err != nil {
			return err
		}
		if !exec.true() {
			return nil
		} else {
			exec.unknown("%v is unknown: %v is unknown", stmt, thenFact)
		}
	}

	exec.success("%v is true", stmt)

	return nil
}
