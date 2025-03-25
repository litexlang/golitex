package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) verifyRelationFact(stmt *parser.RelationFactStmt) error {
	// TODO:  : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	return verifier.verifyRelationFactLiterally(stmt)
}

func (verifier *Verifier) verifyRelationFactLiterally(stmt *parser.RelationFactStmt) error {
	verifier.roundAddOne()
	defer verifier.roundMinusOne()

	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		err := verifier.verifyRelationFactSpecifically(curEnv, stmt)
		if err != nil {
			return err
		}
		if verifier.true() {
			return nil
		}
	}

	if !verifier.round1() {
		return nil
	}

	return verifier.firstRoundVerifySpecFactLiterally(stmt)
}

func (exec *Verifier) verifyRelationFactSpecifically(curEnv *env.Env, stmt *parser.RelationFactStmt) error {
	if string(stmt.Opt.Value) == parser.KeywordEqual {
		return exec.verifyEqualFactSpecifically(curEnv, stmt)
	}

	panic("not implemented")
}
