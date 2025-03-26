package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) verifyRelationFact(stmt *parser.RelationFactStmt) error {
	// TODO:  : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	verifier.roundAddOne()
	defer verifier.roundMinusOne()

	err := verifier.verifyRelationFactSpecifically(stmt)
	if err != nil {
		return err
	}

	if !verifier.round1() {
		return nil
	}

	return verifier.verifyFuncFactUseCondFacts(stmt)
}

func (verifier *Verifier) verifyRelationFactSpecifically(stmt *parser.RelationFactStmt) error {
	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		err := verifier.verifyRelationFactSpecificallyAtEnv(curEnv, stmt)
		if err != nil {
			return err
		}
		if verifier.true() {
			return nil
		}
	}
	return nil
}

func (exec *Verifier) verifyRelationFactSpecificallyAtEnv(curEnv *env.Env, stmt *parser.RelationFactStmt) error {
	if string(stmt.Opt.Value) == parser.KeywordEqual {
		return exec.verifyEqualFactSpecificallyAtEnv(curEnv, stmt)
	}

	panic("not implemented")
}
