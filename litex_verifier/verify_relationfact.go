package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) RelaFact(stmt *parser.RelaFactStmt) error {
	// TODO:  : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	verifier.roundAddOne()
	defer verifier.roundMinusOne()

	err := verifier.RelaFactSpec(stmt)
	if err != nil {
		return err
	}

	if !verifier.round1() {
		return nil
	}

	return verifier.FuncFactCond(stmt)
}

func (verifier *Verifier) RelaFactSpec(stmt *parser.RelaFactStmt) error {
	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		err := verifier.RelaFactSpecAtEnv(curEnv, stmt)
		if err != nil {
			return err
		}
		if verifier.true() {
			return nil
		}
	}
	return nil
}

func (verifier *Verifier) RelaFactSpecAtEnv(curEnv *env.Env, stmt *parser.RelaFactStmt) error {
	if string(stmt.Opt.OptName) == parser.KeywordEqual {
		return verifier.EqualFactSpecAtEnv(curEnv, stmt)
	}

	panic("not implemented")
}
