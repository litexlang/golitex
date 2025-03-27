package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) FuncFact(stmt *parser.FuncFactStmt) error {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally
	verifier.roundAddOne()
	defer verifier.roundMinusOne()

	err := verifier.FuncFactSpec(stmt)
	if err != nil {
		return err
	}
	if verifier.true() {
		return nil
	}

	if !verifier.round1() {
		return nil
	}

	err = verifier.FuncFactCond(stmt)
	if err != nil {
		return err
	}
	if verifier.true() {
		return nil
	}

	return nil
}

func (verifier *Verifier) FuncFactSpec(stmt *parser.FuncFactStmt) error {
	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		searchedNode, got := curEnv.FuncFactMem.GetNode(stmt)
		if !got {
			continue
		}

		for _, knownFact := range searchedNode.Facts {
			verified, err := verifier.FcSliceEqualSpec(&knownFact.Params, &stmt.Params)

			if err != nil {
				return err
			}

			if verified {
				verifier.success(stmt.String(), knownFact.String(stmt.Opt))
				return nil
			}
		}
	}
	return nil
}

func (verifier *Verifier) FuncFactCond(stmt *parser.FuncFactStmt) error {
	// Use cond fact to verify
	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		err := verifier.FuncFactCondAtEnv(curEnv, stmt)
		if err != nil {
			return err
		}
		if verifier.true() {
			return nil
		}
	}
	return nil
}

func (verifier *Verifier) FuncFactCondAtEnv(curEnv *env.Env, stmt *parser.FuncFactStmt) error {
	searched, got := curEnv.CondFactMem.GetFuncFactNode(stmt)
	if !got {
		return nil
	}

	for _, knownFact := range searched.Facts {
		verified, err := verifier.FcSliceEqualSpec(&knownFact.Params, &stmt.Params)

		if err != nil {
			return err
		}

		if verified {
			verifier.success(stmt.String(), knownFact.String(stmt.Opt))
			return nil
		}
	}

	return nil
}
