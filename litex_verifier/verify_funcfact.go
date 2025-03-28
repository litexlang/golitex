package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) FuncFact(stmt *parser.FuncFactStmt) (bool, error) {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	ok, err := verifier.FuncFactSpec(stmt)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if !verifier.round1() {
		return false, nil
	}

	ok, err = verifier.FuncFactCond(stmt)
	if err != nil {
		return false, nil
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (verifier *Verifier) FuncFactSpec(stmt *parser.FuncFactStmt) (bool, error) {
	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		searchedNode, got := curEnv.FuncFactMem.GetNode(stmt)
		if !got {
			continue
		}

		for _, knownFact := range searchedNode.Facts {
			ok, err := verifier.FcSliceEqualSpec(&knownFact.Params, &stmt.Params)

			if err != nil {
				return false, err
			}

			if ok {
				if verifier.round1() {
					verifier.successWithMsg(stmt.String(), knownFact.String(stmt.Opt))
				} else {
					verifier.successNoMsg()
				}
				return true, nil
			}
		}
	}
	return false, nil
}

func (verifier *Verifier) FuncFactCond(stmt *parser.FuncFactStmt) (bool, error) {
	// Use cond fact to verify
	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		ok, err := verifier.FuncFactCondAtEnv(curEnv, stmt)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (verifier *Verifier) FuncFactCondAtEnv(curEnv *env.Env, stmt *parser.FuncFactStmt) (bool, error) {
	searched, got := curEnv.CondFactMem.GetFuncFactNode(stmt)
	if !got {
		return false, nil
	}

LoopOverFacts:
	for _, knownFact := range searched.Facts {
		for _, f := range knownFact.Fact.CondFacts {
			ok, err := verifier.FactStmt(f)
			if err != nil {
				return false, err
			}
			if !ok {
				continue LoopOverFacts
			}
		}

		verified, err := verifier.FcSliceEqualSpec(&knownFact.Params, &stmt.Params)

		if err != nil {
			return false, err
		}

		if verified {
			if verifier.round1() {
				verifier.successWithMsg(stmt.String(), knownFact.Fact.String())
			} else {
				verifier.successNoMsg()
			}
			return true, nil
		}
	}

	return false, nil
}
