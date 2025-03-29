package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (ver *Verifier) FuncFact(stmt *parser.FuncFactStmt) (bool, error) {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	ok, err := ver.FuncFactSpec(stmt)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if !ver.round1() {
		return false, nil
	}

	ok, err = ver.FuncFactCond(stmt)
	if err != nil {
		return false, nil
	}
	if ok {
		return true, nil
	}

	ver.unknownNoMsg()
	return false, nil
}

func (ver *Verifier) FuncFactSpec(stmt *parser.FuncFactStmt) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		if stmt.Opt.PkgName == "" && stmt.Opt.OptName == parser.KeywordEqual {
			return ver.EqualFactSpecAtEnv(curEnv, stmt)
		}

		searchedNode, got := curEnv.FuncFactMem.GetNode(stmt)
		if !got {
			continue
		}

		for _, knownFact := range searchedNode.Facts {
			if stmt.IsTrue != knownFact.IsTrue {
				continue
			}

			ok, err := ver.FcSliceEqual(&knownFact.Params, &stmt.Params, false)

			if err != nil {
				return false, err
			}

			if ok {
				if ver.round1() {
					ver.successWithMsg("", knownFact.String(stmt.Opt))
				} else {
					ver.successNoMsg()
				}
				return true, nil
			}
		}
	}
	return false, nil
}

func (ver *Verifier) FuncFactCond(stmt *parser.FuncFactStmt) (bool, error) {
	// Use cond fact to verify
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		ok, err := ver.FuncFactCondAtEnv(curEnv, stmt)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) FuncFactCondAtEnv(curEnv *env.Env, stmt *parser.FuncFactStmt) (bool, error) {
	searched, got := curEnv.CondFactMem.GetFuncFactNode(stmt)
	if !got {
		return false, nil
	}

LoopOverFacts:
	for _, knownFact := range searched.Facts {
		for _, f := range knownFact.Fact.CondFacts {
			ok, err := ver.FactStmt(f)
			if err != nil {
				return false, err
			}
			if !ok {
				continue LoopOverFacts
			}
		}

		verified, err := ver.FcSliceEqual(&knownFact.Params, &stmt.Params, false)

		if err != nil {
			return false, err
		}

		if verified {
			if ver.round1() {
				ver.successWithMsg(stmt.String(), knownFact.Fact.String())
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}
	}

	return false, nil
}
