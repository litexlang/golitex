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

	// err = verifier.verifyFuncFactUseCondFacts(stmt)
	// if err != nil {
	// 	return err
	// }
	// if verifier.true() {
	// 	return nil
	// }

	verifier.unknown("%s is unknown", stmt.String())
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
				verifier.success("%v is true, verified by %v", stmt.String(), knownFact.String(stmt.Opt))
				return nil
			}
		}
	}
	return nil
}

func (verifier *Verifier) FuncFactCond(stmt parser.SpecFactStmt) error {
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

func (verifier *Verifier) FuncFactCondAtEnv(curEnv *env.Env, stmt parser.SpecFactStmt) error {
	panic("not implemented")
	// key := mem.CondFactMemoryNode{ThenFactAsKey: stmt, CondFacts: nil}
	// // searchNode, err := SearchInEnv(curEnv, &curEnv.ConcreteCondFactMemory.Mem, &key)
	// searchNode, err := curEnv.ConcreteCondFactMemory.Mem.TreeSearch(&key)
	// if err != nil {
	// 	return err
	// }
	// if searchNode == nil {
	// 	return nil
	// }

	// for _, condStmt := range searchNode.Key.CondFacts {
	// 	verified := true
	// 	for _, condFactsInStmt := range condStmt.CondFacts {
	// 		if err := exec.VerifyFactStmt(condFactsInStmt); err != nil {
	// 			return err
	// 		}
	// 		if !exec.true() {
	// 			verified = false
	// 			break
	// 		}
	// 	}
	// 	if verified {
	// 		exec.success("%v is true, verified by %v", stmt, condStmt)
	// 		return nil
	// 	}
	// }

	// return nil
}
