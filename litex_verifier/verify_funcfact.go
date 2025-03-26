package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) verifyFuncFact(stmt *parser.FuncFactStmt) error {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally
	verifier.roundAddOne()
	defer verifier.roundMinusOne()

	err := verifier.verifyFuncFactLiterally(stmt)
	if err != nil {
		return err
	}
	if verifier.true() {
		return nil
	}

	if !verifier.round1() {
		return nil
	}

	err = verifier.verifyFuncFactUseCondFacts(stmt)
	if err != nil {
		return err
	}
	if verifier.true() {
		return nil
	}

	return nil
}

func (verifier *Verifier) verifyFuncFactLiterally(stmt *parser.FuncFactStmt) error {
	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		searchedNode, got := curEnv.ConcreteFuncFactMemory.GetNode(stmt)
		if !got {
			continue
		}

		for _, knownFact := range searchedNode.Facts {
			verified, err := verifier.twoParamSliceHaveEqualParams(&knownFact.Params, &stmt.Params)

			if err != nil {
				return err
			}

			if verified {
				verifier.success("%v is true, verified by %v", stmt, knownFact)
				return nil
			}
		}
	}

	// for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
	// 	searchedNode, err := verifier.useFuncFactMemToVerifyFuncFactAtEnvNodeByNode(stmt)
	// 	// ! 25-3-26 这里要用更好的search方式来搜索已知的信息
	// 	searchedNode, err := curEnv.ConcreteFuncFactMemory.Mem.TreeSearch(stmt)
	// 	if err != nil {
	// 		return err
	// 	}
	// 	if searchedNode != nil {
	// 		verifier.success("%v is true, verified by %v", stmt, searchedNode.Key)
	// 		return nil
	// 	}
	// }

	return nil
}

func (verifier *Verifier) verifyFuncFactUseCondFacts(stmt parser.SpecFactStmt) error {
	// Use cond fact to verify
	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		err := verifier.verifyFuncFactUseCondFactsAtGivenEnv(curEnv, stmt)
		if err != nil {
			return err
		}
		if verifier.true() {
			return nil
		}
	}
	return nil
}

func (exec *Verifier) verifyFuncFactUseCondFactsAtGivenEnv(curEnv *env.Env, stmt parser.SpecFactStmt) error {
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
