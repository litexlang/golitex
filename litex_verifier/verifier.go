package litexverifier

import (
	cmp "golitex/litex_comparator"
	ds "golitex/litex_data_structure"
	env "golitex/litex_env"
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) VerifyFactStmt(stmt parser.FactStmt) error {
	switch stmt := stmt.(type) {
	case *parser.FuncFactStmt:
		return verifier.verifyFuncFact(stmt)
	case *parser.RelationFactStmt:
		return verifier.verifyRelationFact(stmt)
	case *parser.ConditionalFactStmt:
		return verifier.verifyCondFact(stmt)
	default:
		return nil
	}
}

func (verifier *Verifier) verifyRelationFact(stmt *parser.RelationFactStmt) error {
	// TODO:  : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	return verifier.verifyRelationFactLiterally(stmt)
}

func (verifier *Verifier) verifyFuncFact(stmt *parser.FuncFactStmt) error {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	return verifier.verifyFuncFactLiterally(stmt)
}

func (verifier *Verifier) verifyCondFact(stmt *parser.ConditionalFactStmt) error {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	return verifier.verifyCondFactLiterally(stmt)
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

func (verifier *Verifier) verifyFuncFactLiterally(stmt *parser.FuncFactStmt) error {
	verifier.roundAddOne()
	defer verifier.roundMinusOne()

	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		searchedNode, err := verifier.useFuncFactMemToVerifyFuncFactAtEnvNodeByNode(stmt)
		if err != nil {
			return err
		}
		if searchedNode != nil {
			verifier.success("%v is true, verified by %v", stmt, searchedNode.Key)
			return nil
		}
	}

	if !verifier.round1() {
		return nil
	}

	return verifier.firstRoundVerifySpecFactLiterally(stmt)
}

func (verifier *Verifier) firstRoundVerifySpecFactLiterally(stmt parser.SpecFactStmt) error {
	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		err := verifier.useCondFactMemToVerifySpecFactAtEnv(curEnv, stmt)
		if err != nil {
			return err
		}
		if verifier.true() {
			return nil
		}
	}
	// TODO USE UNI FACT TO PROVE
	return nil
}

func (exec *Verifier) useCondFactMemToVerifySpecFactAtEnv(curEnv *env.Env, stmt parser.SpecFactStmt) error {
	key := memory.CondFactMemoryNode{ThenFactAsKey: stmt, CondFacts: nil}
	searchNode, err := SearchInEnv(curEnv, &curEnv.CondFactMemory.Mem, &key)
	if err != nil {
		return err
	}
	if searchNode == nil {
		return nil
	}

	for _, condStmt := range searchNode.Key.CondFacts {
		verified := true
		for _, condFactsInStmt := range condStmt.CondFacts {
			if err := exec.VerifyFactStmt(condFactsInStmt); err != nil {
				return err
			}
			if !exec.true() {
				verified = false
				break
			}
		}
		if verified {
			exec.success("%v is true, verified by %v", stmt, condStmt)
			return nil
		}
	}

	return nil
}

func (exec *Verifier) useFuncFactMemToVerifyFuncFactAtEnvNodeByNode(key *parser.FuncFactStmt) (*ds.Node[*parser.FuncFactStmt], error) {
	curNode := exec.env.FuncFactMemory.Mem.Root
	err := error(nil)
	searched := false
	for curNode != nil {
		// * 这里需要遍历当前的curNode的所有的参数，把参数替换成和该参数相等的参数，然后看下是否有相关的事实
		// * 类似数据库把有特定pattern的事实先全部搜到，然后遍历一遍些事实看看哪些能匹配上

		curNode, err, searched = exec.env.FuncFactMemory.Mem.SearchOneLayer(curNode, key)
		if err != nil {
			return nil, err
		}

		if searched {
			return curNode, nil
		}
	}

	return nil, nil
}

// func (exec *Verifier) useFuncFactMemToVerifyFuncFactAtEnv(env *Env, stmt *parser.FuncFactStmt) error {
// 	// searchedNode, err := env.FuncFactMemory.Mem.SearchInEnv(env, stmt)
// 	searchedNode, err := env.FuncFactMemory.Mem.SearchInEnv(env, stmt)
// 	if err != nil {
// 		return err
// 	}
// 	if searchedNode != nil {
// 		exec.success("%v is true, verified by %v", stmt, searchedNode.Key)
// 		return nil
// 	}

// 	return nil
// }

func (exec *Verifier) verifyRelationFactSpecifically(curEnv *env.Env, stmt *parser.RelationFactStmt) error {
	if string(stmt.Opt.Value) == parser.KeywordEqual {
		return exec.verifyEqualFactSpecifically(curEnv, stmt)
	}

	panic("not implemented")
}

func (exec *Verifier) verifyEqualFactSpecifically(curEnv *env.Env, stmt *parser.RelationFactStmt) error {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: stmt.Params[0], Values: []*parser.Fc{}}

	searchedNode, err := SearchInEnv(curEnv, &curEnv.EqualMemory.Mem, &key)

	if err != nil {
		return err
	}

	comp, err := cmp.CmpFc(stmt.Params[0], stmt.Params[1])

	if err != nil {
		return err
	}
	if comp == 0 {
		exec.success("%v is true, verified by %v", stmt, searchedNode.Key)
		return nil
	}

	if searchedNode == nil {
		return nil
	}

	for _, equalFc := range searchedNode.Key.Values {
		comp, err := cmp.CmpFc(stmt.Params[1], *equalFc)
		if err != nil {
			return err
		}
		if comp == 0 {
			exec.success("%v is true, verified by %v", stmt, equalFc)
			return nil
		}
	}

	return nil
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
