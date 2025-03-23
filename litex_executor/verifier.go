package litexexecutor

import (
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (exec *Executor) verifyFactStmt(stmt parser.FactStmt) error {
	switch stmt := stmt.(type) {
	case *parser.FuncFactStmt:
		return exec.verifyFuncFact(stmt)
	case *parser.RelationFactStmt:
		return exec.verifyRelationFact(stmt)
	case *parser.WhenCondFactStmt:
		return exec.verifyCondFact(stmt)
	default:
		return nil
	}
}

func (exec *Executor) verifyRelationFact(stmt *parser.RelationFactStmt) error {
	// TODO:  : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	return exec.verifyRelationFactLiterally(stmt)
}

func (exec *Executor) verifyFuncFact(stmt *parser.FuncFactStmt) error {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	return exec.verifyFuncFactLiterally(stmt)
}

func (exec *Executor) verifyCondFact(stmt *parser.WhenCondFactStmt) error {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	return exec.verifyCondFactLiterally(stmt)
}

func (exec *Executor) verifyRelationFactLiterally(stmt *parser.RelationFactStmt) error {
	exec.roundAddOne()
	defer exec.roundMinusOne()

	for curEnv := exec.env; curEnv != nil; curEnv = curEnv.Parent {
		err := exec.verifyRelationFactSpecifically(curEnv, stmt)
		if err != nil {
			return err
		}
		if exec.true() {
			return nil
		}
	}

	if !exec.round1() {
		return nil
	}

	return exec.firstRoundVerifySpecFactLiterally(stmt)
}

func (exec *Executor) verifyFuncFactLiterally(stmt *parser.FuncFactStmt) error {
	exec.roundAddOne()
	defer exec.roundMinusOne()

	for curEnv := exec.env; curEnv != nil; curEnv = curEnv.Parent {
		searchedNode, err := exec.useFuncFactMemToVerifyFuncFactAtEnvNodeByNode(stmt)
		if err != nil {
			return err
		}
		if searchedNode != nil {
			exec.success("%v is true, verified by %v", stmt, searchedNode.Key)
			return nil
		}
	}

	if !exec.round1() {
		return nil
	}

	return exec.firstRoundVerifySpecFactLiterally(stmt)
}

func (exec *Executor) firstRoundVerifySpecFactLiterally(stmt parser.SpecFactStmt) error {
	for curEnv := exec.env; curEnv != nil; curEnv = curEnv.Parent {
		err := exec.useCondFactMemToVerifySpecFactAtEnv(curEnv, stmt)
		if err != nil {
			return err
		}
		if exec.true() {
			return nil
		}
	}
	// TODO USE UNI FACT TO PROVE
	return nil
}

func (exec *Executor) useCondFactMemToVerifySpecFactAtEnv(env *memory.Env, stmt parser.SpecFactStmt) error {
	key := memory.CondFactMemoryNode{ThenFactAsKey: stmt, CondFacts: nil}
	searchNode, err := env.CondFactMemory.Mem.SearchInEnv(env, &key)
	if err != nil {
		return err
	}
	if searchNode == nil {
		return nil
	}

	for _, condStmt := range searchNode.Key.CondFacts {
		verified := true
		for _, condFactsInStmt := range condStmt.CondFacts {
			if err := exec.verifyFactStmt(condFactsInStmt); err != nil {
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

func (exec *Executor) useFuncFactMemToVerifyFuncFactAtEnvNodeByNode(key *parser.FuncFactStmt) (*memory.Node[*parser.FuncFactStmt], error) {
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

// func (exec *Executor) useFuncFactMemToVerifyFuncFactAtEnv(env *memory.Env, stmt *parser.FuncFactStmt) error {
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

func (exec *Executor) verifyRelationFactSpecifically(env *memory.Env, stmt *parser.RelationFactStmt) error {
	if string(stmt.Opt.Value) == parser.KeywordEqual {
		return exec.verifyEqualFactSpecifically(env, stmt)
	}

	panic("not implemented")
}

func (exec *Executor) verifyEqualFactSpecifically(env *memory.Env, stmt *parser.RelationFactStmt) error {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: stmt.Params[0], Values: []*parser.Fc{}}

	searchedNode, err := env.EqualMemory.Mem.SearchInEnv(env, &key)

	if err != nil {
		return err
	}

	comp, err := memory.CompareFc(stmt.Params[0], stmt.Params[1])

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
		comp, err := memory.CompareFc(stmt.Params[1], *equalFc)
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

func (exec *Executor) verifyCondFactLiterally(stmt *parser.WhenCondFactStmt) error {
	exec.newEnv()
	defer exec.deleteEnv()

	err := exec.env.NewKnownFact(&parser.KnowStmt{Facts: stmt.CondFacts})
	if err != nil {
		return err
	}

	for _, thenFact := range stmt.ThenFacts {
		err := exec.verifyFactStmt(thenFact)
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
