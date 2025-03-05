package litexexecutor

import (
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (exec *Executor) verifyFactStmt(stmt parser.FactStmt) error {
	switch stmt := stmt.(type) {
	case *parser.FuncFactStmt:
		return exec.verifyFuncFact(stmt)
	case *parser.IfFactStmt:
		return exec.verifyCondFact(stmt)
	default:
		return nil
	}
}

func (exec *Executor) verifyFuncFact(stmt *parser.FuncFactStmt) error {
	exec.searchRound++
	defer exec.roundMinusOne()

	for curEnv := exec.env; curEnv != nil; curEnv = curEnv.Parent {
		err := exec.useSpecFactMemToVerifyFuncFactAtEnv(curEnv, stmt)
		if err != nil {
			return err
		}
		if exec.true() {
			return nil
		}
	}

	if !exec.round1() {
		exec.unknown("%v is unknown", stmt)
		return nil
	}

	for curEnv := exec.env; curEnv != nil; curEnv = curEnv.Parent {
		err := exec.useCondFactMemToVerifyFuncFactAtEnv(curEnv, stmt)
		if err != nil {
			return err
		}
		if exec.true() {
			return nil
		}
	}

	exec.unknown("%v is unknown", stmt)
	return nil
}

func (exec *Executor) useCondFactMemToVerifyFuncFactAtEnv(env *memory.Env, stmt *parser.FuncFactStmt) error {
	key := memory.CondFactMemoryTreeNode{ThenFact: stmt, CondFacts: nil}
	searchNode, err := env.CondFactMemory.KnownFacts.Search(&key)
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

func (exec *Executor) useSpecFactMemToVerifyFuncFactAtEnv(env *memory.Env, stmt *parser.FuncFactStmt) error {
	searchedNode, err := env.SpecFactMemory.KnownFacts.Search(stmt)
	if err != nil {
		return err
	}
	if searchedNode != nil {
		exec.success("%v is true, verified by %v", stmt, searchedNode.Key)
		return nil
	}

	return nil
}

func (exec *Executor) verifyCondFact(stmt *parser.IfFactStmt) error {
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
