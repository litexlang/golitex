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

	err := exec.useKnownSpecFactsToVerifyFuncFact(stmt)
	if err != nil {
		return err
	}
	if exec.true() {
		return nil
	}

	if exec.round1() {
		err := exec.useKnownCondFactsToVerifyFuncFact(stmt)
		if err != nil {
			return err
		}
		if exec.true() {
			return nil
		}
	}

	return nil
}

func (exec *Executor) useKnownCondFactsToVerifyFuncFact(stmt *parser.FuncFactStmt) error {
	key := memory.CondFactMemoryTreeNode{ThenFact: stmt, CondFacts: nil}
	searchNode, err := exec.env.CondFactMemory.KnownFacts.Search(&key)
	if err != nil {
		return err
	}
	if searchNode != nil {
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
	} else {
		exec.unknown("%v is unknown", stmt)
	}

	return nil
}

func (exec *Executor) useKnownSpecFactsToVerifyFuncFact(stmt *parser.FuncFactStmt) error {
	searchedNode, err := exec.env.SpecFactMemory.KnownFacts.Search(stmt)
	if err != nil {
		return err
	}
	if searchedNode != nil {
		exec.success("%v is true, verified by %v", stmt, searchedNode.Key)
	} else {
		exec.unknown("%v is unknown", stmt)
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
			exec.unknown("%v is unknown", stmt)
			return nil
		}
	}

	return nil
}
