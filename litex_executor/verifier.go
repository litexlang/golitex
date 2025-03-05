package litexexecutor

import (
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
	err := exec.useSpecFactToVerifyFuncFact(stmt)
	if err != nil {
		return err
	}
	if exec.True() {
		return nil
	}

	return nil
}

func (exec *Executor) useSpecFactToVerifyFuncFact(stmt *parser.FuncFactStmt) error {
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
		if !exec.True() {
			exec.unknown("%v is unknown", stmt)
			return nil
		}
	}

	return nil
}
