package litexexecutor

import (
	parser "golitex/litex_parser"
)

func (exec *Executor) verifyFactStmt(stmt parser.FactStmt) error {
	switch stmt := stmt.(type) {
	case *parser.FuncFactStmt:
		return exec.verifyFuncFact(stmt)
	default:
		return nil
	}
}

func (exec *Executor) verifyFuncFact(stmt *parser.FuncFactStmt) error {
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
