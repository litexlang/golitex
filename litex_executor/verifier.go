package litexexecutor

import (
	parser "golitex/litex_parser"
)

func (exec *Executor) verifyFuncFact(stmt *parser.FuncFactStmt) error {
	searchedNode, err := exec.env.SpecFactMemory.KnownFacts.Search(stmt)
	if err != nil {
		return err
	}
	if searchedNode != nil {
		exec.success("%v is true, verified by %v", stmt, searchedNode)
	} else {
		exec.unknown("%v is unknown", stmt)
	}

	return nil
}
