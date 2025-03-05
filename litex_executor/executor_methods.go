package litexexecutor

import (
	"fmt"
	parser "golitex/litex_parser"
)

func (exec *Executor) TopLevelStmt(stmt *parser.TopStmt) error {
	exec.clear()
	return exec.stmt(stmt.Stmt)
}

func (exec *Executor) stmt(stmt parser.Stmt) error {
	switch stmt := (stmt).(type) {
	case parser.FactStmt:
		return exec.verifyFactStmt(stmt)
	case *parser.KnowStmt:
		return exec.knowStmt(stmt)
	case *parser.DefVarStmt:
		return exec.defVarStmt(stmt)

	default:
		return fmt.Errorf("unknown statement type: %T", stmt)
	}
}

func (exec *Executor) knowStmt(stmt *parser.KnowStmt) error {
	if err := exec.env.NewKnownFact(stmt); err != nil {
		return err
	}
	exec.success("%v", stmt)
	return nil
}

func (exec *Executor) defVarStmt(stmt *parser.DefVarStmt) error {
	err := exec.env.NewVar(&stmt.Decl.VarTypePair)
	if err != nil {
		return err
	}

	return nil
}
