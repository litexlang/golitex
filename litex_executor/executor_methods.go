package litexexecutor

import (
	"fmt"
	parser "golitex/litex_parser"
)

func (exec *Executor) TopLevelStmt(stmt *parser.TopStmt) error {
	return exec.stmt(&stmt.Stmt)
}

func (exec *Executor) stmt(stmt *parser.Stmt) error {
	switch stmt := (*stmt).(type) {
	case *parser.KnowStmt:
		return exec.knowStmt(stmt)

	default:
		return fmt.Errorf("unknown statement type: %T", stmt)
	}
}

func (exec *Executor) knowStmt(stmt *parser.KnowStmt) error {
	// TODO verify whether stmt is valid, for example all symbols are declared.
	if err := exec.env.NewKnownFact(stmt); err != nil {
		return err
	}
	// TODO
	exec.success(fmt.Sprintf(""))
	return nil
}

func (exec *Executor) defVarStmt(stmt *parser.DefVarStmt) error {
	err := exec.env.NewVar(&stmt.Decl.VarTypePair)
	if err != nil {
		return err
	}

	return nil
}
