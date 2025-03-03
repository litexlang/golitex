package litexexecutor

import (
	"fmt"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func ExecTopLevelStmt(env *mem.Env, stmt *parser.TopStmt) (*ExecValue, error) {
	return execStmt(env, &stmt.Stmt)
}

func execStmt(env *mem.Env, stmt *parser.Stmt) (*ExecValue, error) {
	switch stmt := (*stmt).(type) {
	case *parser.KnowStmt:
		return execKnowStmt(env, stmt)

	default:
		return nil, fmt.Errorf("unknown statement type: %T", stmt)
	}
}

func execKnowStmt(env *mem.Env, stmt *parser.KnowStmt) (*ExecValue, error) {
	// TODO verify whether stmt is valid, for example all symbols are declared.
	if err := env.NewKnownFact(stmt); err != nil {
		return &ExecValue{ExecError, ""}, nil
	}

	return &ExecValue{ExecTrue, ""}, nil
}

func execDefVarStmt(env *mem.Env, stmt *parser.DefVarStmt) (*ExecValue, error) {
	err := env.NewVar(&stmt.Decl.VarTypePair)
	if err != nil {
		return nil, err
	}
	return &ExecValue{ExecTrue, ""}, nil
}
