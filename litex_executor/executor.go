package litexexecutor

import (
	"fmt"
	parser "golitex/litex_parser"
	env "golitex/litex_runtime_environment"
)

func ExecTopLevelStmt(env *env.Env, stmt *parser.TopStmt) (*ExecValue, error) {
	return execStmt(env, &stmt.Stmt)
}

func execStmt(env *env.Env, stmt *parser.Stmt) (*ExecValue, error) {
	switch (*stmt).(type) {
	case *parser.DefVarStmt:
		return execDefVarStmt(env, (*stmt).(*parser.DefVarStmt))
	}

	return nil, fmt.Errorf("unknown statement type: %T", stmt)
}

func execDefVarStmt(env *env.Env, stmt *parser.DefVarStmt) (*ExecValue, error) {
	err := env.NewVar(&stmt.Decl.VarTypePair)
	if err != nil {
		return nil, err
	}
	return &ExecValue{ExecTrue, ""}, nil
}
