package litexexecutor

import (
	"fmt"
	env "golitex/litexenv"
	parser "golitex/litexparser"
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
	for _, pair := range stmt.Decl.VarTypePairs {
		err := env.NewVar(&pair)
		if err != nil {
			return nil, err
		}
	}
	return nil, nil
}
