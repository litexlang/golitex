package executor

import (
	"fmt"
	"golitex/parser"
)

func ExecTopLevelStmt(stmt *parser.TopStmt) (*ExecValue, error) {
	return execStmt(&stmt.Stmt)
}

func execStmt(stmt *parser.Stmt) (*ExecValue, error) {
	switch (*stmt).(type) {
	case *parser.DefVarStmt:
		return execDefVarStmt((*stmt).(*parser.DefVarStmt))
	}

	return nil, fmt.Errorf("unknown statement type: %T", stmt)
}

func execDefVarStmt(stmt *parser.DefVarStmt) (*ExecValue, error) {
	// TODO
	return nil, nil
}
