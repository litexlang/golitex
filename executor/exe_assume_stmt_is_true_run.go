package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) assumeStmtIsTrueRun(stmt ast.Stmt) (glob.ExecState, error) {
	var err error = nil
	var execState glob.ExecState = glob.ExecState_True

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		knowFact := ast.NewKnowStmt([]ast.FactStmt{stmt})
		err = exec.knowStmt(knowFact)
	case *ast.KnowFactStmt:
		err = exec.knowStmt(stmt)
	case *ast.ClaimProveStmt:
		panic("implement me")
	case *ast.DefPropStmt:
		err = exec.defPropStmt(stmt)
	case *ast.DefObjStmt:
		err = exec.defObjStmt(stmt, true)
	case *ast.HaveStmt:
		panic("implement me")
	case *ast.DefExistPropStmt:
		err = exec.defExistPropStmt(stmt)
	case *ast.DefFnStmt:
		err = exec.defFnStmt(stmt)
	case *ast.KnowPropStmt:
		err = exec.knowPropStmt(stmt)
	case *ast.KnowExistPropStmt:
		_, err = exec.knowExistPropStmt(stmt)
	case *ast.ProveInEachCaseStmt:
		panic("implement me")
	case *ast.SupposeStmt:
		panic("implement me")
	case *ast.WithStmt:
		panic("implement me")
	case *ast.ImportStmt:
		panic("implement me")
	case *ast.PubStmt:
		panic("implement me")
	case *ast.ProveStmt:
		panic("implement me")
	case *ast.ClaimProveByContradictionStmt:
		panic("implement me")
	case *ast.DefFnTemplateStmt:
		err = exec.defFnTemplateStmt(stmt)
	default:
		err = fmt.Errorf("unknown statement type: %T", stmt)
	}

	return execState, err
}
