package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) proveIsCommutativePropStmt(stmt *ast.ProveIsCommutativePropStmt) (glob.ExecState, error) {
	ok, err := exec.proveIsCommutativePropStmtMainLogic(stmt)
	if err != nil {
		return glob.ExecStateError, err
	}
	if ok {
		return glob.ExecStateTrue, nil
	}
	return glob.ExecStateUnknown, nil
}

func (exec *Executor) proveIsCommutativePropStmtMainLogic(stmt *ast.ProveIsCommutativePropStmt) (bool, error) {
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndRetainMsg()

	panic("not implemented")
}
