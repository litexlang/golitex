package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	litex_env "golitex/environment"
)

func (exec *Executor) defAlgoStmt(stmt *ast.DefAlgoStmt) ast.StmtRet {
	verRet := exec.checkDefAlgoStmt(stmt)
	if verRet.IsNotTrue() {
		return verRet.ToStmtRet()
	}

	exec.Env.CurEnv().AlgoDefMem[stmt.FuncName] = struct{}{}
	exec.Env.AllDefinedAlgoNames[stmt.FuncName] = litex_env.NewDefinedStuff(stmt, exec.Env.CurEnvDepth())
	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) checkDefAlgoStmt(stmt *ast.DefAlgoStmt) ast.VerRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	ver := NewVerifier(exec.Env)

	// 找到相关函数
	def := ver.Env.GetFnInFnSet(stmt.FuncName)
	if def == nil {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("function %s is not defined", stmt.FuncName))
	}

	// 按def里的param的定义来定义param

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) defineParamsInAlgoDef(stmt *ast.DefAlgoStmt, fnSetObj ast.FnSetObj) ast.VerRet {
	switch f := fnSetObj.(type) {
	case *ast.FnSetObjWithoutName:
		return ver.defineParamsInFnSetObjWithoutName(stmt, f)
	case *ast.FnSetObjWithName:
		return ver.defineParamsInFnSetObjWithName(stmt, f)
	default:
		panic(fmt.Sprintf("unknown fn set obj type: %T", fnSetObj))
	}
}

func (ver *Verifier) defineParamsInFnSetObjWithoutName(stmt *ast.DefAlgoStmt, fnSetObj *ast.FnSetObjWithoutName) ast.VerRet {
	// defLetStmt := ast.NewDefLetStmt(stmt.Params, fnSetObj.ParamSets, fnSetObj.DomFacts.ToFactStmtSlice(), glob.BuiltinLine0)
	panic("")
}

func (ver *Verifier) defineParamsInFnSetObjWithName(stmt *ast.DefAlgoStmt, fnSetObj *ast.FnSetObjWithName) ast.VerRet {
	panic("	")
}
