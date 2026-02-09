package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	litex_env "golitex/environment"
	glob "golitex/glob"
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
	ret := ver.defineParamsInAlgoDef(stmt, def)
	if ret.IsNotTrue() {
		return ret
	}

	// 在每个if 下面检查是不是OK
	panic("")

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
	defLetStmt := ast.NewDefLetStmt(stmt.Params, fnSetObj.ParamSets, []ast.FactStmt{}, glob.BuiltinLine0)
	ret := ver.Env.DefLetStmt(defLetStmt)
	if ret.IsNotTrue() {
		return ast.NewErrVerRet(nil).AddExtraInfo(ret.String())
	}
	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) defineParamsInFnSetObjWithName(stmt *ast.DefAlgoStmt, fnSetObj *ast.FnSetObjWithName) ast.VerRet {
	if len(stmt.Params) != len(fnSetObj.Params) {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("parameter length mismatch: %d != %d", len(stmt.Params), len(fnSetObj.Params)))
	}

	uniMap := make(map[string]ast.Obj)

	for i, param := range stmt.Params {
		uniMap[fnSetObj.Params[i]] = ast.Atom(param)
	}

	paramSets := make([]ast.Obj, len(stmt.Params))
	for i, paramSet := range fnSetObj.ParamSets {
		newParamSet, err := paramSet.Instantiate(uniMap)
		if err != nil {
			return ast.NewErrVerRet(nil).AddExtraInfo(err.Error())
		}
		paramSets[i] = newParamSet
	}

	domFacts := make([]ast.FactStmt, len(fnSetObj.DomFacts))
	for i, domFact := range fnSetObj.DomFacts {
		newDomFact, err := domFact.Instantiate(uniMap)
		if err != nil {
			return ast.NewErrVerRet(nil).AddExtraInfo(err.Error())
		}
		domFacts[i] = newDomFact.(ast.FactStmt)
	}

	defLetStmt := ast.NewDefLetStmt(stmt.Params, paramSets, domFacts, glob.BuiltinLine0)
	ret := ver.Env.DefLetStmt(defLetStmt)
	if ret.IsNotTrue() {
		return ast.NewErrVerRet(nil).AddExtraInfo(ret.String())
	}
	return ast.NewTrueVerRet(nil, nil, "")
}
