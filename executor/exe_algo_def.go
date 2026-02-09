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

	if len(stmt.Stmts) == 0 {
		return ast.NewErrVerRet(nil).AddExtraInfo("no statements in algo def")
	}

	if asIf := stmt.Stmts[len(stmt.Stmts)-1].(*ast.AlgoIf); asIf != nil {
		// 所有case 的 合并是 真的
		caseByCaseFacts := make([]ast.SpecificFactStmt, len(stmt.Stmts))
		for i := 0; i < len(stmt.Stmts); i++ {
			if asIf := stmt.Stmts[i].(*ast.AlgoIf); asIf != nil {
				caseByCaseFacts[i] = asIf.Condition
			} else {
				return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("expect algo if, got %T", stmt.Stmts[i]))
			}
		}

		orFact := ast.NewOrStmt(caseByCaseFacts, glob.BuiltinLine0)
		verRet := ver.VerFactStmt(orFact, Round0NoMsg())
		if verRet.IsNotTrue() {
			return verRet
		}
	}

	// 在每个if 下面检查是不是OK
	for i := 0; i < len(stmt.Stmts)-1; i++ {
		// 必须是 if
		if _, ok := stmt.Stmts[i].(*ast.AlgoIf); !ok {
			return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("expect algo if, got %T", stmt.Stmts[i]))
		}

		verRet := ver.checkDefAlgoUnderIf(stmt, i)
		if verRet.IsNotTrue() {
			return verRet
		}
	}

	// 最后一个是 return 或 if
	switch stmt.Stmts[len(stmt.Stmts)-1].(type) {
	case *ast.AlgoIf:
		return ver.checkDefAlgoUnderIf(stmt, len(stmt.Stmts)-1)
	case *ast.AlgoReturn:
		return ver.checkDefAlgoUnderReturn(stmt, len(stmt.Stmts)-1)
	default:
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("expect algo if or algo return, got %T", stmt.Stmts[len(stmt.Stmts)-1]))
	}

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

func (ver *Verifier) checkDefAlgoUnderIf(stmt *ast.DefAlgoStmt, i int) ast.VerRet {
	// 假装 这个 if 是对的，然后验证
	algoIf := stmt.Stmts[i].(*ast.AlgoIf)

	ret := ver.storeFactAndCheckFnReq(algoIf.Condition)
	if ret.IsNotTrue() {
		return ret
	}

	// 检查 返回值是不是等于 f(x)
	fnObj := ast.NewFnObj(ast.Atom(stmt.FuncName), stmt.Params.ToObjSlice())

	equalFact := ast.NewEqualFact(algoIf.ReturnStmt.Value, fnObj)
	ret = ver.storeFactAndCheckFnReq(equalFact)
	if ret.IsNotTrue() {
		return ret
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) checkDefAlgoUnderReturn(algoDef *ast.DefAlgoStmt, i int) ast.VerRet {
	// 其他的事实全是错的
	for j := 0; j < len(algoDef.Stmts)-1; j++ {
		if _, ok := algoDef.Stmts[j].(*ast.AlgoIf); !ok {
			return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("expect algo if, got %T", algoDef.Stmts[j]))
		}

		notCase := algoDef.Stmts[j].(*ast.AlgoIf).Condition.ReverseIsTrue()
		for _, notCase := range notCase {
			ret := ver.storeFactAndCheckFnReq(notCase)
			if ret.IsNotTrue() {
				return ret
			}
		}
	}

	// 其他的所有的 if 都是 错的，这时候等于
	algoReturn := algoDef.Stmts[i].(*ast.AlgoReturn)

	fnObj := ast.NewFnObj(ast.Atom(algoDef.FuncName), algoDef.Params.ToObjSlice())
	equalFact := ast.NewEqualFact(algoReturn.Value, fnObj)
	ret := ver.storeFactAndCheckFnReq(equalFact)
	if ret.IsNotTrue() {
		return ret
	}

	return ast.NewTrueVerRet(nil, nil, "")
}
