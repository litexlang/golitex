package litex_executor

import (
	ast "golitex/ast"
	cmp "golitex/cmp"
)

func (ver *Verifier) simplifyObj(obj ast.Obj) (bool, ast.Obj) {
	if simplified := cmp.IsNumExprObjThenSimplify(obj); simplified != nil {
		return true, simplified
	}

	if objAsFn, ok := obj.(*ast.FnObj); ok {
		headIsSimplified, headSimplifiedObj := ver.simplifyObj(objAsFn.FnHead)
		if !headIsSimplified {
			return false, nil
		}

		paramsAreSimplified := false
		paramsSimplifiedObjs := make([]ast.Obj, len(objAsFn.Params))
		for i, param := range objAsFn.Params {
			paramsSimplified, paramsSimplifiedObj := ver.simplifyObj(param)
			paramsSimplifiedObjs[i] = paramsSimplifiedObj
			paramsAreSimplified = paramsAreSimplified || paramsSimplified
		}

		if headIsSimplified || paramsAreSimplified {
			return true, ast.NewFnObj(headSimplifiedObj, paramsSimplifiedObjs)
		}

		return false, nil
	}

	return false, obj
}

func (ver *Verifier) simplifyPureSpecFactObjs(stmt *ast.PureSpecificFactStmt) (bool, *ast.PureSpecificFactStmt) {
	simplifiedParams := make([]ast.Obj, len(stmt.Params))
	simplified := false
	for i, param := range stmt.Params {
		paramIsSimplified, simplifiedParam := ver.simplifyObj(param)
		simplifiedParams[i] = simplifiedParam
		simplified = simplified || paramIsSimplified
	}
	return simplified, ast.NewPureSpecificFactStmt(stmt.IsTrue, stmt.PropName, simplifiedParams, stmt.Line)
}
