package litex_executor

import (
	"fmt"
	ast "golitex/ast"
)

func (ver *Verifier) objSatisfyFnReq(obj ast.Obj, state *VerState) ast.VerRet {
	switch objAs := obj.(type) {
	case ast.Atom:
		return ver.Env.LookupNamesInObj(objAs, map[string]struct{}{}).ToEmptyVerREt()
	case *ast.FnObj:
		return ver.fnObjSatisfyFnReq(objAs, state)
	case *ast.FnSetObj:
		panic("")
	case *ast.SetBuilderObj:
		panic("")
	default:
		panic(fmt.Sprintf("unknown object type: %T", obj))
	}
}

func (ver *Verifier) fnObjSatisfyFnReq(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	fnSet := ver.Env.GetFnInFnSet(fnObj.FnHead.String())
	if fnSet == nil {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("%s is not defined function", fnObj.String()))
	}

	// 因为我们已经知道了 f(a) 是函数了，所以f(a)的正确性已经在之前检查过了，所以不检查了。但，我们还是查一下 fnHead 是不是满足条件，比如fnObj是 f(a)(b) 那么要看看a是不是满足f的条件。
	verRetOfHead := ver.objSatisfyFnReq(fnObj.FnHead, state)
	if verRetOfHead.IsNotTrue() {
		return verRetOfHead
	}

	verRetOfFnArgs := ver.ArgsSatisfyFnParamRequirements(fnSet, fnObj.Params, state)
	if verRetOfFnArgs.IsNotTrue() {
		return verRetOfFnArgs
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) ArgsSatisfyFnParamRequirements(fnSet *ast.FnSetObj, arguments ast.ObjSlice, state *VerState) ast.VerRet {
	panic("")
}
