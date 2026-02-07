package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) objSatisfyFnReq(obj ast.Obj, state *VerState) ast.VerRet {
	switch objAs := obj.(type) {
	case ast.Atom:
		return ver.Env.LookupNamesInObj(objAs, map[string]struct{}{}).ToEmptyVerREt()
	case *ast.FnObj:
		objAsFnObj := objAs
		if ret := ver.isBuiltinFunction_VerReq(objAsFnObj, state); ret.IsTrue() || ret.IsErr() {
			return ret
		}

		return ver.fnObjSatisfyFnReq(objAs, state)
	case ast.FnSetObj:
		return ver.fnSetObjSatisfyFnReq(objAs, state)
	case *ast.SetBuilderObj:
		panic("object type SetBuilderObj is not supported")
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
		return verRetOfHead.AddExtraInfo(fmt.Sprintf("%s is not a valid function", fnObj.String()))
	}

	switch fnSet := fnSet.(type) {
	case *ast.FnSetObjWithoutName:
		verRetOfFnArgs := ver.ArgsSatisfyFnSetObjWhenNameIsEmpty(fnSet, fnObj.Params, state)
		if verRetOfFnArgs.IsNotTrue() {
			return verRetOfFnArgs.AddExtraInfo(fmt.Sprintf("%s is not a valid function", fnObj.String()))
		}
		return ast.NewTrueVerRet(nil, nil, "")
	case *ast.FnSetObjWithName:
		verRetOfFnArgs := ver.ArgsSatisfyFnSetObjWithName(fnSet, fnObj.Params, state)
		if verRetOfFnArgs.IsNotTrue() {
			return verRetOfFnArgs.AddExtraInfo(fmt.Sprintf("%s is not a valid function", fnObj.String()))
		}
		return ast.NewTrueVerRet(nil, nil, "")
	default:
		panic(fmt.Sprintf("unknown function set type: %T", fnSet))
	}
}

func (ver *Verifier) ArgsSatisfyFnSetObjWhenNameIsEmpty(fnSet *ast.FnSetObjWithoutName, arguments ast.ObjSlice, state *VerState) ast.VerRet {

	if len(arguments) != len(fnSet.ParamSets) {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("the number of arguments is not equal to the number of parameter sets of %s", fnSet))
	}

	ver.newEnv()
	defer ver.deleteEnv()

	for i, paramSet := range fnSet.ParamSets {
		inFact := ast.NewInFactWithObj(arguments[i], paramSet)
		verRet := ver.VerFactStmt(inFact, state)
		if verRet.IsNotTrue() {
			return verRet
		}
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) ArgsSatisfyFnSetObjWithName(fnSet *ast.FnSetObjWithName, arguments ast.ObjSlice, state *VerState) ast.VerRet {

	if len(arguments) != len(fnSet.ParamSets) {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("the number of arguments is not equal to the number of parameter sets of %s", fnSet))
	}

	ver.newEnv()
	defer ver.deleteEnv()

	paramArgMap := make(map[string]ast.Obj)
	for i, param := range fnSet.Params {
		paramArgMap[param] = arguments[i]
	}

	for i, paramSet := range fnSet.ParamSets {
		newParamSet, err := paramSet.Instantiate(paramArgMap)
		if err != nil {
			return ast.NewErrVerRet(nil).AddExtraInfo(err.Error())
		}
		inFact := ast.NewInFactWithObj(arguments[i], newParamSet)
		verRet := ver.VerFactStmt(inFact, state)
		if verRet.IsNotTrue() {
			return verRet
		}
	}

	for _, fact := range fnSet.DomFacts {
		newFact, err := fact.InstantiateFact(paramArgMap)
		if err != nil {
			return ast.NewErrVerRet(fact).AddExtraInfo(err.Error())
		}
		verRet := ver.VerFactStmt(newFact.(ast.FactStmt), state)
		if verRet.IsNotTrue() {
			return verRet
		}
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) fnSetObjSatisfyFnReq(fnSetObj ast.FnSetObj, state *VerState) ast.VerRet {
	switch fnSetObj := fnSetObj.(type) {
	case *ast.FnSetObjWithoutName:
		return ver.fnSetObjSatisfyFnReqWhenFnNameIsEmpty(fnSetObj, state)
	case *ast.FnSetObjWithName:
		return ver.fnSetObjSatisfyFnReqWhenFnNameIsNotEmpty(fnSetObj, state)
	default:
		panic(fmt.Sprintf("unknown function set object type: %T", fnSetObj))
	}
}

func (ver *Verifier) fnSetObjSatisfyFnReqWhenFnNameIsEmpty(fnSetObj *ast.FnSetObjWithoutName, state *VerState) ast.VerRet {
	for _, paramSet := range fnSetObj.ParamSets {
		verRet := ver.objSatisfyFnReq(paramSet, state)
		if verRet.IsNotTrue() {
			return verRet
		}
	}

	verRet := ver.objSatisfyFnReq(fnSetObj.RetSet, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) fnSetObjSatisfyFnReqWhenFnNameIsNotEmpty(fnSetObj *ast.FnSetObjWithName, state *VerState) ast.VerRet {
	for _, paramSet := range fnSetObj.ParamSets {
		verRet := ver.objSatisfyFnReq(paramSet, state)
		if verRet.IsNotTrue() {
			return verRet
		}
	}

	verRet := ver.objSatisfyFnReq(fnSetObj.RetSet, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	ver.newEnv()
	defer ver.deleteEnv()

	newFnSetObj, err := ver.Env.ReplaceFnNameAndParamsWithNoDuplicateNames(fnSetObj)
	if err != nil {
		return ast.NewErrVerRet(nil).AddExtraInfo(err.Error())
	}

	// 声明这个函数
	defLetStmt := ast.NewDefLetStmt([]string{newFnSetObj.FnName}, []ast.Obj{newFnSetObj}, []ast.FactStmt{}, glob.BuiltinLine0)
	ret := ver.Env.DefLetStmt(defLetStmt)
	if ret.IsNotTrue() {
		return ast.NewErrVerRet(nil).AddExtraInfo(ret.String())
	}

	// 声明里面的变量
	defLet2 := ast.NewDefLetStmt(newFnSetObj.Params, newFnSetObj.ParamSets, newFnSetObj.DomFacts.ToFactStmtSlice(), glob.BuiltinLine0)
	ret2 := ver.Env.DefLetStmt(defLet2)
	if ret2.IsNotTrue() {
		return ast.NewErrVerRet(nil).AddExtraInfo(ret2.String())
	}

	// 检查then里的东西是不是满足条件
	for _, then := range newFnSetObj.ThenFacts {
		switch then := then.(type) {
		case ast.SpecificFactStmt:
			verRet := ver.checkFnsReq(then, state)
			if verRet.IsNotTrue() {
				return verRet
			}
		case *ast.OrStmt:
			verRet := ver.checkOrFnReq(then, state)
			if verRet.IsNotTrue() {
				return verRet
			}
		default:
			panic(fmt.Sprintf("unknown then type: %T", then))
		}
	}

	return ast.NewTrueVerRet(nil, nil, "")
}
