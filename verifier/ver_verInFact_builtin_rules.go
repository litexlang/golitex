// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) inFactBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("invalid number of parameters for in fact")
	}

	if stmt.TypeEnum == ast.FalsePure {
		return ver.falseInFactBuiltinRules(stmt, state)
	}

	ok, err := ver.verInSet_btRules(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.btLitNumInNatOrIntOrRatOrRealOrComplex(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok = ver.builtinSetsInSetSet(stmt, state)
	if ok {
		return true, nil
	}

	ok = ver.returnValueOfBuiltinArithmeticFnInReal(stmt, state)
	if ok {
		return true, nil
	}

	ok = ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if ok {
		return true, nil
	}

	ok = ver.verIn_N_Z_Q_R_C(stmt, state)
	if ok {
		return true, nil
	}

	ok, err = ver.inFnTemplateFact(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.inObjFact(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.verInSetProduct(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// ok, err = ver.atTupleIndex(stmt, state)
	// if err != nil {
	// 	return false, err
	// }
	// if ok {
	// 	return true, nil
	// }

	return false, nil
}

func (ver *Verifier) returnValueOfBuiltinArithmeticFnInReal(stmt *ast.SpecFactStmt, state *VerState) bool {
	ok := ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordReal)
	if !ok {
		return false
	}

	ok = ast.IsFn_WithHeadNameInSlice(stmt.Params[0], []string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower})

	if ok {
		if state.WithMsg {
			ver.successWithMsg(stmt.String(), "the return value of the builtin arithmetic function is in the real set")
		}
		return true
	} else {
		return false
	}
}

// func (ver *Verifier) returnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) bool {
// 	fcFn, ok := stmt.Params[0].(*ast.FcFn)
// 	if !ok {
// 		return false
// 	}

// 	if fcFn.HasHeadInSlice([]string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower}) {
// 		if stmt.Params[1] == ast.FcAtom(glob.KeywordReal) {
// 			if state.WithMsg {
// 				ver.successWithMsg(stmt.String(), "the return value of the builtin arithmetic function is in the real set")
// 			}
// 			return true
// 		}
// 		return false
// 	}

// 	if fcFn.HasHeadInSlice([]string{glob.KeywordLen, glob.KeySymbolPercent}) {
// 		if stmt.Params[1] == ast.FcAtom(glob.KeywordNatural) {
// 			if state.WithMsg {
// 				ver.successWithMsg(stmt.String(), "the return value of the builtin arithmetic function is in the natural set")
// 			}
// 			return true
// 		}
// 		return false
// 	}

// 	// fnDef, ok := ver.env.GetLatestFnTemplate(fcFn.FnHead)
// 	// if !ok {
// 	// 	return false // 这里不传error是有点道理的，因为+-*/的定义不在mem里
// 	// }

// 	// fnDef, ok := ver.env.GetLatestFnT_GivenNameIsIn(fcFn.FnHead.String())
// 	fnT_TheFcIsIn, ok := ver.GetFnTemplateSliceFcIsIn(fcFn.FnHead)
// 	if !ok {
// 		return false // 这里不传error是有点道理的，因为+-*/的定义不在mem里
// 	}
// 	fnDef := fnT_TheFcIsIn[len(fnT_TheFcIsIn)-1]

// 	uniMap := map[string]ast.Fc{}
// 	// if len(fnDef.Params) != len(fcFn.Params) {

// 	if fnDef.AsFcFn != nil {
// 		// TODO: 这里可以改成 stmt.Params[1] 是 fnDef.AsFcFn.Params[0] 母集
// 		ver.VerFactStmt(ast.NewEqualFact(stmt.Params[1], fnDef.AsFcFn.Params[0]), state)
// 		if state.WithMsg {
// 			ver.successWithMsg(stmt.String(), "the return value of the user defined function is in the function return set")
// 		}
// 		return true
// 	} else {
// 		if len(fnDef.AsFnTStruct.Params) != len(fcFn.Params) {
// 			return false
// 		}

// 		// for i, param := range fnDef.Params {
// 		for i, param := range fnDef.AsFnTStruct.Params {
// 			uniMap[param] = fcFn.Params[i]
// 		}

// 		// instantiatedRetSet, err := fnDef.RetSet.Instantiate(uniMap)
// 		instantiatedRetSet, err := fnDef.AsFnTStruct.RetSet.Instantiate(uniMap)
// 		if err != nil {
// 			return false
// 		}

// 		// ok = cmp.CmpFcAsStr(stmt.Params[1], instantiatedRetSet) // left.String() == right.String()
// 		// TODO: 这里可以改成 stmt.Params[1] 是 fnDef.AsFcFn.Params[0] 母集
// 		ok, err = ver.VerFactStmt(ast.NewEqualFact(stmt.Params[1], instantiatedRetSet), state)
// 		if err != nil {
// 			return false
// 		}
// 		if !ok {
// 			return false
// 		}

// 		if state.WithMsg {
// 			ver.successWithMsg(stmt.String(), "the return value of the user defined function is in the function return set")
// 		}

// 		return true
// 	}
// }

func (ver *Verifier) builtinSetsInSetSet(stmt *ast.SpecFactStmt, state *VerState) bool {
	ok := ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordSet)
	if !ok {
		return false
	}

	asAtom, ok := stmt.Params[0].(ast.FcAtom)
	if !ok {
		return false
	}

	// if asAtom.PkgName != glob.EmptyPkg {
	// 	return false
	// }

	if string(asAtom) == glob.KeywordNatural || string(asAtom) == glob.KeywordInteger || string(asAtom) == glob.KeywordReal || string(asAtom) == glob.KeywordComplex || string(asAtom) == glob.KeywordRational || string(asAtom) == glob.KeywordNPos {
		if state.WithMsg {
			ver.successWithMsg(stmt.String(), "the builtin rules")
		}
		return true
	}

	return false
}

func (ver *Verifier) inFnTemplateFact(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if asFcFn, ok := stmt.Params[1].(*ast.FcFn); ok {
		if ast.IsFnTemplate_FcFn(asFcFn) {
			ok, err := ver.ver_In_FnFcFn_FnTT(stmt.Params[0], asFcFn, state)
			if err != nil {
				return false, err
			}
			if ok {
				if state.WithMsg {
					ver.successWithMsg(stmt.String(), fmt.Sprintf("dom of template %s is in the domain of the template where function %s is in. Also, the return value of the function is in the return set of the template where function %s is in", stmt.Params[1], stmt.Params[0], stmt.Params[1]))
				}
				return true, nil
			}
		} else {
			// return false, nil
			ok, err := ver.ver_In_FnTT(stmt.Params[0], asFcFn, state)
			if err != nil {
				return false, err
			}
			if ok {
				if state.WithMsg {
					ver.successWithMsg(stmt.String(), fmt.Sprintf("dom of template %s is in the domain of the template where function %s is in. Also, the return value of the function is in the return set of the template where function %s is in", stmt.Params[1], stmt.Params[0], stmt.Params[1]))
				}
				return true, nil
			}
		}
		return false, nil
		// }
	}

	return false, nil
}

func (ver *Verifier) verInSet_btRules(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	var err error
	ok := ast.IsFcAtomEqualToGivenString(stmt.Params[1], glob.KeywordSet)
	if !ok {
		return false, nil
	}

	// 如果它是finite_set，则直接返回true
	ok, err = ver.fcIsFiniteSet(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// 如果它是N, Z, Q, R, C, 则直接返回true
	ok = ast.IsFcAtomEqualToGivenString(stmt.Params[0], glob.KeywordNatural) ||
		ast.IsFcAtomEqualToGivenString(stmt.Params[0], glob.KeywordInteger) ||
		ast.IsFcAtomEqualToGivenString(stmt.Params[0], glob.KeywordRational) ||
		ast.IsFcAtomEqualToGivenString(stmt.Params[0], glob.KeywordReal) ||
		ast.IsFcAtomEqualToGivenString(stmt.Params[0], glob.KeywordComplex) ||
		ast.IsFcAtomEqualToGivenString(stmt.Params[0], glob.KeywordNPos)
	if ok {
		return ver.processOkMsg(state, stmt.String(), "%s is a builtin set", stmt.Params[0])
	}

	// 如果是被定义好了的fn_template，则直接返回true
	asFcFn, ok := stmt.Params[1].(*ast.FcFn)
	if !ok {
		return false, nil
	}
	ok = ast.IsFnTemplate_FcFn(asFcFn)
	if ok {
		return ver.processOkMsg(state, stmt.String(), "%s is a fn template and all fn templates are sets", stmt.Params[0])
	}

	if leftAsAtom, ok := stmt.Params[0].(ast.FcAtom); ok {
		// _, ok := ver.env.GetFnTemplateDef(leftAsAtom)
		fnDef := ver.env.GetLatestFnT_GivenNameIsIn(leftAsAtom.String())
		if fnDef != nil {
			return ver.processOkMsg(state, stmt.String(), "%s is a fn template and all fn templates are sets", leftAsAtom)
		}
	}

	return false, nil
}

func (ver *Verifier) inObjFact(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	// right param is obj
	ok := ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordObj)
	if !ok {
		return false, nil
	}

	atoms := ast.GetAtomsInFc(stmt.Params[0])
	// 这里有点问题，N,Q,C 这种没算进去，要重新写一下。这里不能直接用 declared, 因为一方面 isDeclared会包含 prop, 一方面 obj isDeclared，会导致罗素悖论
	ok = ver.env.AtomsAreObj(atoms)
	if !ok {
		return false, nil
	}

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), fmt.Sprintf("all atoms in %s are declared as obj or literal number", stmt.Params[0]))
	}

	return true, nil
}

func (ver *Verifier) falseInFactBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	// 任何东西不在空集里
	ok, err := ver.nothingIsInEmptySet(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.objNotInSetWhenAllItemsInThatSetAreNotEqualToIt(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

// TODO 需要先证明一下它是finite set 去开始验证 len(n) = 0
func (ver *Verifier) nothingIsInEmptySet(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	verRet := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[1], ast.FcAtom(glob.KeywordFiniteSet)}, stmt.Line), state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet.ToBoolErr()
	}

	lenOverStmtName := ast.NewFcFn(ast.FcAtom(glob.KeywordLen), []ast.Fc{stmt.Params[1]})
	equalFact := ast.EqualFact(lenOverStmtName, ast.FcAtom("0"))
	verRet = ver.VerFactStmt(equalFact, state)
	return verRet.ToBoolErr()
}

func (ver *Verifier) trueExistInSt(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	pureInFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[1], stmt.Params[2]}, stmt.Line)
	verRet := ver.VerFactStmt(pureInFact, state)
	return verRet.ToBoolErr()
}

func (ver *Verifier) fcIsFiniteSet(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	// TODO: not sure whether I should add this nextState
	nextState := state.GetAddRound()

	finiteSetFact := ast.NewInFactWithFc(stmt.Params[0], ast.FcAtom(glob.KeywordFiniteSet))
	verRet := ver.VerFactStmt(finiteSetFact, nextState)
	return verRet.ToBoolErr()
}

func (ver *Verifier) objNotInSetWhenAllItemsInThatSetAreNotEqualToIt(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if stmt.TypeEnum != ast.FalsePure {
		return false, nil
	}

	notAllItemsInThatSetAreNotEqualToIt := ast.NewUniFact([]string{"x"}, []ast.Fc{stmt.Params[1]}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom("x"), stmt.Params[0]}, stmt.Line)}, stmt.Line)

	verRet := ver.VerFactStmt(notAllItemsInThatSetAreNotEqualToIt, state)
	return verRet.ToBoolErr()
}

func (ver *Verifier) verInSetProduct(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	// left must be (x, y, ...) right must be product(xSet, ySet, ...)
	fcFn, ok := stmt.Params[0].(*ast.FcFn)
	if !ok {
		return false, nil
	}
	ok = ast.IsFcAtomAndEqualToStr(fcFn.FnHead, glob.TupleFcFnHead)
	if !ok {
		return false, nil
	}

	setProductFn, ok := stmt.Params[1].(*ast.FcFn)
	if !ok {
		return false, nil
	}

	if len(fcFn.Params) != len(setProductFn.Params) {
		return false, nil
	}

	for i := range len(fcFn.Params) {
		inFact := ast.NewInFactWithParamFc(fcFn.Params[i], setProductFn.Params[i])
		verRet := ver.VerFactStmt(inFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet.ToBoolErr()
		}
	}

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), fmt.Sprintf("each item in tuple %s is in corresponding set %s", stmt.Params[0], stmt.Params[1]))
	}

	return true, nil
}

// func (ver *Verifier) atTupleIndex(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
// 	// if !ast.IsFcFnWithHeadName(stmt.Params[0], glob.TupleAtOp) {
// 	if !ast.IsFcFnWithHeadName(stmt.Params[0], glob.KeywordProj) {
// 		return false, nil
// 	}

// 	if !ast.IsFcFnWithHeadName(stmt.Params[0].(*ast.FcFn).Params[0], glob.TupleFcFnHead) {
// 		return false, nil
// 	}

// 	asIndex, ok := stmt.Params[0].(*ast.FcFn).Params[1].(ast.FcAtom)
// 	if !ok {
// 		return false, nil
// 	}

// 	asIndexAsInt, err := strconv.Atoi(string(asIndex))
// 	if err != nil {
// 		return false, nil
// 	}

// 	if asIndexAsInt < 0 || asIndexAsInt >= len(stmt.Params[0].(*ast.FcFn).Params[0].(*ast.FcFn).Params) {
// 		return false, nil
// 	}

// 	tupleAtIndex := stmt.Params[0].(*ast.FcFn).Params[0].(*ast.FcFn).Params[asIndexAsInt]

// 	equalFact := ast.NewInFactWithFc(tupleAtIndex, stmt.Params[1])
// 	ok, err = ver.VerFactStmt(equalFact, state)
// 	if err != nil {
// 		return false, err
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	return false, nil
// }

func (ver *Verifier) ver_In_FnFcFn_FnTT(left ast.Fc, fnFcFn *ast.FcFn, state *VerState) (bool, error) {
	ver.newEnv(ver.env)
	defer ver.deleteEnv_DeleteMsg()

	// check when parameters satisfy given fnFcFn parameter requirements, then it satisfies the fn template template requirement

	leftIsInWhichFnTT := ver.env.GetLatestFnT_GivenNameIsIn(left.String())
	if leftIsInWhichFnTT == nil {
		return false, nil
	}

	randomNames := []string{}
	for i := 0; i < len(leftIsInWhichFnTT.AsFnTStruct.Params); i++ {
		randomNames = append(randomNames, ver.env.GenerateUndeclaredRandomName())
	}
	randomAtoms := []ast.Fc{}
	for i := 0; i < len(leftIsInWhichFnTT.AsFnTStruct.Params); i++ {
		randomAtoms = append(randomAtoms, ast.FcAtom(randomNames[i]))
	}

	uniMap := map[string]ast.Fc{}
	for i := 0; i < len(leftIsInWhichFnTT.AsFnTStruct.Params); i++ {
		uniMap[leftIsInWhichFnTT.AsFnTStruct.Params[i]] = ast.FcAtom(randomNames[i])
	}

	// check parameters of the left satisfies the fn template template requirement
	for i, randomName := range randomNames {
		err := ver.env.NewObj_NoDuplicate(randomName, nil)
		if err != nil {
			return false, err
		}
		err = ver.env.NewFact(ast.NewInFactWithParamFc(ast.FcAtom(randomName), (fnFcFn.FnHead).(*ast.FcFn).Params[i]))
		if err != nil {
			return false, err
		}
	}

	leftToUniFact, err := leftIsInWhichFnTT.AsFnTStruct.DeriveUniFact_WithGivenFn(left)
	if err != nil {
		return false, err
	}

	instantiatedLeftToUniFact, err := leftToUniFact.Instantiate(uniMap)
	if err != nil {
		return false, err
	}
	instLeftUniFactAsUniFactStmt, ok := instantiatedLeftToUniFact.(*ast.UniFactStmt)
	if !ok {
		return false, nil
	}

	for i := range instLeftUniFactAsUniFactStmt.Params {
		fact := ast.NewInFactWithParamFc(ast.FcAtom(randomNames[i]), leftIsInWhichFnTT.AsFnTStruct.ParamSets[i])
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet.ToBoolErr()
		}

		err := ver.env.NewFact(fact)
		if err != nil {
			return false, err
		}
	}

	for i := range leftIsInWhichFnTT.AsFnTStruct.DomFacts {
		fact := leftIsInWhichFnTT.AsFnTStruct.DomFacts[i]
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet.ToBoolErr()
		}

		err = ver.env.NewFact(fact)
		if err != nil {
			return false, err
		}
	}

	// whether return value is in ret set of fnFcFn
	fn := ast.NewFcFn(left, randomAtoms)
	verRet := ver.VerFactStmt(ast.NewInFactWithParamFc(fn, fnFcFn.Params[0]), state)
	return verRet.ToBoolErr()
}

func (ver *Verifier) returnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) bool {
	fcFn, ok := stmt.Params[0].(*ast.FcFn)
	if !ok {
		return false
	}

	if fcFn.HasHeadInSlice([]string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower}) {
		if stmt.Params[1] == ast.FcAtom(glob.KeywordReal) {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), "the return value of the builtin arithmetic function is in the real set")
			}
			return true
		}
		return false
	}

	if fcFn.HasHeadInSlice([]string{glob.KeywordLen, glob.KeySymbolPercent}) {
		if stmt.Params[1] == ast.FcAtom(glob.KeywordNatural) {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), "the return value of the builtin arithmetic function is in the natural set")
			}
			return true
		}
		return false
	}

	setFcFnIsIn_ByItsFnT, err := ver.getRetSetOfFcFnByUsingItsFnT(fcFn)
	if err != nil {
		return false
	}

	verRet := ver.VerFactStmt(ast.EqualFact(stmt.Params[1], setFcFnIsIn_ByItsFnT), state)
	ok, _ = verRet.ToBoolErr()
	return ok
}

func (ver *Verifier) getRetSetOfFcFnByUsingItsFnT(fcFn *ast.FcFn) (ast.Fc, error) {
	// f(a)(b,c)(e,d,f) 返回 {f, f(a), f(a)(b,c), f(a)(b,c)(e,d,f)}, {nil, {a}, {b,c}, {e,d,f}}
	fnHeadChain_AndItSelf, _ := ast.GetFnHeadChain_AndItSelf(fcFn)

	// 从后往前找，直到找到有个 fnHead 被已知在一个 fnInFnTInterface 中
	// 比如 f(a)(b,c)(e,d,f) 我不知道 f(a)(b,c) 是哪个 fn_template 里的，但我发现 f(a) $in T 是知道的。那之后就是按T的返回值去套入b,c，然后再把e,d,f套入T的返回值的返回值
	// 此时 indexWhereLatestFnTIsGot 就是 1, FnToFnItemWhereLatestFnTIsGot 就是 f(a) 的 fnInFnTMemItem
	indexWhereLatestFnTIsGot, FnToFnItemWhereLatestFnTIsGot := ver.env.FindRightMostResolvedFn_Return_ResolvedIndexAndFnTMemItem(fnHeadChain_AndItSelf)

	// 比如 f(a)(b,c)(e,d,f) 我们现在得到了 f(a) 的 fnTStruct，那 curParamsChainIndex 就是 2, 表示 f(a) 对应的params就是 (b,c)
	curFnTStruct := (FnToFnItemWhereLatestFnTIsGot.AsFnTStruct)
	curParamsChainIndex := indexWhereLatestFnTIsGot + 1

	// 验证 paramsChain 是否满足 fnTStruct，比如 b,c 是否满足 f(a) 的参数要求
	for curParamsChainIndex < len(fnHeadChain_AndItSelf)-1 {
		curRetSet, ok := curFnTStruct.RetSet.(*ast.FcFn)
		if !ok {
			return nil, fmt.Errorf("curRetSet is not an FcFn")
		}

		var err error
		// curFnTStruct, err = ver.GetFnStructFromFnTName_CheckFnTParamsReq(curRetSet, state)
		curFnTStruct, err = ver.env.GetFnStructFromFnTName(curRetSet)
		if err != nil {
			return nil, err
		}

		curParamsChainIndex++
	}

	return curFnTStruct.RetSet, nil
}
