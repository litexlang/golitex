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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) inFactBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	if len(stmt.Params) != 2 {
		return NewVerErr(fmt.Sprintf("invalid number of parameters for in fact: %d", len(stmt.Params)))
	}

	if stmt.TypeEnum == ast.FalsePure {
		return ver.falseInFactBuiltinRules(stmt, state)
	}

	var verRet VerRet
	var ok bool

	verRet = ver.verInSet_btRules(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.btLitNumInNatOrIntOrRatOrRealOrComplex(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	ok = ver.builtinSetsInSetSet(stmt, state)
	if ok {
		return NewVerTrue("")
	}

	ok = ver.returnValueOfBuiltinArithmeticFnInReal(stmt, state)
	if ok {
		return NewVerTrue("")
	}

	ok = ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if ok {
		return NewVerTrue("")
	}

	ok = ver.verIn_N_Z_Q_R_C(stmt, state)
	if ok {
		return NewVerTrue("")
	}

	verRet = ver.inFnTemplateFact(stmt, state)
	if verRet.IsErr() {
		return NewVerErr(verRet.String())
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.inObjFact(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInSetProduct(stmt, state)
	if verRet.IsErr() {
		return NewVerErr(verRet.String())
	}
	if verRet.IsTrue() {
		return verRet
	}

	return NewVerUnknown("")
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

func (ver *Verifier) inFnTemplateFact(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	if asFcFn, ok := stmt.Params[1].(*ast.FcFn); ok {
		if ast.IsFnTemplate_FcFn(asFcFn) {
			verRet := ver.ver_In_FnFcFn_FnTT(stmt.Params[0], asFcFn, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				if state.WithMsg {
					ver.successWithMsg(stmt.String(), fmt.Sprintf("dom of template %s is in the domain of the template where function %s is in. Also, the return value of the function is in the return set of the template where function %s is in", stmt.Params[1], stmt.Params[0], stmt.Params[1]))
				}
				return NewVerTrue("")
			}
		} else {
			// return false, nil
			verRet := ver.ver_In_FnTT(stmt.Params[0], asFcFn, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				if state.WithMsg {
					ver.successWithMsg(stmt.String(), fmt.Sprintf("dom of template %s is in the domain of the template where function %s is in. Also, the return value of the function is in the return set of the template where function %s is in", stmt.Params[1], stmt.Params[0], stmt.Params[1]))
				}
				return NewVerTrue("")
			}
		}
		return NewVerUnknown("")
		// }
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verInSet_btRules(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	var verRet VerRet
	ok := ast.IsFcAtomEqualToGivenString(stmt.Params[1], glob.KeywordSet)
	if !ok {
		return NewVerUnknown("")
	}

	// 如果它是finite_set，则直接返回true
	verRet = ver.fcIsFiniteSet(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return NewVerTrue("")
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
		return NewVerUnknown("")
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

	return NewVerUnknown("")
}

func (ver *Verifier) inObjFact(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	// right param is obj
	ok := ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordObj)
	if !ok {
		return NewVerUnknown("")
	}

	atoms := ast.GetAtomsInFc(stmt.Params[0])
	// 这里有点问题，N,Q,C 这种没算进去，要重新写一下。这里不能直接用 declared, 因为一方面 isDeclared会包含 prop, 一方面 obj isDeclared，会导致罗素悖论
	ok = ver.env.AtomsAreObj(atoms)
	if !ok {
		return NewVerUnknown("")
	}

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), fmt.Sprintf("all atoms in %s are declared as obj or literal number", stmt.Params[0]))
	}

	return NewVerTrue("")
}

func (ver *Verifier) falseInFactBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	// 任何东西不在空集里
	verRet := ver.nothingIsInEmptySet(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.objNotInSetWhenAllItemsInThatSetAreNotEqualToIt(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	return NewVerUnknown("")
}

// TODO 需要先证明一下它是finite set 去开始验证 len(n) = 0
func (ver *Verifier) nothingIsInEmptySet(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	verRet := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[1], ast.FcAtom(glob.KeywordFiniteSet)}, stmt.Line), state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	lenOverStmtName := ast.NewFcFn(ast.FcAtom(glob.KeywordLen), []ast.Fc{stmt.Params[1]})
	equalFact := ast.EqualFact(lenOverStmtName, ast.FcAtom("0"))
	verRet = ver.VerFactStmt(equalFact, state)
	return verRet
}

func (ver *Verifier) trueExistInSt(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	pureInFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[1], stmt.Params[2]}, stmt.Line)
	verRet := ver.VerFactStmt(pureInFact, state)
	return verRet
}

func (ver *Verifier) fcIsFiniteSet(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	// TODO: not sure whether I should add this nextState
	nextState := state.GetAddRound()

	finiteSetFact := ast.NewInFactWithFc(stmt.Params[0], ast.FcAtom(glob.KeywordFiniteSet))
	verRet := ver.VerFactStmt(finiteSetFact, nextState)
	return verRet
}

func (ver *Verifier) objNotInSetWhenAllItemsInThatSetAreNotEqualToIt(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	if stmt.TypeEnum != ast.FalsePure {
		return NewVerUnknown("")
	}

	notAllItemsInThatSetAreNotEqualToIt := ast.NewUniFact([]string{"x"}, []ast.Fc{stmt.Params[1]}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom("x"), stmt.Params[0]}, stmt.Line)}, stmt.Line)

	verRet := ver.VerFactStmt(notAllItemsInThatSetAreNotEqualToIt, state)
	return verRet
}

func (ver *Verifier) verInSetProduct(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	// left must be (x, y, ...) right must be product(xSet, ySet, ...)
	fcFn, ok := stmt.Params[0].(*ast.FcFn)
	if !ok {
		return NewVerUnknown("")
	}
	ok = ast.IsFcAtomAndEqualToStr(fcFn.FnHead, glob.TupleFcFnHead)
	if !ok {
		return NewVerUnknown("")
	}

	setProductFn, ok := stmt.Params[1].(*ast.FcFn)
	if !ok {
		return NewVerUnknown("")
	}

	if len(fcFn.Params) != len(setProductFn.Params) {
		return NewVerUnknown("")
	}

	for i := range len(fcFn.Params) {
		inFact := ast.NewInFactWithParamFc(fcFn.Params[i], setProductFn.Params[i])
		verRet := ver.VerFactStmt(inFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), fmt.Sprintf("each item in tuple %s is in corresponding set %s", stmt.Params[0], stmt.Params[1]))
	}

	return NewVerTrue("")
}

func (ver *Verifier) ver_In_FnFcFn_FnTT(left ast.Fc, fnFcFn *ast.FcFn, state *VerState) VerRet {
	ver.newEnv(ver.env)
	defer ver.deleteEnv_DeleteMsg()

	// check when parameters satisfy given fnFcFn parameter requirements, then it satisfies the fn template template requirement

	leftIsInWhichFnTT := ver.env.GetLatestFnT_GivenNameIsIn(left.String())
	if leftIsInWhichFnTT == nil {
		return NewVerUnknown("")
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
			return NewVerErr(err.Error())
		}
		err = ver.env.NewFact(ast.NewInFactWithParamFc(ast.FcAtom(randomName), (fnFcFn.FnHead).(*ast.FcFn).Params[i]))
		if err != nil {
			return NewVerErr(err.Error())
		}
	}

	leftToUniFact, err := leftIsInWhichFnTT.AsFnTStruct.DeriveUniFact_WithGivenFn(left)
	if err != nil {
		return NewVerErr(err.Error())
	}

	instantiatedLeftToUniFact, err := leftToUniFact.InstantiateFact(uniMap)
	if err != nil {
		return NewVerErr(err.Error())
	}
	instLeftUniFactAsUniFactStmt, ok := instantiatedLeftToUniFact.(*ast.UniFactStmt)
	if !ok {
		return NewVerUnknown("")
	}

	for i := range instLeftUniFactAsUniFactStmt.Params {
		fact := ast.NewInFactWithParamFc(ast.FcAtom(randomNames[i]), leftIsInWhichFnTT.AsFnTStruct.ParamSets[i])
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		err := ver.env.NewFact(fact)
		if err != nil {
			return NewVerErr(err.Error())
		}
	}

	for i := range leftIsInWhichFnTT.AsFnTStruct.DomFacts {
		fact := leftIsInWhichFnTT.AsFnTStruct.DomFacts[i]
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		err = ver.env.NewFact(fact)
		if err != nil {
			return NewVerErr(err.Error())
		}
	}

	// whether return value is in ret set of fnFcFn
	fn := ast.NewFcFn(left, randomAtoms)
	verRet := ver.VerFactStmt(ast.NewInFactWithParamFc(fn, fnFcFn.Params[0]), state)
	return verRet
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
