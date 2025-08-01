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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
)

func (ver *Verifier) inFactBuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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

	ok, err = ver.atTupleIndex(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) returnValueOfBuiltinArithmeticFnInReal(stmt *ast.SpecFactStmt, state VerState) bool {
	ok := ast.IsFcAtomAndEqualToStr(stmt.Params[1], glob.KeywordReal)
	if !ok {
		return false
	}

	ok = ast.IsFn_WithHeadNameInSlice(stmt.Params[0], []string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower})

	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "the return value of the builtin arithmetic function is in the real set")
		}
		return true
	} else {
		return false
	}
}

func (ver *Verifier) returnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state VerState) bool {
	fcFn, ok := stmt.Params[0].(*ast.FcFn)
	if !ok {
		return false
	}

	if fcFn.HasHeadInSlice([]string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower}) {
		if stmt.Params[1] == ast.FcAtom(glob.KeywordReal) {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), "the return value of the builtin arithmetic function is in the real set")
			}
			return true
		}
		return false
	}

	if fcFn.HasHeadInSlice([]string{glob.KeywordLen, glob.KeySymbolPercent}) {
		if stmt.Params[1] == ast.FcAtom(glob.KeywordNatural) {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), "the return value of the builtin arithmetic function is in the natural set")
			}
			return true
		}
		return false
	}

	// fnDef, ok := ver.env.GetLatestFnTemplate(fcFn.FnHead)
	// if !ok {
	// 	return false // 这里不传error是有点道理的，因为+-*/的定义不在mem里
	// }

	fnDef, ok := ver.env.GetLatestFnTT_GivenNameIsIn(fcFn.FnHead.String())
	if !ok {
		return false // 这里不传error是有点道理的，因为+-*/的定义不在mem里
	}

	uniMap := map[string]ast.Fc{}
	// if len(fnDef.Params) != len(fcFn.Params) {
	if len(fnDef.FnTemplateStmt.Params) != len(fcFn.Params) {
		return false
	}

	// for i, param := range fnDef.Params {
	for i, param := range fnDef.FnTemplateStmt.Params {
		uniMap[param] = fcFn.Params[i]
	}

	// instantiatedRetSet, err := fnDef.RetSet.Instantiate(uniMap)
	instantiatedRetSet, err := fnDef.FnTemplateStmt.RetSet.Instantiate(uniMap)
	if err != nil {
		return false
	}

	// ok = cmp.CmpFcAsStr(stmt.Params[1], instantiatedRetSet) // left.String() == right.String()
	ok, err = ver.VerFactStmt(ast.NewEqualFact(stmt.Params[1], instantiatedRetSet), state)
	if err != nil {
		return false
	}
	if !ok {
		return false
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), "the return value of the user defined function is in the function return set")
	}

	return true
}

func (ver *Verifier) builtinSetsInSetSet(stmt *ast.SpecFactStmt, state VerState) bool {
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
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "the builtin rules")
		}
		return true
	}

	return false
}

func (ver *Verifier) inFnTemplateFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if asFcFn, ok := stmt.Params[1].(*ast.FcFn); ok {
		if ast.IsFnFcFn(asFcFn) {
			ok, err := ver.ver_In_FnFcFn_FnTT(stmt.Params[0], asFcFn, state)
			if err != nil {
				return false, err
			}
			if ok {
				if state.requireMsg() {
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
				if state.requireMsg() {
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

// TODO: inFnTemplateFact
// func (ver *Verifier) inFnTemplateFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	return false, nil
// 	var fnTemplate *ast.FnTemplateNoName
// 	var err error

// 	if templateName, ok := stmt.Params[1].(ast.FcAtom); ok {
// 		if !ok {
// 			return false, nil
// 		}

// 		fnTDef, ok := ver.env.GetFnTemplateTemplateDef(templateName)
// 		if !ok {
// 			return false, nil
// 		}
// 		fnTemplate = &fnTDef.
// 	} else if fnFn, ok := stmt.Params[1].(*ast.FcFn); ok && ast.IsFnFcFn(fnFn) {
// 		fnTemplate, err = ast.FnFcToFnTemplateStmt(fnFn)
// 		if err != nil {
// 			return false, err
// 		}
// 	} else {
// 		return false, nil
// 	}

// 	// Case1: 用直接验证的方式去验证，比如 know forall x Z, y Z: x + y $in Z, 可以推出 fn(Z, Z) Z·
// 	// derivedUniFact := fnTemplate.DeriveUniFact(stmt.Params[0])
// 	if fnTemplate.Name != "" {
// 		derivedUniFact := fnTemplate.DeriveUniFact2()
// 		instantiatedUniFact, err := derivedUniFact.Instantiate(map[string]ast.Fc{string(fnTemplate.DefHeader.Name): stmt.Params[0]})
// 		if err != nil {
// 			return false, err
// 		}

// 		ok, err := ver.VerFactStmt(instantiatedUniFact, state)
// 		if err != nil {
// 			return false, err
// 		}
// 		if ok {
// 			return true, nil
// 		}
// 	} else {
// 		derivedUniFact := fnTemplate.DeriveUniFact3(stmt.Params[0])
// 		ok, err := ver.VerFactStmt(derivedUniFact, state)
// 		if err != nil {
// 			return false, err
// 		}
// 		if ok {
// 			return true, nil
// 		}
// 	}

// 	// Case2: 用已知的符合的fn_template去验证

// 	instantiatedDefFnStmt, err := fnTemplate.InstantiateByFnName_WithTemplateNameGivenFc(stmt.Params[0])
// 	if err != nil {
// 		return false, nil
// 	}

// 	specFactDefs, ok := ver.env.GetFnTemplateOfFc(stmt.Params[0])
// 	if !ok {
// 		return false, nil
// 	}

// 	for i := len(specFactDefs) - 1; i >= 0; i-- {
// 		ok, err := ver.leftDomLeadToRightDom_RightDomLeadsToRightThen(stmt.Params[0], specFactDefs[i], instantiatedDefFnStmt, state)
// 		if err != nil {
// 			return false, err
// 		}
// 		if ok {
// 			return true, nil
// 		}
// 	}

// 	return false, nil
// }

func (ver *Verifier) verInSet_OverAllObjsEqualToIt(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ver.isProvingObjInSetUsingEqualObjs = true
	defer func() {
		ver.isProvingObjInSetUsingEqualObjs = false
	}()

	ok, err := ver.VerFactStmt(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	objectsEqualToIt, ok := ver.env.GetEqualFcs(stmt.Params[0])
	if !ok {
		return false, nil
	}

	for _, obj := range *objectsEqualToIt {
		ok, err := ver.VerFactStmt(ast.NewInFactWithFc(obj, stmt.Params[1]), state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) verInSet_btRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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
	ok = ast.IsFnFcFn(asFcFn)
	if ok {
		return ver.processOkMsg(state, stmt.String(), "%s is a fn template and all fn templates are sets", stmt.Params[0])
	}

	if leftAsAtom, ok := stmt.Params[0].(ast.FcAtom); ok {
		// _, ok := ver.env.GetFnTemplateDef(leftAsAtom)
		_, ok := ver.env.GetLatestFnTT_GivenNameIsIn(leftAsAtom.String())
		if ok {
			return ver.processOkMsg(state, stmt.String(), "%s is a fn template and all fn templates are sets", leftAsAtom)
		}
	}

	return false, nil
}

func (ver *Verifier) inObjFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), fmt.Sprintf("all atoms in %s are declared as obj or literal number", stmt.Params[0]))
	}

	return true, nil
}

func (ver *Verifier) falseInFactBuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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
func (ver *Verifier) nothingIsInEmptySet(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[1], ast.FcAtom(glob.KeywordFiniteSet)}), state); err != nil || !ok {
		return ok, err
	}

	lenOverStmtName := ast.NewFcFn(ast.FcAtom(glob.KeywordLen), []ast.Fc{stmt.Params[1]})
	equalFact := ast.EqualFact(lenOverStmtName, ast.FcAtom("0"))
	ok, err := ver.VerFactStmt(equalFact, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) trueExistInSt(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	pureInFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Params[1], stmt.Params[2]})
	ok, err := ver.VerFactStmt(pureInFact, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return false, nil
}

func (ver *Verifier) fcIsFiniteSet(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// TODO: not sure whether I should add this nextState
	nextState := state.addRound()

	finiteSetFact := ast.NewInFactWithFc(stmt.Params[0], ast.FcAtom(glob.KeywordFiniteSet))
	ok, err := ver.VerFactStmt(finiteSetFact, nextState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) objNotInSetWhenAllItemsInThatSetAreNotEqualToIt(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.TypeEnum != ast.FalsePure {
		return false, nil
	}

	notAllItemsInThatSetAreNotEqualToIt := ast.NewUniFact([]string{"x"}, []ast.Fc{stmt.Params[1]}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom("x"), stmt.Params[0]})})

	ok, err := ver.VerFactStmt(notAllItemsInThatSetAreNotEqualToIt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return false, nil
}

func (ver *Verifier) verInSetProduct(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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
	ok = ast.IsFcAtomAndEqualToStr(setProductFn.FnHead, glob.KeywordSetProduct)
	if !ok {
		return false, nil
	}

	if len(fcFn.Params) != len(setProductFn.Params) {
		return false, nil
	}

	for i := range len(fcFn.Params) {
		inFact := ast.NewInFactWithParamFc(fcFn.Params[i], setProductFn.Params[i])
		ok, err := ver.VerFactStmt(inFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), fmt.Sprintf("each item in tuple %s is in corresponding set %s", stmt.Params[0], stmt.Params[1]))
	}

	return true, nil
}

func (ver *Verifier) atTupleIndex(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// if !ast.IsFcFnWithHeadName(stmt.Params[0], glob.TupleAtOp) {
	if !ast.IsFcFnWithHeadName(stmt.Params[0], glob.KeywordProj) {
		return false, nil
	}

	if !ast.IsFcFnWithHeadName(stmt.Params[0].(*ast.FcFn).Params[0], glob.TupleFcFnHead) {
		return false, nil
	}

	asIndex, ok := stmt.Params[0].(*ast.FcFn).Params[1].(ast.FcAtom)
	if !ok {
		return false, nil
	}

	asIndexAsInt, err := strconv.Atoi(string(asIndex))
	if err != nil {
		return false, nil
	}

	if asIndexAsInt < 0 || asIndexAsInt >= len(stmt.Params[0].(*ast.FcFn).Params[0].(*ast.FcFn).Params) {
		return false, nil
	}

	tupleAtIndex := stmt.Params[0].(*ast.FcFn).Params[0].(*ast.FcFn).Params[asIndexAsInt]

	equalFact := ast.NewInFactWithFc(tupleAtIndex, stmt.Params[1])
	ok, err = ver.VerFactStmt(equalFact, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) ver_In_FnFcFn_FnTT(left ast.Fc, fnFcFn *ast.FcFn, state VerState) (bool, error) {
	ver.newEnv(ver.env)
	defer ver.deleteEnv_DeleteMsg()

	// check when parameters satisfy given fnFcFn parameter requirements, then it satisfies the fn template template requirement

	leftIsInWhichFnTT, ok := ver.env.GetLatestFnTT_GivenNameIsIn(left.String())
	if !ok {
		return false, nil
	}

	randomNames := []string{}
	for i := 0; i < len(leftIsInWhichFnTT.FnTemplateStmt.Params); i++ {
		randomNames = append(randomNames, ver.env.GenerateUndeclaredRandomName())
	}
	randomAtoms := []ast.Fc{}
	for i := 0; i < len(leftIsInWhichFnTT.FnTemplateStmt.Params); i++ {
		randomAtoms = append(randomAtoms, ast.FcAtom(randomNames[i]))
	}

	uniMap := map[string]ast.Fc{}
	for i := 0; i < len(leftIsInWhichFnTT.FnTemplateStmt.Params); i++ {
		uniMap[leftIsInWhichFnTT.FnTemplateStmt.Params[i]] = ast.FcAtom(randomNames[i])
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

	leftToUniFact, err := leftIsInWhichFnTT.FnTemplateStmt.DeriveUniFact_WithGivenFn(left)
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
		fact := ast.NewInFactWithParamFc(ast.FcAtom(randomNames[i]), leftIsInWhichFnTT.FnTemplateStmt.ParamSets[i])
		ok, err := ver.VerFactStmt(fact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}

		err = ver.env.NewFact(fact)
		if err != nil {
			return false, err
		}
	}

	for i := range leftIsInWhichFnTT.FnTemplateStmt.DomFacts {
		fact := leftIsInWhichFnTT.FnTemplateStmt.DomFacts[i]
		ok, err := ver.VerFactStmt(fact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}

		err = ver.env.NewFact(fact)
		if err != nil {
			return false, err
		}
	}

	// whether return value is in ret set of fnFcFn
	fn := ast.NewFcFn(left, randomAtoms)
	ok, err = ver.VerFactStmt(ast.NewInFactWithParamFc(fn, fnFcFn.Params[0]), state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}
