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
	"strconv"
)

func (ver *Verifier) inFactBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(stmt.Params) != 2 {
		return NewExecErr(fmt.Sprintf("invalid number of parameters for in fact: %d", len(stmt.Params)))
	}

	if stmt.TypeEnum == ast.FalsePure {
		return ver.falseInFactBuiltinRules(stmt, state)
	}

	var verRet ExecRet

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

	verRet = ver.builtinSetsInSetSet(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.returnValueOfBuiltinArithmeticFnInReal(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.returnValueOfUserDefinedFnInFnReturnSet(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verIn_N_Z_Q_R_C(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.inFnTemplateFact(stmt, state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
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
		return NewExecErr(verRet.String())
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInCartSet(stmt, state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	}
	if verRet.IsTrue() {
		return verRet
	}

	// fn(R)R $in set
	verRet = ver.FnTemplateIsASet(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return NewExecUnknown("")
}

func (ver *Verifier) FnTemplateIsASet(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if asAtom, ok := stmt.Params[1].(ast.Atom); ok {
		if asAtom != glob.KeywordSet {
			return NewExecUnknown("")
		}
	}

	if asFcFn, ok := stmt.Params[0].(*ast.FnObj); ok {
		if ast.IsFnTemplate_FcFn(asFcFn) {
			// 所有参数还都真是集合
			for i := range asFcFn.FnHead.(*ast.FnObj).Params {
				verRet := ver.VerFactStmt(ast.NewInFactWithParamFc(asFcFn.FnHead.(*ast.FnObj).Params[i], ast.Atom(glob.KeywordSet)), state)
				if verRet.IsErr() || verRet.IsUnknown() {
					return NewExecUnknown("")
				}
			}

			for i := range asFcFn.Params {
				if verRet := ver.VerFactStmt(ast.NewInFactWithParamFc(asFcFn.Params[i], ast.Atom(glob.KeywordSet)), state); verRet.IsErr() || verRet.IsUnknown() {
					return NewExecUnknown("")
				}
			}
			return NewExecTrue("")
		}
	}

	// TODO 如果fnTemplate 里面的涉及到的 paramSet 也都是集合，那就返回true

	return NewExecUnknown("")
}

func (ver *Verifier) returnValueOfBuiltinArithmeticFnInReal(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	ok := ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordReal)
	if !ok {
		return NewExecUnknown("")
	}

	ok = ast.IsFn_WithHeadNameInSlice(stmt.Params[0], map[string]struct{}{glob.KeySymbolPlus: {}, glob.KeySymbolMinus: {}, glob.KeySymbolStar: {}, glob.KeySymbolSlash: {}, glob.KeySymbolPower: {}})

	if ok {
		msg := fmt.Sprintf("return value of builtin arithmetic function %s is in Real", stmt.Params[0])
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
	}
	return NewExecUnknown("")
}

func (ver *Verifier) builtinSetsInSetSet(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	ok := ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordSet)
	if !ok {
		return NewExecUnknown("")
	}

	asAtom, ok := stmt.Params[0].(ast.Atom)
	if !ok {
		return NewExecUnknown("")
	}

	// if asAtom.PkgName != glob.EmptyPkg {
	// 	return NewExecUnknown("")
	// }

	if string(asAtom) == glob.KeywordNatural || string(asAtom) == glob.KeywordInteger || string(asAtom) == glob.KeywordReal || string(asAtom) == glob.KeywordComplex || string(asAtom) == glob.KeywordRational || string(asAtom) == glob.KeywordNPos {
		msg := fmt.Sprintf("%s is a builtin set", asAtom)
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
	}

	return NewExecUnknown("")
}

func (ver *Verifier) inFnTemplateFact(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if asFcFn, ok := stmt.Params[1].(*ast.FnObj); ok {
		if ast.IsFnTemplate_FcFn(asFcFn) {
			verRet := ver.ver_In_FnFcFn_FnTT(stmt.Params[0], asFcFn, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				msg := fmt.Sprintf("dom of template %s is in the domain of the template where function %s is in. Also, the return value of the function is in the return set of the template where function %s is in", stmt.Params[1], stmt.Params[0], stmt.Params[1])
				return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
			}
		} else {
			// return false, nil
			verRet := ver.ver_In_FnTT(stmt.Params[0], asFcFn, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				msg := fmt.Sprintf("dom of template %s is in the domain of the template where function %s is in. Also, the return value of the function is in the return set of the template where function %s is in", stmt.Params[1], stmt.Params[0], stmt.Params[1])
				return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
			}
		}
		return NewExecUnknown("")
		// }
	}

	return NewExecUnknown("")
}

func (ver *Verifier) verInSet_btRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	var verRet ExecRet
	ok := ast.IsFcAtomEqualToGivenString(stmt.Params[1], glob.KeywordSet)
	if !ok {
		return NewExecUnknown("")
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

	// 如果它是 cart(...)，直接返回true
	if ast.IsFn_WithHeadName(stmt.Params[0], glob.KeywordCart) {
		return ver.processOkMsg(state, stmt.String(), "%s is a builtin set", stmt.Params[0])
	}

	verRet = ver.FnTemplateIsASet(stmt, state.GetNoMsg())
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := "When parameter sets of a fn template are all sets, then the fn template is a set"
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(msg))
	}

	// 如果是被定义好了的fn_template，则直接返回true
	asFcFn, ok := stmt.Params[1].(*ast.FnObj)
	if !ok {
		return NewExecUnknown("")
	}
	ok = ast.IsFnTemplate_FcFn(asFcFn)
	if ok {
		return ver.processOkMsg(state, stmt.String(), "%s is a fn template and all fn templates are sets", stmt.Params[0])
	}

	if leftAsAtom, ok := stmt.Params[0].(ast.Atom); ok {
		// _, ok := ver.env.GetFnTemplateDef(leftAsAtom)
		fnDef := ver.Env.GetLatestFnT_GivenNameIsIn(leftAsAtom.String())
		if fnDef != nil {
			return ver.processOkMsg(state, stmt.String(), "%s is a fn template and all fn templates are sets", leftAsAtom)
		}
	}

	return NewExecUnknown("")
}

func (ver *Verifier) inObjFact(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	// right param is obj
	ok := ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordObj)
	if !ok {
		return NewExecUnknown("")
	}

	atoms := ast.GetAtomsInObj(stmt.Params[0])
	// 这里有点问题，N,Q,C 这种没算进去，要重新写一下。这里不能直接用 declared, 因为一方面 isDeclared会包含 prop, 一方面 obj isDeclared，会导致罗素悖论
	ok = ver.Env.AtomsAreObj(atoms)
	if !ok {
		return NewExecUnknown("")
	}

	msg := fmt.Sprintf("all atoms in %s are declared as obj or literal number", stmt.Params[0])
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
}

func (ver *Verifier) falseInFactBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
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

	// 如果你是数字，那么必须要真的长成自然数的形状，才是自然数，否则不行
	// 也就是说，如果数字字面上看起来不像自然数（是小数、负数或表达式），可以证明它不在自然数中
	verRet = ver.litNumNotInNaturalByLiteralShape(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	// 如果在证明 not in Z
	verRet = ver.litNumNotInIntegerByLiteralShape(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	// 如果证明 not in N_pos
	verRet = ver.litNumNotInNPosByLiteralShape(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	return NewExecUnknown("")
}

// TODO 需要先证明一下它是finite set 去开始验证 len(n) = 0
func (ver *Verifier) nothingIsInEmptySet(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	verRet := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{stmt.Params[1], ast.Atom(glob.KeywordFiniteSet)}, stmt.Line), state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	lenOverStmtName := ast.NewFnObj(ast.Atom(glob.KeywordCount), []ast.Obj{stmt.Params[1]})
	equalFact := ast.EqualFact(lenOverStmtName, ast.Atom("0"))
	verRet = ver.VerFactStmt(equalFact, state)
	return verRet
}

func (ver *Verifier) trueExistInSt(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	pureInFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{stmt.Params[1], stmt.Params[2]}, stmt.Line)
	verRet := ver.VerFactStmt(pureInFact, state)
	return verRet
}

// func (ver *Verifier) fcIsFiniteSet(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
// 	// TODO: not sure whether I should add this nextState
// 	nextState := state.GetAddRound()

// 	finiteSetFact := ast.NewInFactWithFc(stmt.Params[0], ast.FcAtom(glob.KeywordFiniteSet))
// 	verRet := ver.VerFactStmt(finiteSetFact, nextState)
// 	return verRet
// }

func (ver *Verifier) objNotInSetWhenAllItemsInThatSetAreNotEqualToIt(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if stmt.TypeEnum != ast.FalsePure {
		return NewExecUnknown("")
	}

	notAllItemsInThatSetAreNotEqualToIt := ast.NewUniFact([]string{"x"}, []ast.Obj{stmt.Params[1]}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{ast.Atom("x"), stmt.Params[0]}, stmt.Line)}, stmt.Line)

	verRet := ver.VerFactStmt(notAllItemsInThatSetAreNotEqualToIt, state)
	return verRet
}

// verInCartSet_ByTuple verifies a $in cart(...) by checking if the tuple's elements are in corresponding cart sets
// func (ver *Verifier) verInCartSet_ByTuple(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
// 	// Check if right side is cart(...)
// 	cartSet, ok := stmt.Params[1].(*ast.FnObj)
// 	if !ok {
// 		return NewExecUnknown("")
// 	}
// 	if !ast.IsAtomObjAndEqualToStr(cartSet.FnHead, glob.KeywordCart) {
// 		return NewExecUnknown("")
// 	}

// 	// Get obj from ObjFromCartSetMem
// 	obj := stmt.Params[0]
// 	item := ver.Env.GetObjFromCartSetMemItem(obj)
// 	if item == nil {
// 		return NewExecUnknown("")
// 	}

// 	// Get EqualTo tuple
// 	tuple := item.EqualToOrNil
// 	if tuple == nil {
// 		return NewExecUnknown("")
// 	}

// 	tupleAsFn, ok := tuple.(*ast.FnObj)
// 	if !ok || !ast.IsTupleFnObj(tupleAsFn) {
// 		return NewExecUnknown("")
// 	}

// 	// Check that tuple length matches cart set length
// 	if len(tupleAsFn.Params) != len(cartSet.Params) {
// 		return NewExecErr(fmt.Sprintf("tuple length (%d) does not match cart set length (%d) in %s", len(tupleAsFn.Params), len(cartSet.Params), stmt))
// 	}

// 	// Check that each element of tuple is in the corresponding cart set
// 	for i := range len(tupleAsFn.Params) {
// 		inFact := ast.NewInFactWithFc(tupleAsFn.Params[i], cartSet.Params[i])
// 		verRet := ver.VerFactStmt(inFact, state)
// 		if verRet.IsErr() {
// 			return verRet
// 		}
// 		if verRet.IsUnknown() {
// 			return NewExecUnknown("")
// 		}
// 	}

// 	msg := fmt.Sprintf("each element in tuple %s is in corresponding cart set %s", tuple, cartSet)
// 	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
// }

func (ver *Verifier) verInSetProduct(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	// left must be (x, y, ...) right must be product(xSet, ySet, ...)
	fcFn, ok := stmt.Params[0].(*ast.FnObj)
	if !ok {
		return NewExecUnknown("")
	}
	// ok = ast.IsAtomObjAndEqualToStr(fcFn.FnHead, glob.TupleFcFnHead)
	// if !ok {
	// 	return NewExecUnknown("")
	// }

	setProductFn, ok := stmt.Params[1].(*ast.FnObj)
	if !ok {
		return NewExecUnknown("")
	}

	if len(fcFn.Params) != len(setProductFn.Params) {
		return NewExecUnknown("")
	}

	for i := range len(fcFn.Params) {
		inFact := ast.NewInFactWithParamFc(fcFn.Params[i], setProductFn.Params[i])
		verRet := ver.VerFactStmt(inFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	msg := fmt.Sprintf("each item in tuple %s is in corresponding set %s", stmt.Params[0], stmt.Params[1])
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
}

// verInCartSet verifies a $in cart(...) by checking:
// 1. dim(a) = dim(cart(...))
// 2. a[i] $in cart(...).Params[i-1] for each i
func (ver *Verifier) verInCartSet(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	// Check if right side is cart(...)
	cartSet, ok := stmt.Params[1].(*ast.FnObj)
	if !ok {
		return NewExecUnknown("")
	}
	if !ast.IsAtomObjAndEqualToStr(cartSet.FnHead, glob.KeywordCart) {
		return NewExecUnknown("")
	}

	obj := stmt.Params[0]

	// Step 1: Verify dim(a) = dim(cart(...))
	// dim(cart(...)) = len(cartSet.Params)
	cartDimValue := len(cartSet.Params)

	ret := ver.VerFactStmt(ast.NewEqualFact(ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{obj}), ast.Atom(strconv.Itoa(cartDimValue))), state)
	if ret.IsErr() {
		return ret
	}
	if ret.IsUnknown() {
		return NewExecUnknown("")
	}

	// Step 2: Verify a[i] $in cartSet.Params[i-1] for each i
	for i := range len(cartSet.Params) {
		index := i + 1 // index starts from 1
		indexObj := ast.Atom(fmt.Sprintf("%d", index))

		// Create indexed object: a[i]
		indexedObj := ast.NewFnObj(ast.Atom(glob.KeywordIndexOpt), []ast.Obj{obj, indexObj})

		// Verify a[i] $in cartSet.Params[i]
		inFact := ast.NewInFactWithFc(indexedObj, cartSet.Params[i])
		verRet := ver.VerFactStmt(inFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return NewExecUnknown("")
		}
	}

	msg := fmt.Sprintf("dim(%s) = %d and each element %s[i] is in corresponding cart set %s", obj, cartDimValue, obj, cartSet)
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
}

func (ver *Verifier) ver_In_FnFcFn_FnTT(left ast.Obj, fnFcFn *ast.FnObj, state *VerState) ExecRet {
	ver.newEnv(ver.Env)
	defer ver.deleteEnv_DeleteMsg()

	// check when parameters satisfy given fnFcFn parameter requirements, then it satisfies the fn template template requirement

	leftIsInWhichFnTT := ver.Env.GetLatestFnT_GivenNameIsIn(left.String())
	if leftIsInWhichFnTT == nil {
		return NewExecUnknown("")
	}

	randomNames := []string{}
	for i := 0; i < len(leftIsInWhichFnTT.AsFnTStruct.Params); i++ {
		randomNames = append(randomNames, ver.Env.GenerateUndeclaredRandomName())
	}
	randomAtoms := []ast.Obj{}
	for i := 0; i < len(leftIsInWhichFnTT.AsFnTStruct.Params); i++ {
		randomAtoms = append(randomAtoms, ast.Atom(randomNames[i]))
	}

	uniMap := map[string]ast.Obj{}
	for i := 0; i < len(leftIsInWhichFnTT.AsFnTStruct.Params); i++ {
		uniMap[leftIsInWhichFnTT.AsFnTStruct.Params[i]] = ast.Atom(randomNames[i])
	}

	// check parameters of the left satisfies the fn template template requirement
	for i, randomName := range randomNames {
		ret := ver.Env.NewObj_NoDuplicate(randomName, nil)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
		ret = ver.Env.NewFact(ast.NewInFactWithParamFc(ast.Atom(randomName), (fnFcFn.FnHead).(*ast.FnObj).Params[i]))
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	leftToUniFact, err := leftIsInWhichFnTT.AsFnTStruct.DeriveUniFact_WithGivenFn(left)
	if err != nil {
		return NewExecErr(err.Error())
	}

	instantiatedLeftToUniFact, err := leftToUniFact.InstantiateFact(uniMap)
	if err != nil {
		return NewExecErr(err.Error())
	}
	instLeftUniFactAsUniFactStmt, ok := instantiatedLeftToUniFact.(*ast.UniFactStmt)
	if !ok {
		return NewExecUnknown("")
	}

	for i := range instLeftUniFactAsUniFactStmt.Params {
		fact := ast.NewInFactWithParamFc(ast.Atom(randomNames[i]), leftIsInWhichFnTT.AsFnTStruct.ParamSets[i])
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		ret := ver.Env.NewFact(fact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	for i := range leftIsInWhichFnTT.AsFnTStruct.DomFacts {
		fact := leftIsInWhichFnTT.AsFnTStruct.DomFacts[i]
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		ret := ver.Env.NewFact(fact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	// whether return value is in ret set of fnFcFn
	fn := ast.NewFnObj(left, randomAtoms)
	verRet := ver.VerFactStmt(ast.NewInFactWithParamFc(fn, fnFcFn.Params[0]), state)
	return verRet
}

func (ver *Verifier) returnValueOfUserDefinedFnInFnReturnSet(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	fcFn, ok := stmt.Params[0].(*ast.FnObj)
	if !ok {
		return NewExecUnknown("")
	}

	if fcFn.HasHeadInSlice([]string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower}) {
		if stmt.Params[1] == ast.Atom(glob.KeywordReal) {
			msg := fmt.Sprintf("return value of builtin arithmetic function %s is in Real", fcFn)
			return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
		}
		return NewExecUnknown("")
	}

	if fcFn.HasHeadInSlice([]string{glob.KeywordCount, glob.KeySymbolPercent}) {
		if stmt.Params[1] == ast.Atom(glob.KeywordNatural) {
			msg := fmt.Sprintf("return value of builtin function %s is in Natural", fcFn)
			return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
		}
		return NewExecUnknown("")
	}

	setFcFnIsIn_ByItsFnT, err := ver.getRetSetOfFcFnByUsingItsFnT(fcFn)
	if err != nil {
		return NewExecUnknown("")
	}

	verRet := ver.VerFactStmt(ast.EqualFact(stmt.Params[1], setFcFnIsIn_ByItsFnT), state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("return value of function %s is in its function template return set %s", fcFn, setFcFnIsIn_ByItsFnT)
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
	}
	return NewExecUnknown("")
}

func (ver *Verifier) getRetSetOfFcFnByUsingItsFnT(fcFn *ast.FnObj) (ast.Obj, error) {
	// f(a)(b,c)(e,d,f) 返回 {f, f(a), f(a)(b,c), f(a)(b,c)(e,d,f)}, {nil, {a}, {b,c}, {e,d,f}}
	fnHeadChain_AndItSelf, _ := ast.GetFnHeadChain_AndItSelf(fcFn)

	// 从后往前找，直到找到有个 fnHead 被已知在一个 fnInFnTInterface 中
	// 比如 f(a)(b,c)(e,d,f) 我不知道 f(a)(b,c) 是哪个 fn_template 里的，但我发现 f(a) $in T 是知道的。那之后就是按T的返回值去套入b,c，然后再把e,d,f套入T的返回值的返回值
	// 此时 indexWhereLatestFnTIsGot 就是 1, FnToFnItemWhereLatestFnTIsGot 就是 f(a) 的 fnInFnTMemItem
	indexWhereLatestFnTIsGot, FnToFnItemWhereLatestFnTIsGot := ver.Env.FindRightMostResolvedFn_Return_ResolvedIndexAndFnTMemItem(fnHeadChain_AndItSelf)

	if FnToFnItemWhereLatestFnTIsGot == nil {
		return nil, fmt.Errorf("no fn template found for %s", fcFn)
	}

	// 比如 f(a)(b,c)(e,d,f) 我们现在得到了 f(a) 的 fnTStruct，那 curParamsChainIndex 就是 2, 表示 f(a) 对应的params就是 (b,c)
	curFnTStruct := (FnToFnItemWhereLatestFnTIsGot.AsFnTStruct)
	curParamsChainIndex := indexWhereLatestFnTIsGot + 1

	// 验证 paramsChain 是否满足 fnTStruct，比如 b,c 是否满足 f(a) 的参数要求
	for curParamsChainIndex < len(fnHeadChain_AndItSelf)-1 {
		curRetSet, ok := curFnTStruct.RetSet.(*ast.FnObj)
		if !ok {
			return nil, fmt.Errorf("curRetSet is not an FcFn")
		}

		var ret glob.GlobRet
		// curFnTStruct, ret = ver.GetFnStructFromFnTName_CheckFnTParamsReq(curRetSet, state)
		curFnTStruct, ret = ver.Env.GetFnStructFromFnTName(curRetSet)
		if ret.IsErr() {
			return nil, fmt.Errorf(ret.String())
		}

		curParamsChainIndex++
	}

	uniMap := map[string]ast.Obj{}
	for i := 0; i < len(curFnTStruct.Params); i++ {
		uniMap[curFnTStruct.Params[i]] = fcFn.Params[i]
	}
	// inst return set
	instRetSet, err := curFnTStruct.RetSet.Instantiate(uniMap)
	if err != nil {
		return nil, fmt.Errorf(err.Error())
	}

	return instRetSet, nil
}

func (ver *Verifier) litNumNotInNaturalByLiteralShape(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	// 检查是否是 not x $in N 的形式
	if !ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNatural) {
		return NewExecUnknown("")
	}

	// 检查字面上是否是自然数形状（必须是 AtomObj 且字面上看起来就是自然数）
	// 如果字面上就是自然数形状（比如 "5"），不能证明它不在自然数中
	if ast.IsFcLiterallyNatNumber(stmt.Params[0]) {
		// 字面上是自然数，不能证明它不在自然数中
		return NewExecUnknown("")
	}

	// 尝试检查是否是数字字面量表达式
	_, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return NewExecErr(err.Error())
	}
	if !ok {
		// 不是数字字面量，返回 unknown
		return NewExecUnknown("")
	}

	// 如果是数字表达式但字面上不是自然数形状（小数、负数或表达式），可以证明它不在自然数中
	msg := fmt.Sprintf("%s is literally not a natural number (not in the shape of natural number)", stmt.Params[0])
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
}

func (ver *Verifier) litNumNotInIntegerByLiteralShape(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	// 检查是否是 not x $in Z 的形式
	if !ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordInteger) {
		return NewExecUnknown("")
	}

	// 检查字面上是否是整数形状（必须是 AtomObj 且字面上看起来就是整数）
	// 如果字面上就是整数形状（比如 "5" 或 "-3"），不能证明它不在整数中
	if ast.IsFcLiterallyIntNumber(stmt.Params[0]) {
		// 字面上是整数，不能证明它不在整数中
		return NewExecUnknown("")
	}

	// 尝试检查是否是数字字面量表达式
	_, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return NewExecErr(err.Error())
	}
	if !ok {
		// 不是数字字面量，返回 unknown
		return NewExecUnknown("")
	}

	// 如果是数字表达式但字面上不是整数形状（小数或表达式），可以证明它不在整数中
	msg := fmt.Sprintf("%s is literally not an integer (not in the shape of integer)", stmt.Params[0])
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
}

func (ver *Verifier) litNumNotInNPosByLiteralShape(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	// 检查是否是 not x $in N_pos 的形式
	if !ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNPos) {
		return NewExecUnknown("")
	}

	// 检查字面上是否是正整数形状（必须是 AtomObj 且字面上看起来就是正整数）
	// 如果字面上就是正整数形状（比如 "5"），不能证明它不在正整数中
	if ast.IsFcLiterallyNPosNumber(stmt.Params[0]) {
		// 字面上是正整数，不能证明它不在正整数中
		return NewExecUnknown("")
	}

	// 尝试检查是否是数字字面量表达式
	_, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return NewExecErr(err.Error())
	}
	if !ok {
		// 不是数字字面量，返回 unknown
		return NewExecUnknown("")
	}

	// 如果是数字表达式但字面上不是正整数形状（小数、负数、0或表达式），可以证明它不在正整数中
	msg := fmt.Sprintf("%s is literally not a positive integer (not in the shape of positive integer)", stmt.Params[0])
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
}
