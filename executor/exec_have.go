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

func (exec *Executor) haveObjStStmt(stmt *ast.HaveObjStStmt, requireMsg bool) ExecRet {
	defer func() {
		if requireMsg {
			exec.newMsg(fmt.Sprintf("%s\n", stmt))
		}
	}()

	if string(stmt.Fact.PropName) == glob.KeywordExistPropPreImageByReplacement {
		execState, err := exec.haveExistByReplacementStmt(stmt)
		if err != nil {
			return NewExecErr(err.Error())
		}
		if execState.IsNotTrue() {
			return execState
		}
		return NewExecTrue("")
	}

	// 检查 SpecFactStmt 是否满足了
	execState, err := exec.openANewEnvAndCheck(stmt.Fact, false)

	if err != nil {
		return NewExecErr(err.Error())
	}

	if stmt.Fact.PropName == glob.KeywordItemExistsIn && execState.IsUnknown() {
		ok, err := exec.checkInFactInSet_SetIsNonEmpty(stmt.Fact)
		if err != nil {
			return NewExecErr(err.Error())
		}
		if ok {
			execState = NewExecTrue("")
		}
	}

	if execState.IsNotTrue() {
		exec.newMsg(fmt.Sprintf("%s is unknown", stmt.Fact.String()))
		return execState
	}

	if stmt.Fact.PropName == glob.KeywordItemExistsIn && execState.IsTrue() {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.ObjNames[0]}, []ast.Obj{stmt.Fact.Params[0]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState
		}
		return NewExecTrue("")
	}

	// TODO： have 可能会引入3种不同的东西：set,obj,fn都可能；每种情况，处理起来不一样：比如如果你是fn和set，那可能就要把你放到 setMem 和 fnMem 里了
	// 这个 warning 不合时宜了，因为fn的定义其实和obj一样了，就是额外多个满足特定的template

	// TODO 把 exist prop def 里的东西释放出来
	existPropDef := exec.Env.GetExistPropDef(stmt.Fact.PropName)
	if existPropDef == nil {
		return NewExecUnknown("")
	}

	if len(existPropDef.ExistParams) != len(stmt.ObjNames) {
		return NewExecErr(fmt.Sprintf("exist prop def params number not equal to have stmt obj names number. expect %d, but got %d", len(existPropDef.ExistParams), len(stmt.ObjNames)))
	}

	uniMap := map[string]ast.Obj{}
	ExistParamsAtoms := []ast.Obj{}
	for i, param := range existPropDef.ExistParams {
		paramAsAtom := ast.FcAtom(stmt.ObjNames[i])
		uniMap[param] = paramAsAtom
		ExistParamsAtoms = append(ExistParamsAtoms, paramAsAtom)
	}

	for i, param := range existPropDef.DefBody.DefHeader.Params {
		uniMap[param] = stmt.Fact.Params[i]
	}

	instantiatedExistPropDefStmt, err := existPropDef.Instantiate(uniMap)
	if err != nil {
		return NewExecErr(err.Error())
	}

	// 把 obj 放入环境
	for i, objName := range stmt.ObjNames {
		stmtForDef := ast.NewDefLetStmt([]string{objName}, []ast.Obj{instantiatedExistPropDefStmt.(*ast.DefExistPropStmt).ExistParamSets[i]}, []ast.FactStmt{}, stmt.Line)
		err := exec.Env.DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(stmtForDef)
		if err != nil {
			return NewExecErr(err.Error())
		}
		execState := NewExecTrue(stmtForDef.String())
		if execState.IsNotTrue() {
			return execState
		}
	}

	// param in param sets is true
	// for _, paramInParamSet := range instantiatedExistPropDefStmt.ExistParamInSetsFacts() {
	// 	err := exec.env.NewFact(paramInParamSet)
	// 	if err != nil {
	// 		return glob.ExecState_Error, err
	// 	}
	// }

	for i, existParamSet := range instantiatedExistPropDefStmt.(*ast.DefExistPropStmt).ExistParamSets {
		err := exec.Env.NewFact(ast.NewInFact(stmt.ObjNames[i], existParamSet))
		if err != nil {
			return NewExecErr(err.Error())
		}
	}

	// dom of def exist prop is true
	for _, domFact := range instantiatedExistPropDefStmt.(*ast.DefExistPropStmt).DefBody.DomFacts {
		err := exec.Env.NewFact(domFact)
		if err != nil {
			return NewExecErr(err.Error())
		}
		exec.newMsg(fmt.Sprintf("%s\nis true by definition", domFact))
	}

	// iff of def exist prop is true
	for _, iffFact := range instantiatedExistPropDefStmt.(*ast.DefExistPropStmt).DefBody.IffFacts {
		err := exec.Env.NewFact(iffFact)
		if err != nil {
			return NewExecErr(err.Error())
		}
		exec.newMsg(fmt.Sprintf("%s\nis true by definition", iffFact))
	}

	// 相关的 exist st 事实也成立
	existStFactParams := ast.MakeExistFactParamsSlice(ExistParamsAtoms, stmt.Fact.Params)

	newExistStFact := ast.NewSpecFactStmt(ast.TrueExist_St, ast.FcAtom(string(stmt.Fact.PropName)), existStFactParams, stmt.Line)
	err = exec.Env.NewFact(newExistStFact)
	if err != nil {
		return NewExecErr(err.Error())
	}
	exec.newMsg(fmt.Sprintf("%s\nis true by definition", newExistStFact))

	return NewExecTrue("")
}

func (exec *Executor) haveObjInNonEmptySetStmt(stmt *ast.HaveObjInNonEmptySetStmt) ExecRet {
	for i := range len(stmt.Objs) {
		existInFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordItemExistsIn), []ast.Obj{stmt.ObjSets[i]}, stmt.Line)
		haveStmt := ast.NewHaveStmt([]string{stmt.Objs[i]}, existInFact, stmt.Line)
		execState := exec.haveObjStStmt(haveStmt, false)
		if execState.IsNotTrue() {
			return execState
		}
	}

	return NewExecTrue("").AddMsg(fmt.Sprintf("%s\n", stmt))
}

func (exec *Executor) checkInFactInSet_SetIsNonEmpty(pureInFact *ast.SpecFactStmt) (bool, error) {
	if _, ok := glob.BuiltinObjKeywordSet[pureInFact.Params[0].String()]; ok {
		return true, nil
	}

	isFiniteSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Obj{pureInFact.Params[0], ast.FcAtom(glob.KeywordFiniteSet)}, pureInFact.Line)
	ok, err := exec.openANewEnvAndCheck(isFiniteSetFact, false)
	if err != nil {
		return false, err
	}
	if ok.IsTrue() {
		// 如果 len > 0 那就是可以
		lenOverStmtName := ast.NewFcFn(ast.FcAtom(glob.KeywordLen), []ast.Obj{pureInFact.Params[0]})
		largerThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolGreater), []ast.Obj{lenOverStmtName, ast.FcAtom("0")}, pureInFact.Line)
		ok, err := exec.openANewEnvAndCheck(largerThanZeroFact, false)
		if err != nil {
			return false, err
		}
		if ok.IsTrue() {
			return true, nil
		}
	}

	return false, nil
}

func (exec *Executor) haveEnumSetStmt(stmt *ast.HaveEnumSetStmt) ExecRet {
	exec.newMsg(stmt.String())

	enumFact := stmt.Fact

	// 验证里面的各个元素不相等
	for i := range len(enumFact.Items) {
		for j := i + 1; j < len(enumFact.Items); j++ {
			notEqualFact := ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Obj{enumFact.Items[i], enumFact.Items[j]}, stmt.Line)
			ok, err := exec.openANewEnvAndCheck(notEqualFact, false)
			if err != nil {
				return NewExecErr(err.Error())
			}
			if ok.IsUnknown() {
				return NewExecErr("enumeration set items must be distinct, but " + notEqualFact.String() + " is unknown")
			}
		}
	}

	// 定义这个新的集合
	defObjStmt := ast.NewDefLetStmt([]string{enumFact.CurSet.String()}, []ast.Obj{ast.FcAtom(glob.KeywordSet)}, []ast.FactStmt{enumFact}, stmt.Line)
	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	return NewExecTrue("")
}

func (exec *Executor) haveIntensionalSetStmt(stmt *ast.HaveIntensionalSetStmt) ExecRet {
	exec.newMsg(stmt.String())

	intensionalSetFact := stmt.Fact

	// very important: check whether the parent set is a set
	state := exec.factStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Obj{intensionalSetFact.ParentSet, ast.FcAtom(glob.KeywordSet)}, stmt.Line))
	if state.IsErr() {
		return NewExecErr(state.String())
	}
	if state.IsUnknown() {
		return NewExecErr("parent set of intensional set must be a set, i.e. `" + intensionalSetFact.ParentSet.String() + " in " + ast.FcAtom(glob.KeywordSet).String() + "` is true, but `" + intensionalSetFact.ParentSet.String() + " in " + ast.FcAtom(glob.KeywordSet).String() + "` is not")
	}

	defObjStmt := ast.NewDefLetStmt([]string{intensionalSetFact.CurSet.String()}, []ast.Obj{ast.FcAtom(glob.KeywordSet)}, []ast.FactStmt{intensionalSetFact}, stmt.Line)
	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	return NewExecTrue("")
}

func (exec *Executor) haveExistByReplacementStmt(stmt *ast.HaveObjStStmt) (ExecRet, error) {
	if len(stmt.Fact.Params) != 4 {
		return NewExecErr(""), fmt.Errorf("set defined by replacement must have 3 parameters, but %s has %d", stmt.Fact.String(), len(stmt.Fact.Params))
	}

	propName, ok := stmt.Fact.Params[2].(ast.FcAtom)
	if !ok {
		return NewExecErr(""), fmt.Errorf("third parameter of set defined by replacement must be a prop name, but %s is not", stmt.Fact.String())
	}

	uniFact := ast.GetForallXOnlyOneYSatisfyGivenProp(stmt.Fact.Params[0], stmt.Fact.Params[1], propName)

	execState := exec.factStmt(uniFact)
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	fourthObjInSetDefinedByReplacement := ast.NewInFactWithFc(stmt.Fact.Params[3], ast.NewFcFn(ast.FcAtom(glob.KeywordSetDefinedByReplacement), []ast.Obj{stmt.Fact.Params[0], stmt.Fact.Params[1], propName}))
	execState = exec.factStmt(fourthObjInSetDefinedByReplacement)
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	defObjStmt := ast.NewDefLetStmt([]string{stmt.ObjNames[0]}, []ast.Obj{stmt.Fact.Params[0]}, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, propName, []ast.Obj{ast.FcAtom(stmt.ObjNames[0]), stmt.Fact.Params[3]}, stmt.Line)}, stmt.Line)
	execState = exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	return NewExecTrue(""), nil
}
