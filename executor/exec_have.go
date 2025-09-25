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
	verifier "golitex/verifier"
)

func (exec *Executor) haveObjStStmt(stmt *ast.HaveObjStStmt, requireMsg bool) (glob.ExecState, error) {
	defer func() {
		if glob.RequireMsg() && requireMsg {
			exec.newMsg(fmt.Sprintf("%s\n", stmt))
		}
	}()

	if string(stmt.Fact.PropName) == glob.KeywordExistPropPreImageByReplacement {
		execState, err := exec.haveExistByReplacementStmt(stmt)
		if notOkExec(execState, err) {
			return execState, err
		}
		return glob.ExecState_True, nil
	}

	// 检查 SpecFactStmt 是否满足了
	execState, err := exec.openANewEnvAndCheck(&stmt.Fact, false)

	if stmt.Fact.PropName == glob.KeywordExistIn && execState != glob.ExecState_True && err == nil {
		ok, err := exec.checkInFactInSet_SetIsNonEmpty(&stmt.Fact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if ok {
			execState = glob.ExecState_True
		}
	}

	if notOkExec(execState, err) {
		if glob.RequireMsg() {
			exec.newMsg(fmt.Sprintf("%s is unknown", stmt.Fact.String()))
		}
		return execState, err
	}

	if stmt.Fact.PropName == glob.KeywordExistIn && execState == glob.ExecState_True {
		err := exec.defObjStmt(ast.NewDefObjStmt([]string{stmt.ObjNames[0]}, []ast.Fc{stmt.Fact.Params[0]}, []ast.FactStmt{}, stmt.Line), false)
		if err != nil {
			return glob.ExecState_Error, err
		}
		return glob.ExecState_True, nil
	}

	// TODO： have 可能会引入3种不同的东西：set,obj,fn都可能；每种情况，处理起来不一样：比如如果你是fn和set，那可能就要把你放到 setMem 和 fnMem 里了
	// 这个 warning 不合时宜了，因为fn的定义其实和obj一样了，就是额外多个满足特定的template

	// TODO 把 exist prop def 里的东西释放出来
	existPropDef, ok := exec.env.GetExistPropDef(stmt.Fact.PropName)
	if !ok {
		return glob.ExecState_Unknown, nil
	}

	if len(existPropDef.ExistParams) != len(stmt.ObjNames) {
		return glob.ExecState_Error, fmt.Errorf("exist prop def params number not equal to have stmt obj names number. expect %d, but got %d", len(existPropDef.ExistParams), len(stmt.ObjNames))
	}

	uniMap := map[string]ast.Fc{}
	ExistParamsAtoms := []ast.Fc{}
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
		return glob.ExecState_Error, err
	}

	ver := verifier.NewVerifier(exec.env)

	// 把 obj 放入环境
	for i, objName := range stmt.ObjNames {
		err := ver.NewDefObj_InsideAtomsDeclared(ast.NewDefObjStmt([]string{objName}, []ast.Fc{instantiatedExistPropDefStmt.ExistParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// param in param sets is true
	// for _, paramInParamSet := range instantiatedExistPropDefStmt.ExistParamInSetsFacts() {
	// 	err := exec.env.NewFact(paramInParamSet)
	// 	if err != nil {
	// 		return glob.ExecState_Error, err
	// 	}
	// }

	for i, existParamSet := range instantiatedExistPropDefStmt.ExistParamSets {
		err := exec.env.NewFact(ast.NewInFact(stmt.ObjNames[i], existParamSet))
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// dom of def exist prop is true
	for _, domFact := range instantiatedExistPropDefStmt.DefBody.DomFacts {
		err := exec.env.NewFact(domFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if glob.RequireMsg() {
			exec.newMsg(fmt.Sprintf("%s\nis true by definition", domFact))
		}
	}

	// iff of def exist prop is true
	for _, iffFact := range instantiatedExistPropDefStmt.DefBody.IffFacts {
		err := exec.env.NewFact(iffFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if glob.RequireMsg() {
			exec.newMsg(fmt.Sprintf("%s\nis true by definition", iffFact))
		}
	}

	// 相关的 exist st 事实也成立
	existStFactParams := ast.MakeExistFactParamsSlice(ExistParamsAtoms, stmt.Fact.Params)

	newExistStFact := ast.NewSpecFactStmt(ast.TrueExist_St, ast.FcAtom(string(stmt.Fact.PropName)), existStFactParams)
	err = exec.env.NewFact(newExistStFact)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if glob.RequireMsg() {
		exec.newMsg(fmt.Sprintf("%s\nis true by definition", newExistStFact))
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) haveObjInNonEmptySetStmt(stmt *ast.HaveObjInNonEmptySetStmt) (glob.ExecState, error) {
	failed := true
	defer func() {
		if glob.RequireMsg() && !failed {
			exec.newMsg(fmt.Sprintf("%s\n", stmt))
		}
	}()

	for i := range len(stmt.Objs) {
		existInFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordExistIn), []ast.Fc{stmt.ObjSets[i]})
		haveStmt := ast.NewHaveStmt([]string{stmt.Objs[i]}, *existInFact)
		execState, err := exec.haveObjStStmt(haveStmt, false)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	failed = false

	return glob.ExecState_True, nil
}

func (exec *Executor) checkInFactInSet_SetIsNonEmpty(pureInFact *ast.SpecFactStmt) (bool, error) {
	if _, ok := glob.BuiltinObjKeywordSet[pureInFact.Params[0].String()]; ok {
		return true, nil
	}

	isFiniteSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{pureInFact.Params[0], ast.FcAtom(glob.KeywordFiniteSet)})
	ok, err := exec.openANewEnvAndCheck(isFiniteSetFact, false)
	if err != nil {
		return false, err
	}
	if ok == glob.ExecState_True {
		// 如果 len > 0 那就是可以
		lenOverStmtName := ast.NewFcFn(ast.FcAtom(glob.KeywordLen), []ast.Fc{pureInFact.Params[0]})
		largerThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolGreater), []ast.Fc{lenOverStmtName, ast.FcAtom("0")})
		ok, err := exec.openANewEnvAndCheck(largerThanZeroFact, false)
		if err != nil {
			return false, err
		}
		if ok == glob.ExecState_True {
			return true, nil
		}
	}

	return false, nil
}

func (exec *Executor) haveSetStmt(stmt *ast.HaveSetStmt) (glob.ExecState, error) {
	exec.newMsg(stmt.String())
	switch asStmt := stmt.Fact.(type) {
	case *ast.EnumStmt:
		return exec.haveEnumSetStmt(asStmt)
	case *ast.IntensionalSetStmt:
		return exec.haveIntensionalSetStmt(asStmt)
	}

	return glob.ExecState_Error, fmt.Errorf("unknown set statement type: %T", stmt.Fact)
}

func (exec *Executor) haveEnumSetStmt(stmt *ast.EnumStmt) (glob.ExecState, error) {
	// 验证里面的各个元素不相等
	for i := range len(stmt.Items) {
		for j := i + 1; j < len(stmt.Items); j++ {
			notEqualFact := ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{stmt.Items[i], stmt.Items[j]})
			ok, err := exec.openANewEnvAndCheck(notEqualFact, false)
			if err != nil {
				return glob.ExecState_Error, err
			}
			if ok != glob.ExecState_True {
				return glob.ExecState_Error, fmt.Errorf("enumeration set items must be distinct, but %s is unknown", notEqualFact)
			}
		}
	}

	// 定义这个新的集合
	defObjStmt := ast.NewDefObjStmt([]string{stmt.CurSet.String()}, []ast.Fc{ast.FcAtom(glob.KeywordSet)}, []ast.FactStmt{stmt}, stmt.Line)
	err := exec.defObjStmt(defObjStmt, false)
	if err != nil {
		return glob.ExecState_Error, err
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) haveIntensionalSetStmt(stmt *ast.IntensionalSetStmt) (glob.ExecState, error) {
	// very important: check whether the parent set is a set
	ok, err := exec.factStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.ParentSet, ast.FcAtom(glob.KeywordSet)}))
	if err != nil {
		return glob.ExecState_Error, err
	}
	if ok != glob.ExecState_True {
		return glob.ExecState_Error, fmt.Errorf("parent set of intensional set must be a set, i.e. `%s in %s` is true, but `%s in %s` is not", stmt.ParentSet, ast.FcAtom(glob.KeywordSet), stmt.ParentSet, ast.FcAtom(glob.KeywordSet))
	}

	defObjStmt := ast.NewDefObjStmt([]string{stmt.CurSet.String()}, []ast.Fc{ast.FcAtom(glob.KeywordSet)}, []ast.FactStmt{stmt}, stmt.Line)
	err = exec.defObjStmt(defObjStmt, false)
	if err != nil {
		return glob.ExecState_Error, err
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) haveExistByReplacementStmt(stmt *ast.HaveObjStStmt) (glob.ExecState, error) {
	if len(stmt.Fact.Params) != 4 {
		return glob.ExecState_Error, fmt.Errorf("set defined by replacement must have 3 parameters, but %s has %d", stmt.Fact.String(), len(stmt.Fact.Params))
	}

	propName, ok := stmt.Fact.Params[2].(ast.FcAtom)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("third parameter of set defined by replacement must be a prop name, but %s is not", stmt.Fact.String())
	}

	uniFact := ast.GetForallXOnlyOneYSatisfyGivenProp(stmt.Fact.Params[0], stmt.Fact.Params[1], propName)

	execState, err := exec.factStmt(uniFact)
	if notOkExec(execState, err) {
		return execState, err
	}

	fourthObjInSetDefinedByReplacement := ast.NewInFactWithFc(stmt.Fact.Params[3], ast.NewFcFn(ast.FcAtom(glob.KeywordSetDefinedByReplacement), []ast.Fc{stmt.Fact.Params[0], stmt.Fact.Params[1], propName}))
	execState, err = exec.factStmt(fourthObjInSetDefinedByReplacement)
	if notOkExec(execState, err) {
		return execState, err
	}

	defObjStmt := ast.NewDefObjStmt([]string{stmt.ObjNames[0]}, []ast.Fc{stmt.Fact.Params[0]}, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, propName, []ast.Fc{ast.FcAtom(stmt.ObjNames[0]), stmt.Fact.Params[3]})}, stmt.Line)
	err = exec.defObjStmt(defObjStmt, false)
	if err != nil {
		return glob.ExecState_Error, err
	}

	return glob.ExecState_True, nil
}
