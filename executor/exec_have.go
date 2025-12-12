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
	// 检查 SpecFactStmt 是否满足了
	execState := exec.Verify(stmt.Fact, false)
	if execState.IsNotTrue() {
		return execState
	}

	if execState.IsNotTrue() {
		return execState
	}

	// TODO： have 可能会引入3种不同的东西：set,obj,fn都可能；每种情况，处理起来不一样：比如如果你是fn和set，那可能就要把你放到 setMem 和 fnMem 里了
	// 这个 warning 不合时宜了，因为fn的定义其实和obj一样了，就是额外多个满足特定的template

	// TODO 把 exist prop def 里的东西释放出来
	existPropDef := exec.Env.GetExistPropDef(stmt.Fact.PropName)
	if existPropDef == nil {
		return NewEmptyExecUnknown()
	}

	if len(existPropDef.ExistParams) != len(stmt.ObjNames) {
		return NewExecErr(fmt.Sprintf("exist prop def params number not equal to have stmt obj names number. expect %d, but got %d", len(existPropDef.ExistParams), len(stmt.ObjNames)))
	}

	uniMap := map[string]ast.Obj{}
	ExistParamsAtoms := []ast.Obj{}
	for i, param := range existPropDef.ExistParams {
		paramAsAtom := ast.Atom(stmt.ObjNames[i])
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
		ret := exec.Env.DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(stmtForDef)
		if ret.IsErr() {
			return NewExecErr(ret.String())
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
		ret := exec.Env.NewFact(ast.NewInFact(stmt.ObjNames[i], existParamSet))
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	// dom of def exist prop is true
	for _, domFact := range instantiatedExistPropDefStmt.(*ast.DefExistPropStmt).DefBody.DomFacts {
		ret := exec.Env.NewFact(domFact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	// iff of def exist prop is true
	for _, iffFact := range instantiatedExistPropDefStmt.(*ast.DefExistPropStmt).DefBody.IffFacts {
		ret := exec.Env.NewFact(iffFact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	// 相关的 exist st 事实也成立
	existStFactParams := ast.MakeExistFactParamsSlice(ExistParamsAtoms, stmt.Fact.Params)

	newExistStFact := ast.NewSpecFactStmt(ast.TrueExist_St, ast.Atom(string(stmt.Fact.PropName)), existStFactParams, stmt.Line)
	ret := exec.Env.NewFact(newExistStFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	result := NewEmptyExecTrue()
	if requireMsg {
		result = result.AddMsg(fmt.Sprintf("%s\n", stmt))
	}
	// Note: Messages about "is true by definition" are now handled in the verifier
	return result
}

func (exec *Executor) haveObjInNonEmptySetStmt(stmt *ast.HaveObjInNonEmptySetStmt) ExecRet {
	for i := range len(stmt.Objs) {
		if !glob.IsKeywordSetOrNonEmptySetOrFiniteSet(stmt.ObjSets[i].String()) {
			existInFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsANonEmptySet), []ast.Obj{stmt.ObjSets[i]}, stmt.Line)
			execState := exec.factStmt(existInFact)
			if execState.IsNotTrue() {
				return NewExecErr(fmt.Sprintf("%s\n", stmt.String())).AddMsg(execState.String())
			}
		}

		stmtForDef := ast.NewDefLetStmt([]string{stmt.Objs[i]}, []ast.Obj{stmt.ObjSets[i]}, []ast.FactStmt{}, stmt.Line)
		ret := exec.Env.DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(stmtForDef)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
		execState := NewExecTrue(stmtForDef.String())
		if execState.IsNotTrue() {
			return NewExecErr(fmt.Sprintf("%s\n", stmt.String())).AddMsg(execState.String())
		}
	}

	return NewEmptyExecTrue().AddMsg(fmt.Sprintf("%s\n", stmt))
}

// func (exec *Executor) checkInFactInSet_SetIsNonEmpty(pureInFact *ast.SpecFactStmt) (bool, error) {
// 	if _, ok := glob.BuiltinObjKeywordSet[pureInFact.Params[0].String()]; ok {
// 		return true, nil
// 	}

// 	isFiniteSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{pureInFact.Params[0], ast.Atom(glob.KeywordFiniteSet)}, pureInFact.Line)
// 	execRet := exec.Verify(isFiniteSetFact, false)
// 	if execRet.IsNotTrue() {
// 		return false, fmt.Errorf(execRet.String())
// 	}
// 	if execRet.IsTrue() {
// 		// 如果 len > 0 那就是可以
// 		lenOverStmtName := ast.NewFnObj(ast.Atom(glob.KeywordCount), []ast.Obj{pureInFact.Params[0]})
// 		largerThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{lenOverStmtName, ast.Atom("0")}, pureInFact.Line)
// 		execRet := exec.Verify(largerThanZeroFact, false)
// 		if execRet.IsNotTrue() {
// 			return false, fmt.Errorf(execRet.String())
// 		}
// 		if execRet.IsTrue() {
// 			return true, nil
// 		}
// 	}

// 	return false, nil
// }

func (exec *Executor) haveCartSetStmt(stmt *ast.HaveCartSetStmt) ExecRet {
	// check that the cart has at least 2 parameters
	if len(stmt.CartObj.Params) < 2 {
		return NewExecErr(fmt.Sprintf("cart must have at least 2 parameters, %s in %s is not valid", stmt.CartObj.String(), stmt.CartObj.String()))
	}

	// Check that each parameter of cart is a set
	for i, param := range stmt.CartObj.Params {
		state := exec.factStmt(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{param, ast.Atom(glob.KeywordSet)}, stmt.Line))
		if state.IsErr() {
			return NewExecErr(state.String())
		}
		if state.IsUnknown() {
			return NewExecErr(fmt.Sprintf("cart parameter %d (%s) must be a set, i.e. `%s in %s` must be true, but it is unknown", i+1, param.String(), param.String(), ast.Atom(glob.KeywordSet).String()))
		}
	}

	// Define the new set variable
	defObjStmt := ast.NewDefLetStmt([]string{stmt.Name}, []ast.Obj{ast.Atom(glob.KeywordSet)}, []ast.FactStmt{}, stmt.Line)
	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	// Store the equal fact: x = cart(a, b, c, ...)
	equalFact := ast.NewEqualFact(ast.Atom(stmt.Name), stmt.CartObj)
	ret := exec.Env.NewFact(equalFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewEmptyExecTrue().AddMsg(stmt.String())
}
