// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	verifier "golitex/verifier"
	"strings"
)

func (exec *Executor) stmt(stmt ast.Stmt) (glob.ExecState, error) {
	var err error = nil
	var execState glob.ExecState = glob.ExecState_True

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		execState, err = exec.factStmt(stmt)
	case *ast.KnowFactStmt:
		err = exec.knowFactStmt(stmt)
	case *ast.ClaimStmt:
		execState, err = exec.claimStmt(stmt)
	case *ast.DefPropStmt:
		err = exec.defPropStmt(stmt)
	case *ast.DefObjStmt:
		err = exec.defObjStmt(stmt)
	case *ast.HaveStmt:
		execState, err = exec.haveStmt(stmt)
	case *ast.DefExistPropStmt:
		err = exec.defExistPropStmt(stmt)
	case *ast.DefFnStmt:
		err = exec.defFnStmt(stmt)
	case *ast.KnowPropStmt:
		err = exec.knowPropStmt(stmt)
	case *ast.KnowExistPropStmt:
		_, err = exec.knowExistPropStmt(stmt)
	case *ast.SetDefSetBuilderStmt:
		err = exec.setDefStmt(stmt)
	case *ast.ProveInEachCaseStmt:
		execState, err = exec.proveInEachCaseStmt(stmt)
	case *ast.SupposeStmt:
		execState, err = exec.supposePropMatchStmt(stmt)
	case *ast.WithPropMatchStmt:
		execState, err = exec.withPropMatchStmt(stmt)
	case *ast.KnowSupposeStmt:
		execState, err = exec.knowSupposeStmt(stmt)

	default:
		err = fmt.Errorf("unknown statement type: %T", stmt)
	}

	if err != nil {
		return glob.ExecState_Error, glob.NewErrLink(err, "%s\nexecution error", stmt.String())
	} else {
		return execState, nil
	}
}

func (exec *Executor) TopLevelStmt(stmt *ast.TopStmt) (glob.ExecState, error) {
	exec.clearMsgAndOutput()
	return exec.stmt(stmt.Stmt)
}

func (exec *Executor) factStmt(stmt ast.FactStmt) (glob.ExecState, error) {
	defer exec.appendMsg("\n")

	curVerifier := verifier.NewVerifier(exec.env)
	ok, err := curVerifier.FactStmt(stmt, verifier.Round0Msg)
	if err != nil {
		return glob.ExecState_Error, err
	}

	if ok {
		err := exec.env.NewFact(stmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		return glob.ExecState_True, nil
	}

	if glob.CheckFalse {
		if asSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
			reversedFact := asSpecFact.ReverseTrue()
			curVerifier := verifier.NewVerifier(exec.env)
			ok, err := curVerifier.FactStmt(reversedFact, verifier.Round0Msg)
			if err != nil {
				return glob.ExecState_Error, err
			}
			if ok {
				exec.appendMsg(asSpecFact.String() + "\nis false")
				return glob.ExecState_False, nil
			} else {
				exec.appendMsg(stmt.String() + "\nis unknown")
			}
		} else {
			exec.appendMsg(stmt.String() + "\nis unknown")
		}
	} else {
		exec.appendMsg(stmt.String() + "\nis unknown")
	}

	return glob.ExecState_Unknown, nil
}

// TODO: 再know时就检查，仅仅依赖写在dom里的事实，是否真的能让涉及到的函数和prop能真的满足条件。如果不满足条件，那就warning
func (exec *Executor) knowFactStmt(stmt *ast.KnowFactStmt) error {
	defer exec.appendMsg("\n")

	for _, fact := range stmt.Facts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	exec.appendMsg(stmt.String())
	return nil
}

func (exec *Executor) claimStmt(stmt *ast.ClaimStmt) (glob.ExecState, error) {
	isSuccess := false
	var err error = nil

	if stmt.IsProve {
		isSuccess, err = exec.claimStmtProve(stmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
	} else {
		isSuccess, err = exec.claimStmtProveByContradiction(stmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	if !isSuccess {
		return glob.ExecState_Unknown, nil
	}

	if asSpecFact, ok := stmt.ToCheckFact.(*ast.SpecFactStmt); ok {
		err = exec.env.Parent.NewFact(asSpecFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	} else if asUniFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt); ok {
		// newUniFact, err := ast.AddUniPrefixToUniFact(asUniFact)

		// if err != nil {
		// 	return glob.ExecState_Error, err
		// }

		newUniFact := asUniFact

		err = exec.env.Parent.NewFact(newUniFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}
	return glob.ExecState_True, nil
}

func (exec *Executor) GetMsgAsStr0ToEnd() string {
	return strings.Join(exec.env.Msgs, "\n")
}

func (exec *Executor) defPropStmt(stmt *ast.DefPropStmt) error {
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	err := exec.env.NewDefProp(stmt)
	if err != nil {
		return err
	}

	// prop leads to iff
	if stmt.IffFacts == nil || len(stmt.IffFacts) == 0 {
		return nil
	}

	propToIff, iffToProp, err := stmt.Make_PropToIff_IffToProp()
	if err != nil {
		return err
	}

	err = exec.env.NewFact(propToIff)

	exec.appendMsg(fmt.Sprintf("%s\nis true by definition", propToIff.String()))

	if err != nil {
		return err
	}

	err = exec.env.NewFact(iffToProp)
	if err != nil {
		return err
	}

	exec.appendMsg(fmt.Sprintf("%s\nis true by definition", iffToProp.String()))

	if len(stmt.IffFacts) == 0 {
		return nil
	}

	return nil
}

func (exec *Executor) defObjStmt(stmt *ast.DefObjStmt) error {
	defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
	err := exec.env.NewDefObj(stmt)
	if err != nil {
		return err
	}

	for i := range stmt.ParamInSetsFacts {
		err := exec.env.NewFact(stmt.ParamInSetsFacts[i])
		if err != nil {
			return err
		}
	}

	for _, fact := range stmt.Facts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	return nil
}

func (exec *Executor) defFnStmt(stmt *ast.DefFnStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())
	err := exec.env.NewDefFn(stmt)
	if err != nil {
		return err
	}

	// the function object is in fn
	retSet, err := ast.GetParamSetFromInStmt(stmt.RetInSetsFact)
	if err != nil {
		return err
	}

	paramSets := []ast.Fc{}
	for _, paramInSet := range stmt.DefHeader.ParamInSetsFacts {
		paramSet, err := ast.GetParamSetFromInStmt(paramInSet)
		if err != nil {
			return err
		}
		paramSets = append(paramSets, paramSet)
	}

	fnSet := ast.MakeFnSetFc(paramSets, retSet)

	inFact := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{ast.NewFcAtomWithName(stmt.DefHeader.Name), fnSet})
	err = exec.env.NewFact(inFact)
	if err != nil {
		return err
	}

	uniFactThen := []ast.FactStmt{stmt.RetInSetsFact}
	uniFactThen = append(uniFactThen, stmt.ThenFacts...)

	thenFacts := []ast.FactStmt{}
	thenFacts = append(thenFacts, uniFactThen...)

	uniFact := ast.NewUniFactStmtWithSetReqInDom(stmt.DefHeader.Params, []ast.Fc{}, stmt.DomFacts, thenFacts, ast.EmptyIffFacts, []ast.FactStmt{})
	err = exec.env.NewFact(uniFact)

	if err != nil {
		return err
	}

	// 现在只处理dom里没额外的东西的情况
	if len(stmt.DomFacts) == 0 {
		setParams, err := ast.GetParamsSetFromInStatements(stmt.DefHeader.ParamInSetsFacts)
		if err != nil {
			return err
		}
		fnInFnSet, err := ast.GetParamSetFromInStmt(stmt.RetInSetsFact)
		if err != nil {
			return err
		}
		fnSet := ast.NewFcFn(ast.NewFcFn(ast.NewFcAtomWithName(glob.KeywordFn), setParams), []ast.Fc{fnInFnSet})

		newFact := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{ast.NewFcAtomWithName(stmt.DefHeader.Name), fnSet})

		err = exec.env.NewFact(newFact)
		if err != nil {
			return err
		}
	}

	return nil
}

func (exec *Executor) defExistPropStmt(stmt *ast.DefExistPropStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())
	err := exec.env.NewDefExistProp(stmt)
	if err != nil {
		return err
	}
	return nil
}

func (exec *Executor) haveStmt(stmt *ast.HaveStmt) (glob.ExecState, error) {
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	// 检查 SpecFactStmt 是否满足了
	execState, err := exec.factStmt(&stmt.Fact)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if execState != glob.ExecState_True {
		exec.appendMsg(fmt.Sprintf("%s is unknown", stmt.Fact.String()))
		return glob.ExecState_Unknown, nil
	}

	// TODO： have 可能会引入3种不同的东西：set,obj,fn都可能；每种情况，处理起来不一样：比如如果你是fn和set，那可能就要把你放到 setMem 和 fnMem 里了
	exec.appendInternalWarningMsg("Litex only support have obj. if you want to introduce set or fn by the have stmt, you need to use the set or fn stmt to introduce them.")

	// TODO 把 exist prop def 里的东西释放出来
	existPropDef, ok := exec.env.GetExistPropDef(stmt.Fact.PropName)
	if !ok {
		return glob.ExecState_Unknown, nil
	}

	if len(existPropDef.ExistParams) != len(stmt.ObjNames) {
		return glob.ExecState_Error, fmt.Errorf("exist prop def params number not equal to have stmt obj names number. expect %d, but got %d", len(existPropDef.ExistParams), len(stmt.ObjNames))
	}

	// TODO 暂时认为都是obj
	for _, objName := range stmt.ObjNames {
		err := exec.env.NewDefObj(ast.NewDefObjStmt([]string{objName}, []ast.Fc{}, []ast.FactStmt{}, []ast.FactStmt{}))
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	uniMap := map[string]ast.Fc{}
	ExistParamsAtoms := []ast.Fc{}
	for i, param := range existPropDef.ExistParams {
		paramAsAtom := ast.NewFcAtomWithName(stmt.ObjNames[i])
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

	// param in param sets is true
	for _, paramInParamSet := range instantiatedExistPropDefStmt.ExistInSetsFacts {
		err := exec.env.NewFact(paramInParamSet)
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
		exec.appendMsg(fmt.Sprintf("%s\nis true by definition", domFact.String()))
	}

	// iff of def exist prop is true
	for _, iffFact := range instantiatedExistPropDefStmt.DefBody.IffFacts {
		err := exec.env.NewFact(iffFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		exec.appendMsg(fmt.Sprintf("%s\nis true by definition", iffFact.String()))
	}

	// 相关的 exist st 事实也成立
	existStFactParams := []ast.Fc{}
	existStFactParams = append(existStFactParams, ExistParamsAtoms...)
	existStFactParams = append(existStFactParams, ast.BuiltinExist_St_FactExistParamPropParmSepAtom)
	existStFactParams = append(existStFactParams, stmt.Fact.Params...)

	newExistStFact := ast.NewSpecFactStmt(ast.TrueExist_St, *ast.NewFcAtomWithName(stmt.Fact.PropName.Name), existStFactParams)
	err = exec.env.NewFact(newExistStFact)
	if err != nil {
		return glob.ExecState_True, nil
	}
	exec.appendMsg(fmt.Sprintf("%s\nis true by definition", newExistStFact.String()))

	return glob.ExecState_True, nil
}

func (exec *Executor) defStmt(stmt ast.DefStmt) error {
	// TODO：这里需要处理任何可能出现的 Def,包括stmt是个DefObj, DefProp, DefConExistProp, DefConFn, DefConProp. 本函数用于 claim forall x Type. 这里的 Type 可以是 obj, fn, prop, existProp.
	// 本函数需要处理所有可能的类型，并根据类型调用不同的函数。

	switch stmt := stmt.(type) {
	case *ast.DefObjStmt:
		return exec.defObjStmt(stmt)
	case *ast.DefFnStmt:
		return exec.defFnStmt(stmt)
	case *ast.DefPropStmt:
		return exec.defPropStmt(stmt)
	case *ast.DefExistPropStmt:
		return exec.defExistPropStmt(stmt)
	default:
		return fmt.Errorf("unknown def stmt type: %T", stmt)
	}
}

func (exec *Executor) GetUniFactSettings(asUnivFact *ast.UniFactStmt) error {
	for _, param := range asUnivFact.Params {
		err := exec.defStmt(ast.NewDefObjStmt([]string{param}, []ast.Fc{}, []ast.FactStmt{}, []ast.FactStmt{}))
		if err != nil {
			return err
		}
	}
	for _, fact := range asUnivFact.DomFacts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	return nil
}

func (exec *Executor) execProofBlock(proof []ast.Stmt) (glob.ExecState, error) {
	for _, curStmt := range proof {
		execState, err := exec.stmt(curStmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			if execState == glob.ExecState_Unknown && glob.ContinueExecutionIfExecUnknown {
				exec.appendWarningMsg("unknown fact: %s", curStmt.String())
				continue
			} else {
				return execState, nil
			}
		}
	}
	return glob.ExecState_True, nil
}

func (exec *Executor) claimStmtProve(stmt *ast.ClaimStmt) (bool, error) {
	exec.newEnv(exec.env, exec.env.CurMatchProp)
	isSuccess := false

	defer func() {
		exec.appendMsg("\n")
		if isSuccess {
			exec.appendNewMsgAtBegin("is true\n")
		} else {
			exec.appendNewMsgAtBegin("is unknown\n")
		}
		exec.appendNewMsgAtBegin(stmt.String())
		exec.deleteEnvAndRetainMsg()
	}()

	if asUnivFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt); ok {
		// 把变量引入，把dom事实引入
		err := exec.GetUniFactSettings(asUnivFact)
		if err != nil {
			return false, err
		}
	}

	execState, err := exec.execProofBlock(stmt.Proofs)
	if err != nil {
		return false, err
	}
	if execState != glob.ExecState_True {
		return false, nil
	}

	// 写成 prove: ... 这样的事实，是没有toCheckFact的，默认是nil
	if stmt.ToCheckFact == ast.ClaimStmtEmptyToCheck {
		isSuccess = true
		return true, nil
	}

	if asSpecFact, ok := stmt.ToCheckFact.(*ast.SpecFactStmt); ok {
		execState, err := exec.factStmt(asSpecFact)
		if err != nil {
			return false, err
		}
		if execState == glob.ExecState_True {
			isSuccess = true
		}
		return execState == glob.ExecState_True, nil
	}

	// TODO: 需要处理forall的情况
	if asUniFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt); ok {
		for _, fact := range asUniFact.ThenFacts {
			execState, err := exec.factStmt(fact)
			if err != nil {
				return false, err
			}
			if execState != glob.ExecState_True {
				return false, nil
			}
		}
		isSuccess = true
		return true, nil
	}

	return false, fmt.Errorf("unknown claim stmt to check fact type: %T", stmt.ToCheckFact)
}

func (exec *Executor) claimStmtProveByContradiction(stmt *ast.ClaimStmt) (bool, error) {
	exec.newEnv(exec.env, exec.env.CurMatchProp)
	isSuccess := false

	defer func() {
		exec.appendMsg("\n")
		if isSuccess {
			exec.appendNewMsgAtBegin("is true\n")
		} else {
			exec.appendNewMsgAtBegin("is unknown\n")
		}
		exec.appendNewMsgAtBegin(stmt.String())
		exec.deleteEnvAndRetainMsg()
	}()

	if stmt.ToCheckFact == ast.ClaimStmtEmptyToCheck {
		return false, fmt.Errorf("prove by contradiction does not support empty check")
	}

	// Must be SpecFactStmt
	specFactStmt, ok := stmt.ToCheckFact.(*ast.SpecFactStmt)
	if !ok {
		return false, fmt.Errorf("prove by contradiction only support spec fact")
	}

	reversedFact := specFactStmt.ReverseTrue()

	err := exec.env.NewFact(reversedFact)
	if err != nil {
		return false, err
	}

	for _, curStmt := range stmt.Proofs {
		execState, err := exec.stmt(curStmt)
		if err != nil {
			return false, err
		}
		if execState != glob.ExecState_True {
			return false, nil
		}
	}

	lastStmtAsFact, ok := stmt.Proofs[len(stmt.Proofs)-1].(*ast.SpecFactStmt)
	if !ok {
		return false, fmt.Errorf("prove by contradiction only support fact")
	}

	reversedLastFact := lastStmtAsFact.ReverseTrue()

	execState, err := exec.factStmt(reversedLastFact)
	if err != nil {
		return false, err
	}
	if execState == glob.ExecState_True {
		return true, nil
	}

	return false, nil
}

func (exec *Executor) setDefStmt(stmt *ast.SetDefSetBuilderStmt) error {
	defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))

	// err := exec.env.SetDefMem.Insert(stmt)

	// insert as obj
	inFact := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{ast.NewFcAtomWithName(stmt.SetName), ast.NewFcAtomWithName(glob.KeywordSet)})

	err := exec.defObjStmt(ast.NewDefObjStmt([]string{stmt.SetName}, []ast.Fc{ast.NewFcAtomWithName(glob.KeywordSet)}, []ast.FactStmt{}, []ast.FactStmt{inFact}))
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) proveInEachCaseStmt(stmt *ast.ProveInEachCaseStmt) (glob.ExecState, error) {
	isSuccess := false
	defer func() {
		exec.appendMsg("\n")
		if isSuccess {
			exec.appendNewMsgAtBegin("is true\n")
		} else {
			exec.appendNewMsgAtBegin("is unknown\n")
		}
		exec.appendNewMsgAtBegin(stmt.String())
	}()

	// prove orFact is true
	execState, err := exec.factStmt(&stmt.OrFact)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if execState != glob.ExecState_True {
		return glob.ExecState_Error, fmt.Errorf("prove in each case: or fact is not true")
	}

	for i := range stmt.OrFact.Facts {
		execState, err := exec.execProofBlockForEachCase(i, stmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return execState, nil
		}
	}

	isSuccess = true
	return glob.ExecState_True, nil
}

func (exec *Executor) execProofBlockForEachCase(index int, stmt *ast.ProveInEachCaseStmt) (glob.ExecState, error) {
	exec.newEnv(exec.env, exec.env.CurMatchProp)
	defer exec.deleteEnvAndRetainMsg()

	caseStmt := stmt.OrFact.Facts[index]

	err := exec.env.NewFact(&caseStmt)
	if err != nil {
		return glob.ExecState_Error, err
	}

	for _, proofStmt := range stmt.Proofs[index] {
		execState, err := exec.stmt(proofStmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return execState, nil
		}
	}

	// verify thenFacts are true
	for _, thenFact := range stmt.ThenFacts {
		execState, err := exec.factStmt(thenFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return execState, nil
		}
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) knowExistPropStmt(stmt *ast.KnowExistPropStmt) (glob.ExecState, error) {
	defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))

	err := exec.defExistPropStmt(&stmt.ExistProp)
	if err != nil {
		return glob.ExecState_Error, err
	}

	thenFacts := []ast.FactStmt{stmt.ExistProp.ToSpecFact()}
	knownUniFact := ast.NewUniFactStmtWithSetReqInDom(stmt.ExistProp.DefBody.DefHeader.Params, stmt.ExistProp.DefBody.DefHeader.SetParams, stmt.ExistProp.DefBody.DomFacts, thenFacts, ast.EmptyIffFacts, stmt.ExistProp.DefBody.DefHeader.ParamInSetsFacts)

	err = exec.env.NewFact(knownUniFact)
	if err != nil {
		return glob.ExecState_Error, err
	}

	exec.appendMsg(fmt.Sprintf("%s\nis true by definition", knownUniFact.String()))

	return glob.ExecState_True, nil
}

func (exec *Executor) knowPropStmt(stmt *ast.KnowPropStmt) error {
	defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))

	err := exec.defPropStmt(&stmt.Prop)
	if err != nil {
		return err
	}

	thenFacts := []ast.FactStmt{stmt.Prop.ToSpecFact()}
	knownUniFact := ast.NewUniFactStmtWithSetReqInDom(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.SetParams, stmt.Prop.DomFacts, thenFacts, ast.EmptyIffFacts, stmt.Prop.DefHeader.ParamInSetsFacts)

	err = exec.env.NewFact(knownUniFact)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) knowSupposeStmt(stmt *ast.KnowSupposeStmt) (glob.ExecState, error) {
	exec.env.CurMatchProp = &stmt.SupposeStmt.Fact
	defer func() {
		exec.env.CurMatchProp = nil
	}()

	knownFacts := []ast.FactStmt{}
	for _, stmt := range stmt.SupposeStmt.Body {
		if fact, ok := stmt.(ast.FactStmt); ok {
			knownFacts = append(knownFacts, fact)
		} else {
			return glob.ExecState_Error, fmt.Errorf("currently, know suppose stmt only supports fact stmt")
		}
	}

	execState, factsWithPrefix, err := exec.supposeStmt_storeFactsToParentEnv_addPrefixToSupposeFactAndBodyFacts(knownFacts, &stmt.SupposeStmt, exec.env)
	if err != nil {
		return glob.ExecState_Error, err
	}

	for i, fact := range factsWithPrefix {
		stmt.SupposeStmt.Body[i] = fact
	}

	return execState, nil
}
