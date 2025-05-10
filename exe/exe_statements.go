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

// 在子函数里管理msg，即比如现在是TypeStmt，那在处理TypeStmt的地方处理它的string，二不是在这里
func (exec *Executor) stmt(stmt ast.Stmt) (glob.ExecState, error) {
	var err error = nil
	var execState glob.ExecState = glob.ExecState_True

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		execState, err = exec.factStmt(stmt)
	case *ast.KnowStmt:
		err = exec.knowStmt(stmt)
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
	case *ast.MatcherEnvStmt:
		err = exec.matcherEnvStmt(stmt)
	case *ast.KnowPropStmt:
		err = exec.knowPropStmt(stmt)
	case *ast.SetDefSetBuilderStmt:
		err = exec.setDefStmt(stmt)
	case *ast.ProveInEachCaseStmt:
		execState, err = exec.proveInEachCaseStmt(stmt)

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

	curVerifier := verifier.NewVerifier(exec.env, exec.curPkg)
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
			newStmt := asSpecFact.ReverseIsTrue()
			curVerifier := verifier.NewVerifier(exec.env, exec.curPkg)
			ok, err := curVerifier.FactStmt(newStmt, verifier.Round0Msg)
			if err != nil {
				return glob.ExecState_Error, err
			}
			if ok {
				exec.appendMsg(asSpecFact.String() + "\nis false")
				return glob.ExecState_False, nil
			} else {
				exec.appendMsg(stmt.String() + "\nis unknown")
			}
		}
	} else {
		exec.appendMsg(stmt.String() + "\nis unknown")
	}

	return glob.ExecState_Unknown, nil
}

func (exec *Executor) knowStmt(stmt *ast.KnowStmt) error {
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
	// TODO: 这里需要优化，因为claim和prove的逻辑是一样的，所以可以合并
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

	// store
	if !isSuccess {
		return glob.ExecState_Unknown, nil
	}

	if asSpecFact, ok := stmt.ToCheckFact.(*ast.SpecFactStmt); ok {
		err = exec.env.Parent.NewFact(asSpecFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	} else if asUniFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt); ok {
		newUniFact, err := ast.AddUniPrefixToUniFact(asUniFact)
		if err != nil {
			return glob.ExecState_Error, err
		}

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

	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendMsg(stmt.String())

	// iff leads to prop
	err := exec.env.NewDefProp(stmt)
	if err != nil {
		return err
	}

	// prop leads to iff
	if len(stmt.IffFacts) == 0 {
		return nil
	}

	uniFactParams := stmt.DefHeader.Params
	uniFactParamSets := stmt.DefHeader.SetParams
	domFacts := []ast.FactStmt{}
	domFacts = append(domFacts, stmt.DomFacts...)
	propAsSpec := stmt.ToSpecFact()
	domFacts = append(domFacts, propAsSpec)

	newUniFact := ast.NewUniFactStmtWithSetReqInDom(uniFactParams, uniFactParamSets, domFacts, stmt.IffFacts, ast.EmptyIffFacts, stmt.DefHeader.ParamInSetsFacts)

	err = exec.env.NewFact(newUniFact)

	exec.appendMsg(fmt.Sprintf("know by prop definition:\n%s", newUniFact.String()))

	if err != nil {
		return err
	}

	if len(stmt.IffFacts) == 0 {
		return nil
	}

	return nil
}

func (exec *Executor) defObjStmt(stmt *ast.DefObjStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
	err := exec.env.NewDefObj(stmt)
	if err != nil {
		return err
	}

	for i, objName := range stmt.Objs {
		objInSetFact := ast.SpecFactStmt{
			TypeEnum: ast.TruePure,
			PropName: ast.FcAtom{
				PkgName: "",
				Name:    glob.KeywordIn,
			},
			Params: []ast.Fc{&ast.FcAtom{PkgName: glob.BtEmptyPkgName, Name: objName}, stmt.ObjSets[i]},
		}
		err := exec.env.NewFact(&objInSetFact)
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

	fcFnParams := []ast.Fc{}
	for _, fc := range stmt.DefHeader.Params {
		fcFnParams = append(fcFnParams, &ast.FcAtom{PkgName: "", Name: fc})
	}

	fcFn := ast.FcFn{FnHead: &ast.FcAtom{PkgName: glob.BtEmptyPkgName, Name: stmt.DefHeader.Name}, ParamSegs: [][]ast.Fc{fcFnParams}}

	retFact := ast.SpecFactStmt{TypeEnum: ast.TruePure, PropName: ast.FcAtom{PkgName: "", Name: glob.KeywordIn}, Params: []ast.Fc{&fcFn, stmt.RetSet}}

	uniFactThen := []ast.FactStmt{&retFact}
	uniFactThen = append(uniFactThen, stmt.ThenFacts...)

	thenFacts := []ast.FactStmt{}
	thenFacts = append(thenFacts, uniFactThen...)

	uniFact := ast.UniFactStmt{Params: stmt.DefHeader.Params, ParamSets: stmt.DefHeader.SetParams, DomFacts: stmt.DomFacts, ThenFacts: thenFacts}
	err = exec.env.NewFact(&uniFact)

	if err != nil {
		return err
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

	// TODO 暂时认为都是obj
	for _, objName := range stmt.ObjNames {
		err := exec.env.NewDefObj(&ast.DefObjStmt{Objs: []string{objName}, ObjSets: []ast.Fc{}, Facts: []ast.FactStmt{}})
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// TODO 把 exist prop def 里的东西释放出来
	existPropDef, ok := exec.env.GetExistPropDef(stmt.Fact.PropName)
	if !ok {
		return glob.ExecState_Unknown, nil
	}

	uniMap := map[string]ast.Fc{}
	paramAsAtoms := []ast.Fc{}
	for i, param := range existPropDef.DefBody.DefHeader.Params {
		paramAsAtom := ast.NewFcAtom(glob.BtEmptyPkgName, stmt.ObjNames[i])
		uniMap[param] = paramAsAtom
		paramAsAtoms = append(paramAsAtoms, paramAsAtom)
	}

	instantiatedExistPropDefStmt, err := existPropDef.Instantiate(uniMap)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// param in param sets is true
	paramInParamFacts, err := exec.ParamInParamSets(&instantiatedExistPropDefStmt.DefBody.DefHeader)
	if err != nil {
		return glob.ExecState_Error, err
	}
	for _, paramInParamSet := range paramInParamFacts {
		err := exec.env.NewFact(&paramInParamSet)
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
	}

	// iff of def exist prop is true
	for _, iffFact := range instantiatedExistPropDefStmt.DefBody.IffFacts {
		err := exec.env.NewFact(iffFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// 相关的 exist st 事实也成立
	existStFactParams := []ast.Fc{}
	existStFactParams = append(existStFactParams, paramAsAtoms...)
	existStFactParams = append(existStFactParams, ast.BuiltinExist_St_FactExistParamPropParmSepAtom)
	existStFactParams = append(existStFactParams, stmt.Fact.Params...)

	newExistStFact := ast.SpecFactStmt{
		TypeEnum: ast.TrueExist_St,
		PropName: ast.FcAtom{PkgName: exec.curPkg, Name: stmt.Fact.PropName.Name},
		Params:   existStFactParams,
	}
	err = exec.env.NewFact(&newExistStFact)
	if err != nil {
		return glob.ExecState_True, nil
	}

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

func (exec *Executor) matcherEnvStmt(stmt *ast.MatcherEnvStmt) error {
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	for _, curStmt := range stmt.Body {
		execState, err := exec.stmt(curStmt)
		if err != nil {
			return err
		}
		if execState != glob.ExecState_True {
			return fmt.Errorf("matcher env stmt is not true")
		}
	}

	return nil
}

func (exec *Executor) GetUniFactSettings(asUnivFact *ast.UniFactStmt) error {
	for i, param := range asUnivFact.Params {
		exec.defStmt(&ast.DefObjStmt{Objs: []string{param}, ObjSets: []ast.Fc{asUnivFact.ParamSets[i]}, Facts: []ast.FactStmt{}})
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
			if execState == glob.ExecState_Unknown && glob.ContinueExecutionWhenExecUnknown {
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
	exec.newEnv()
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
	exec.newEnv()
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

	newClaimFact := specFactStmt.ReverseIsTrue()

	err := exec.env.NewFact(newClaimFact)
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

	reverseLastFact := lastStmtAsFact.ReverseIsTrue()

	execState, err := exec.factStmt(reverseLastFact)
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

	err := exec.env.SetMem.Insert(stmt, exec.curPkg)
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
	exec.newEnv()
	defer exec.deleteEnvAndRetainMsg()

	caseStmt := stmt.OrFact.Facts[index]

	err := exec.env.NewFact(caseStmt)
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
