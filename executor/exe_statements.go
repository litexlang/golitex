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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
	verifier "golitex/verifier"
	"strings"
)

func (exec *Executor) Stmt(stmt ast.Stmt) (glob.ExecState, error) {
	var err error = nil
	var execState glob.ExecState = glob.ExecState_True

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		execState, err = exec.factStmt(stmt)
	case *ast.KnowFactStmt:
		err = exec.knowStmt(stmt)
	case *ast.ClaimProveStmt:
		execState, err = exec.claimStmt(stmt)
	case *ast.DefPropStmt:
		err = exec.defPropStmt(stmt)
	case *ast.DefObjStmt:
		err = exec.defObjStmt(stmt, true)
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
	case *ast.ProveInEachCaseStmt:
		execState, err = exec.proveInEachCaseStmt(stmt)
	case *ast.SupposeStmt:
		execState, err = exec.supposePropMatchStmt(stmt)
	case *ast.WithStmt:
		execState, err = exec.withStmt(stmt)
	case *ast.ImportDirStmt:
		execState, err = exec.importDirStmt(stmt)
	case *ast.ImportFileStmt:
		execState, err = exec.importFileStmt(stmt)
	case *ast.ClaimPropStmt:
		execState, err = exec.claimPropStmt(stmt)
	case *ast.ClaimExistPropStmt:
		execState, err = exec.claimExistPropStmt(stmt)
	case *ast.ProveStmt:
		execState, err = exec.proveStmt(stmt)
	case *ast.ClaimProveByContradictionStmt:
		execState, err = exec.execClaimStmtProveByContradiction(stmt)
	case *ast.DefFnTemplateStmt:
		err = exec.defFnTemplateStmt(stmt)
	case *ast.ImportGloballyStmt:
		execState, err = exec.importGloballyStmt(stmt)
	case *ast.ProveByMathInductionStmt:
		execState, err = exec.mathInductionFact_BuiltinRules(stmt)
	default:
		err = fmt.Errorf("unknown statement type: %T", stmt)
	}

	if err != nil {
		return glob.ExecState_Error, glob.NewErrLink(err, "execution error:")
	} else {
		return execState, nil
	}
}

func (exec *Executor) factStmt(stmt ast.FactStmt) (glob.ExecState, error) {
	if glob.IsNotImportDirStmt() {
		defer exec.appendMsg("\n")
	}

	curVerifier := verifier.NewVerifier(exec.env)
	ok, err := curVerifier.VerFactStmt(stmt, verifier.Round0Msg)
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
		state, err := exec.checkReverse(stmt)
		if notOkExec(state, err) {
			return state, err
		}
		return state, nil
	} else {
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(stmt.String() + "\nis unknown")
		}
	}

	return glob.ExecState_Unknown, nil
}

// TODO: 再know时就检查，仅仅依赖写在dom里的事实，是否真的能让涉及到的函数和prop能真的满足条件。如果不满足条件，那就warning
func (exec *Executor) knowStmt(stmt *ast.KnowFactStmt) error {
	if glob.IsNotImportDirStmt() {
		defer exec.appendMsg("\n")
	}

	for _, fact := range stmt.Facts {
		if !exec.env.AreAtomsInFactAreDeclared(fact, map[string]struct{}{}) {
			return fmt.Errorf(env.AtomsInFactNotDeclaredMsg(fact))
		}

		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	if glob.IsNotImportDirStmt() {
		exec.appendMsg(stmt.String())
	}
	return nil
}

func (exec *Executor) claimStmt(stmt *ast.ClaimProveStmt) (glob.ExecState, error) {
	return exec.execClaimStmtProve(stmt)
}

func (exec *Executor) execClaimStmtProve(stmt *ast.ClaimProveStmt) (glob.ExecState, error) {
	state, err := exec.claimStmtProve(stmt)
	if notOkExec(state, err) {
		return state, err
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	exec.knowStmt(ast.NewKnowStmt([]ast.FactStmt{stmt.ToCheckFact}))

	return glob.ExecState_True, nil
}

func (exec *Executor) execClaimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) (glob.ExecState, error) {
	state, err := exec.claimStmtProveByContradiction(stmt)
	if notOkExec(state, err) {
		return state, err
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	exec.knowStmt(ast.NewKnowStmt([]ast.FactStmt{stmt.ClaimProveStmt.ToCheckFact}))

	return glob.ExecState_True, nil
}

func (exec *Executor) GetMsgAsStr0ToEnd() string {
	ret := strings.Join(exec.env.Msgs, "\n")
	exec.env.Msgs = []string{}
	return ret
}

func (exec *Executor) defPropStmt(stmt *ast.DefPropStmt) error {
	if glob.IsNotImportDirStmt() {
		defer exec.appendMsg(stmt.String() + "\n")
	}

	err := exec.env.NewDefProp_InsideAtomsDeclared(stmt)
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
	if err != nil {
		return err
	}
	if glob.IsNotImportDirStmt() {
		exec.appendMsg(fmt.Sprintf("%s\nis true by definition", propToIff.String()))
	}

	err = exec.env.NewFact(iffToProp)
	if err != nil {
		return err
	}
	if glob.IsNotImportDirStmt() {
		exec.appendMsg(fmt.Sprintf("%s\nis true by definition", iffToProp.String()))
	}

	if len(stmt.IffFacts) == 0 {
		return nil
	}

	return nil
}

func (exec *Executor) defObjStmt(stmt *ast.DefObjStmt, requireMsg bool) error {
	if glob.IsNotImportDirStmt() {
		defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
	}

	if requireMsg {
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
		}
	}

	ver := verifier.NewVerifier(exec.env)
	return ver.NewDefObj_InsideAtomsDeclared(stmt)
}

// func (exec *Executor) defFnStmt(stmt *ast.DefFnStmt) error {
// 	defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))

// 	err := exec.env.KnowDefFnSatisfyFnTemplate_KnowUniFactDerivedFromDefFn(ast.NewFcAtomWithName(stmt.Name), &stmt.FnTemplateStmt)
// 	if err != nil {
// 		return err
// 	}

// 	// put into obj mem
// 	err = exec.env.ObjDefMem.InsertItem(stmt.Name)
// 	if err != nil {
// 		return err
// 	}

// 	return nil
// }

func (exec *Executor) defFnTemplateStmt(stmt *ast.DefFnTemplateStmt) error {
	if glob.IsNotImportDirStmt() {
		defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
	}

	err := exec.env.ExecDefFnTemplate(stmt)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) defExistPropStmt(stmt *ast.DefExistPropStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	if glob.IsNotImportDirStmt() {
		defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
	}

	return exec.env.NewDefExistProp_InsideAtomsDeclared(stmt)
}

func (exec *Executor) haveStmt(stmt *ast.HaveStmt) (glob.ExecState, error) {
	defer func() {
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
		}
	}()

	// 检查 SpecFactStmt 是否满足了
	execState, err := exec.factStmt(&stmt.Fact)
	if notOkExec(execState, err) {
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(fmt.Sprintf("%s is unknown", stmt.Fact.String()))
		}
		return execState, err
	}

	// TODO： have 可能会引入3种不同的东西：set,obj,fn都可能；每种情况，处理起来不一样：比如如果你是fn和set，那可能就要把你放到 setMem 和 fnMem 里了
	// 这个 warning 不合时宜了，因为fn的定义其实和obj一样了，就是额外多个满足特定的template
	exec.appendInternalWarningMsg("Litex only support have obj. if you want to introduce set or fn by the have stmt, you need to use the set or fn stmt to introduce them.")

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
		err := ver.NewDefObj_InsideAtomsDeclared(ast.NewDefObjStmt([]string{objName}, []ast.Fc{instantiatedExistPropDefStmt.ExistParamSets[i]}, []ast.FactStmt{}))
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
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(fmt.Sprintf("%s\nis true by definition", domFact.String()))
		}
	}

	// iff of def exist prop is true
	for _, iffFact := range instantiatedExistPropDefStmt.DefBody.IffFacts {
		err := exec.env.NewFact(iffFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(fmt.Sprintf("%s\nis true by definition", iffFact.String()))
		}
	}

	// 相关的 exist st 事实也成立
	existStFactParams := ast.MakeExistFactParamsSlice(ExistParamsAtoms, stmt.Fact.Params)

	newExistStFact := ast.NewSpecFactStmt(ast.TrueExist_St, ast.FcAtom(string(stmt.Fact.PropName)), existStFactParams)
	err = exec.env.NewFact(newExistStFact)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if glob.IsNotImportDirStmt() {
		exec.appendMsg(fmt.Sprintf("%s\nis true by definition", newExistStFact.String()))
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) execProofBlock(proof []ast.Stmt) (glob.ExecState, error) {
	for _, curStmt := range proof {
		execState, err := exec.Stmt(curStmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			if execState == glob.ExecState_Unknown && glob.ContinueExecutionIfExecUnknown {
				exec.appendWarningMsg("unknown fact:\n%s", curStmt.String())
				return glob.ExecState_Unknown, nil
			} else {
				return execState, nil
			}
		}
	}
	return glob.ExecState_True, nil
}

func (exec *Executor) claimStmtProve(stmt *ast.ClaimProveStmt) (glob.ExecState, error) {
	err := error(nil)
	isSuccess := false

	exec.newEnv(exec.env, exec.env.CurMatchProp)
	if glob.IsNotImportDirStmt() {
		defer func() {
			exec.appendMsg("\n")
			if isSuccess {
				exec.appendNewMsgAtBegin("is true\n\n")
			} else {
				exec.appendNewMsgAtBegin("is unknown\n\n")
			}
			exec.appendNewMsgAtBegin(stmt.String())
			exec.deleteEnvAndRetainMsg()
		}()
	}

	// 需要检查stmt.ToCheckFact里的东西都是在外部声明好了的
	if stmt.ToCheckFact != ast.ClaimStmtEmptyToCheck {
		ok := exec.env.AreAtomsInFactAreDeclared(stmt.ToCheckFact, map[string]struct{}{})
		if !ok {
			return glob.ExecState_Error, fmt.Errorf(env.AtomsInFactNotDeclaredMsg(stmt.ToCheckFact))
		}
	}

	if _, ok := stmt.ToCheckFact.(*ast.UniFactStmt); ok {
		isSuccess, err = exec.claimStmtProveUniFact(stmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if !isSuccess {
			return glob.ExecState_Unknown, nil
		}
		return glob.ExecState_True, nil
	} else {
		execState, err := exec.execProofBlock(stmt.Proofs)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return glob.ExecState_Unknown, nil
		}
		// check claim
		execState, err = exec.factStmt(stmt.ToCheckFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return glob.ExecState_Unknown, nil
		}
		return glob.ExecState_True, nil
	}
}

func (exec *Executor) claimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) (glob.ExecState, error) {
	isSuccess := false

	exec.newEnv(exec.env, exec.env.CurMatchProp)
	if glob.IsNotImportDirStmt() {
		defer func() {
			exec.appendMsg("\n")
			if isSuccess {
				exec.appendNewMsgAtBegin("is true\n")
			} else {
				exec.appendNewMsgAtBegin("is unknown\n")
			}
			exec.appendNewMsgAtBegin(stmt.ClaimProveStmt.String())
			exec.deleteEnvAndRetainMsg()
		}()
	}

	if stmt.ClaimProveStmt.ToCheckFact == ast.ClaimStmtEmptyToCheck {
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction does not support empty check")
	}

	// Must be orStmt or specFactStmt
	specFactStmt, ok := stmt.ClaimProveStmt.ToCheckFact.(ast.OrStmt_SpecStmt)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction only support spec fact")
	}

	reversedFact := specFactStmt.ReverseIsTrue()

	for _, curFact := range reversedFact {
		err := exec.env.NewFact(&curFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	execState, err := exec.execProofBlock(stmt.ClaimProveStmt.Proofs)
	if notOkExec(execState, err) {
		return execState, err
	}

	lastStmtAsFact, ok := stmt.ClaimProveStmt.Proofs[len(stmt.ClaimProveStmt.Proofs)-1].(ast.OrStmt_SpecStmt)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction only support fact")
	}

	reversedLastFact := lastStmtAsFact.ReverseIsTrue()

	for _, curFact := range reversedLastFact {
		execState, err = exec.factStmt(&curFact)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) proveInEachCaseStmt(stmt *ast.ProveInEachCaseStmt) (glob.ExecState, error) {
	isSuccess := false
	defer func() {
		if glob.IsNotImportDirStmt() {
			exec.appendMsg("\n")
		}
		if isSuccess {
			exec.appendNewMsgAtBegin("is true\n")
		} else {
			exec.appendNewMsgAtBegin("is unknown\n")
		}
		exec.appendNewMsgAtBegin(stmt.String())
	}()

	// prove orFact is true
	execState, err := exec.factStmt(&stmt.OrFact)
	if notOkExec(execState, err) {
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(fmt.Sprintf("%s is unknown", stmt.OrFact.String()))
		}
		return execState, err
	}

	for i := range stmt.OrFact.Facts {
		execState, err := exec.execProofBlockForEachCase(i, stmt)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	isSuccess = true
	return glob.ExecState_True, nil
}

func (exec *Executor) execProofBlockForEachCase(index int, stmt *ast.ProveInEachCaseStmt) (glob.ExecState, error) {
	exec.newEnv(exec.env, exec.env.CurMatchProp)
	defer exec.deleteEnvAndRetainMsg()

	caseStmt := stmt.OrFact.Facts[index]

	err := exec.env.NewFact(caseStmt)
	if err != nil {
		return glob.ExecState_Error, err
	}

	for _, proofStmt := range stmt.Proofs[index] {
		execState, err := exec.Stmt(proofStmt)
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

// 只要 dom 成立，那prop成立，进而prop的iff成立
func (exec *Executor) knowExistPropStmt(stmt *ast.KnowExistPropStmt) (glob.ExecState, error) {
	if glob.IsNotImportDirStmt() {
		defer func() {
			exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
		}()
	}

	err := exec.defExistPropStmt(&stmt.ExistProp)
	if err != nil {
		return glob.ExecState_Error, err
	}

	thenFacts := []ast.FactStmt{stmt.ExistProp.ToSpecFact()}
	knownUniFact := ast.NewUniFact(stmt.ExistProp.DefBody.DefHeader.Params, stmt.ExistProp.DefBody.DefHeader.ParamSets, stmt.ExistProp.DefBody.DomFacts, thenFacts)

	err = exec.env.NewFact(knownUniFact)
	if err != nil {
		return glob.ExecState_Error, err
	}

	if glob.IsNotImportDirStmt() {
		exec.appendMsg(fmt.Sprintf("%s\nis true by definition", knownUniFact.String()))
	}

	return glob.ExecState_True, nil
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
func (exec *Executor) knowPropStmt(stmt *ast.KnowPropStmt) error {
	if glob.IsNotImportDirStmt() {
		defer func() {
			exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
		}()
	}

	err := exec.defPropStmt(&stmt.Prop)
	if err != nil {
		return err
	}

	thenFacts := []ast.FactStmt{stmt.Prop.ToSpecFact()}
	knownUniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.DomFacts, thenFacts)

	err = exec.env.NewFact(knownUniFact)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) proveStmt(stmt *ast.ProveStmt) (glob.ExecState, error) {
	// new env
	exec.newEnv(exec.env, exec.env.CurMatchProp)
	defer exec.deleteEnvAndRetainMsg()

	return exec.execProofBlock(stmt.Proof)
}

// prove uniFact in claim at current env
func (exec *Executor) claimStmtProveUniFact(stmt *ast.ClaimProveStmt) (bool, error) {
	asUnivFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt)
	if !ok {
		return false, fmt.Errorf("claim stmt prove uni fact only support uni fact")
	}

	// declare parameters in asUnivFact in the env
	objDefStmt := ast.NewDefObjStmt(asUnivFact.Params, asUnivFact.ParamSets, asUnivFact.DomFacts)
	err := exec.defObjStmt(objDefStmt, false)
	if err != nil {
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(fmt.Sprintf("Claim statement error: Failed to declare parameters in universal fact:\n%s\n", objDefStmt.String()))
		}
		return false, err
	}

	// exec proof block
	execState, err := exec.execProofBlock(stmt.Proofs)
	if err != nil {
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(fmt.Sprintf("Claim statement error: Failed to execute proof block:\n%s\n", stmt.String()))
		}
		return false, err
	}
	if execState != glob.ExecState_True {
		return false, nil
	}

	// TODO: 让claim能forall if
	// if asUnivFact.IffFacts == nil || len(asUnivFact.IffFacts) == 0 {
	for _, fact := range asUnivFact.ThenFacts {
		execState, err := exec.factStmt(fact)
		if err != nil {
			if glob.IsNotImportDirStmt() {
				exec.appendMsg(fmt.Sprintf("Claim statement error: Failed to execute fact statement:\n%s\n", fact.String()))
			}
			return false, err
		}
		if execState != glob.ExecState_True {
			return false, nil
		}
	}
	return true, nil

}

func (exec *Executor) defFnStmt(stmt *ast.DefFnStmt) error {
	if glob.IsNotImportDirStmt() {
		defer func() {
			exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
		}()
	}

	err := exec.env.NewObj(stmt.FnTemplateStmt.Name)
	if err != nil {
		return err
	}

	err = exec.env.StoreFnSatisfyFnTemplateFact(ast.FcAtom(stmt.FnTemplateStmt.Name), &stmt.FnTemplateStmt)
	if err != nil {
		return err
	}

	derivedFact := stmt.FnTemplateStmt.DeriveUniFact(ast.FcAtom(stmt.FnTemplateStmt.Name))
	err = exec.env.NewFact(derivedFact)
	if err != nil {
		return err
	}

	if glob.IsNotImportDirStmt() {
		exec.appendMsg(fmt.Sprintf("%s\nis true by definition", derivedFact.String()))
	}

	return nil
}

func (exec *Executor) checkReverse(stmt ast.FactStmt) (glob.ExecState, error) {
	if asSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
		reversedFact := asSpecFact.ReverseTrue()
		curVerifier := verifier.NewVerifier(exec.env)
		ok, err := curVerifier.VerFactStmt(reversedFact, verifier.Round0Msg)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if ok {
			if glob.IsNotImportDirStmt() {
				exec.appendMsg(asSpecFact.String() + "\nis false")
			}
			return glob.ExecState_False, nil
		} else {
			if glob.IsNotImportDirStmt() {
				exec.appendMsg(stmt.String() + "\nis unknown")
			}
		}
	} else if asOrStmt, ok := stmt.(*ast.OrStmt); ok {
		for _, fact := range asOrStmt.Facts {
			execState, err := exec.checkReverse(fact)
			if notOkExec(execState, err) {
				if glob.IsNotImportDirStmt() {
					exec.appendMsg(stmt.String() + "\nis unknown")
				}
				return execState, err
			}
		}
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(stmt.String() + "\nis false")
		}
	} else {
		if glob.IsNotImportDirStmt() {
			exec.appendMsg(stmt.String() + "\nis unknown")
		}
	}

	return glob.ExecState_Unknown, nil
}

// 也许我应该语义改成，先声明prop，然后再证明prop，而不是现在这个样子
func (exec *Executor) claimPropStmt(stmt *ast.ClaimPropStmt) (glob.ExecState, error) {
	// prop all atoms declared
	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.DomFacts, stmt.Prop.IffFacts)
	if !exec.env.AreAtomsInFactAreDeclared(uniFact, map[string]struct{}{}) && !exec.env.IsFcAtomDeclaredByUser(ast.FcAtom(stmt.Prop.DefHeader.Name)) {
		return glob.ExecState_Error, fmt.Errorf("claim prop statement error: atoms in fact are not declared")
	}

	// check proofs
	execState, err := exec.checkClaimPropStmtProofs(stmt)
	if notOkExec(execState, err) {
		return execState, err
	}

	// know exec
	err = exec.knowPropStmt(ast.NewKnowPropStmt(stmt.Prop))
	if notOkExec(execState, err) {
		return execState, err
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) checkClaimPropStmtProofs(stmt *ast.ClaimPropStmt) (glob.ExecState, error) {
	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.DomFacts, stmt.Prop.IffFacts)

	exec.newEnv(exec.env, exec.env.CurMatchProp)
	defer func() {
		exec.deleteEnvAndRetainMsg()
	}()

	ok, err := exec.claimStmtProveUniFact(ast.NewClaimProveStmt(uniFact, stmt.Proofs))
	if err != nil {
		return glob.ExecState_Error, err
	}
	if !ok {
		return glob.ExecState_False, nil
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) claimExistPropStmt(stmt *ast.ClaimExistPropStmt) (glob.ExecState, error) {
	return exec.checkClaimExistPropStmtProofs(stmt)
}

func (exec *Executor) checkClaimExistPropStmtProofs(stmt *ast.ClaimExistPropStmt) (glob.ExecState, error) {
	panic("not implemented")
}
