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
	case *ast.HaveObjStStmt:
		execState, err = exec.haveObjStStmt(stmt)
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
	case *ast.ProveByMathInductionStmt:
		execState, err = exec.mathInductionFact_BuiltinRules(stmt)
	case *ast.ProveOverFiniteSetStmt:
		execState, err = exec.proveOverFiniteSetStmt(stmt)
	case *ast.HaveObjInNonEmptySetStmt:
		execState, err = exec.haveObjInNonEmptySetStmt(stmt)
	case *ast.HaveSetStmt:
		execState, err = exec.haveSetStmt(stmt)
	case *ast.HaveSetFnStmt:
		execState, err = exec.haveSetFnStmt(stmt)
	case *ast.HaveSetDefinedByReplacementStmt:
		execState, err = exec.haveSetDefinedByReplacementStmt(stmt)
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

	if len(stmt.IffFacts) == 0 {
		return nil
	}

	// prop leads to iff
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

func (exec *Executor) execProofBlockAtCurEnv(proof []ast.Stmt) (glob.ExecState, error) {
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

	exec.newEnv(exec.env)
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
	ok := exec.env.AreAtomsInFactAreDeclared(stmt.ToCheckFact, map[string]struct{}{})
	if !ok {
		return glob.ExecState_Error, fmt.Errorf(env.AtomsInFactNotDeclaredMsg(stmt.ToCheckFact))
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
		execState, err := exec.execProofBlockAtCurEnv(stmt.Proofs)
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

	exec.newEnv(exec.env)
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

	execState, err := exec.execProofBlockAtCurEnv(stmt.ClaimProveStmt.Proofs)
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
	exec.newEnv(exec.env)
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

	if len(stmt.Prop.IffFacts) == 0 {
		_, iffToProp, err := stmt.Prop.Make_PropToIff_IffToProp()
		if err != nil {
			return err
		}
		err = exec.env.NewFact(iffToProp)
		if err != nil {
			return err
		}
	}

	paramsAsFc := []ast.Fc{}
	for i := range stmt.Prop.DefHeader.Params {
		paramsAsFc = append(paramsAsFc, ast.FcAtom(stmt.Prop.DefHeader.Params[i]))
	}

	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(stmt.Prop.DefHeader.Name), paramsAsFc)}, stmt.Prop.ThenFacts)

	err = exec.env.NewFact(uniFact)
	if err != nil {
		return err
	}

	uniFact2 := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.IffFacts, stmt.Prop.ThenFacts)
	err = exec.env.NewFact(uniFact2)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) proveStmt(stmt *ast.ProveStmt) (glob.ExecState, error) {
	// new env
	exec.newEnv(exec.env)
	defer exec.deleteEnvAndRetainMsg()

	return exec.execProofBlockAtCurEnv(stmt.Proof)
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
	execState, err := exec.execProofBlockAtCurEnv(stmt.Proofs)
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

	err := exec.env.NewObj_NoDuplicate(stmt.FnTemplateStmt.Name)
	if err != nil {
		return err
	}

	err = exec.env.StoreFnSatisfyFnTemplateFact(ast.FcAtom(stmt.FnTemplateStmt.Name), &stmt.FnTemplateStmt)
	if err != nil {
		return err
	}

	// derivedFact := stmt.FnTemplateStmt.DeriveUniFact(ast.FcAtom(stmt.FnTemplateStmt.Name))
	derivedFact := stmt.FnTemplateStmt.DeriveUniFact()
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
	var err error
	var execState glob.ExecState = glob.ExecState_Error

	// prop all atoms declared
	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.DomFacts, stmt.Prop.IffFacts)
	if !exec.env.AreAtomsInFactAreDeclared(uniFact, map[string]struct{}{}) && !exec.env.IsFcAtomDeclaredByUser(ast.FcAtom(stmt.Prop.DefHeader.Name)) {
		return glob.ExecState_Error, fmt.Errorf("claim prop statement error: atoms in fact are not declared")
	}

	// check proofs
	if stmt.IsProve {
		execState, err = exec.checkClaimPropStmtProofs(stmt)
		if notOkExec(execState, err) {
			return execState, err
		}
	} else {
		execState, err = exec.checkClaimPropStmtProveByContradiction(stmt)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	// know exec
	err = exec.knowPropStmt(ast.NewKnowPropStmt(stmt.Prop))
	if notOkExec(execState, err) {
		return execState, err
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) checkClaimPropStmtProofs(stmt *ast.ClaimPropStmt) (glob.ExecState, error) {
	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.IffFacts, stmt.Prop.ThenFacts)

	exec.newEnv(exec.env)
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

func (exec *Executor) proveOverFiniteSetStmt(stmt *ast.ProveOverFiniteSetStmt) (glob.ExecState, error) {
	exec.appendMsg(stmt.String())

	ver := verifier.NewVerifier(exec.env)
	return ver.ProveOverFiniteSet(stmt)
}

func (exec *Executor) haveSetFnStmt(stmt *ast.HaveSetFnStmt) (glob.ExecState, error) {
	exec.appendMsg(stmt.String())

	// declare related fn
	fnDefStmt := stmt.ToDefFnStmt()
	err := exec.defFnStmt(fnDefStmt)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// have set fn
	exec.env.HaveSetFnDefMem[stmt.DefHeader.Name] = *stmt

	return glob.ExecState_True, nil
}

func (exec *Executor) checkClaimPropStmtProveByContradiction(stmt *ast.ClaimPropStmt) (glob.ExecState, error) {
	exec.newEnv(exec.env)
	defer func() {
		exec.deleteEnvAndRetainMsg()
	}()

	// declare parameters in prop

	objDefStmt := ast.NewDefObjStmt(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.IffFacts)
	err := exec.defObjStmt(objDefStmt, false)
	if err != nil {
		return glob.ExecState_Error, err
	}

	thenFactsAsReversible := []ast.OrStmt_SpecStmt{}
	for _, fact := range stmt.Prop.ThenFacts {
		asReversible, ok := fact.(ast.OrStmt_SpecStmt)
		if !ok {
			return glob.ExecState_Error, fmt.Errorf("claim prop statement error: then fact is not an or statement")
		}
		thenFactsAsReversible = append(thenFactsAsReversible, asReversible)
	}

	// assume reverse of all then facts in prop or true
	reversedThenFacts := ast.ReverseSliceOfReversibleFacts(thenFactsAsReversible)
	for _, fact := range reversedThenFacts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	execState, err := exec.execProofBlockAtCurEnv(stmt.Proofs)
	if notOkExec(execState, err) {
		return execState, err
	}

	// 最后一项的逆也对
	lastProof := stmt.Proofs[len(stmt.Proofs)-1]
	lastProofAsReversible, ok := lastProof.(ast.OrStmt_SpecStmt)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("claim prop statement error: last proof is not an or statement")
	}

	reverseLastProof := lastProofAsReversible.ReverseIsTrue()
	for _, fact := range reverseLastProof {
		execState, err := exec.factStmt(&fact)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) haveSetDefinedByReplacementStmt(stmt *ast.HaveSetDefinedByReplacementStmt) (glob.ExecState, error) {
	exec.appendMsg(stmt.String())

	defObjStmt := ast.NewDefObjStmt([]string{stmt.Name}, []ast.Fc{ast.NewFcFn(ast.FcAtom(glob.KeywordSetDefinedByReplacement), []ast.Fc{stmt.DomSet, stmt.RangeSet, stmt.PropName})}, []ast.FactStmt{})
	err := exec.defObjStmt(defObjStmt, false)
	if err != nil {
		return glob.ExecState_Error, err
	}

	return glob.ExecState_True, nil
}
