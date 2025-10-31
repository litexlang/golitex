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
	env "golitex/environment"
	glob "golitex/glob"
	verifier "golitex/verifier"
	"strings"
)

func (exec *Executor) claimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) (ExecRet, error) {
	isSuccess := false

	exec.NewEnv(exec.env)
	if glob.RequireMsg() {
		defer func() {
			exec.newMsg("\n")
			if isSuccess {
				exec.appendNewMsgAtBegin("is true\n")
			} else {
				exec.appendNewMsgAtBegin("is unknown\n")
			}
			exec.appendNewMsgAtBegin(stmt.ClaimProveStmt.String())
			exec.deleteEnvAndRetainMsg()
		}()
	}

	switch asStmt := stmt.ClaimProveStmt.ToCheckFact.(type) {
	case ast.Spec_OrFact:
		return exec.reversibleFactProveByContradiction(asStmt, stmt)
	case *ast.UniFactStmt:
		return exec.uniFactProveByContradiction(asStmt, stmt)
	default:
		return NewExecErr(""), fmt.Errorf("prove by contradiction only support reversible fact or uni fact")
	}
}

func (exec *Executor) reversibleFactProveByContradiction(specFactStmt ast.Spec_OrFact, stmt *ast.ClaimProveByContradictionStmt) (ExecRet, error) {
	reversedFact := specFactStmt.ReverseIsTrue()

	for _, curFact := range reversedFact {
		err := exec.env.NewFact(curFact)
		if err != nil {
			return NewExecErr(""), err
		}
	}

	execState, err := exec.execStmtsAtCurEnv(stmt.ClaimProveStmt.Proofs)
	if notOkExec(execState, err) {
		return execState, err
	}

	lastStmtAsFact, ok := stmt.ClaimProveStmt.Proofs[len(stmt.ClaimProveStmt.Proofs)-1].(ast.Spec_OrFact)
	if !ok {
		return NewExecErr(""), fmt.Errorf("prove by contradiction only support fact as last statement")
	}

	reversedLastFact := lastStmtAsFact.ReverseIsTrue()

	reversedLastFactStr := []string{"and:"}
	for _, curFact := range reversedLastFact {
		reversedLastFactStr = append(reversedLastFactStr, curFact.String())
	}
	reversedLastFactStrStr := strings.Join(reversedLastFactStr, "\n\t")

	exec.newMsg(fmt.Sprintf("the reversed last statement of current claim statement is:\n%s\nwe prove it(them)\n", reversedLastFactStrStr))

	for _, curFact := range reversedLastFact {
		execState, err = exec.factStmt(curFact)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	exec.newMsg(fmt.Sprintf("last statement of current claim statement:\n%s\nis true and false. Prove by contradiction is successful!", lastStmtAsFact))

	return NewExecTrue(""), nil
}

func (exec *Executor) uniFactProveByContradiction(specFactStmt *ast.UniFactStmt, stmt *ast.ClaimProveByContradictionStmt) (ExecRet, error) {
	ver := verifier.NewVerifier(exec.env)
	newStmtPtr, err := ver.PreprocessUniFactParams_DeclareParams(specFactStmt)
	if err != nil {
		return NewExecErr(""), err
	}

	// know cond facts
	for _, condFact := range newStmtPtr.DomFacts {
		err := exec.env.NewFact(condFact)
		if err != nil {
			return NewExecErr(""), err
		}
	}

	// know reversed then facts
	thenFactsAsReversibleFacts := []ast.Spec_OrFact{}
	for _, thenFact := range newStmtPtr.ThenFacts {
		if reversibleThenFact, ok := thenFact.(ast.Spec_OrFact); ok {
			thenFactsAsReversibleFacts = append(thenFactsAsReversibleFacts, reversibleThenFact)
		} else {
			return NewExecErr(""), fmt.Errorf("then fact:\n%s\nis not reversible. Then section of universal fact prove by contradiction only support reversible fact", thenFact)
		}
	}
	reversedThenFacts := ast.ReverseSliceOfReversibleFacts(thenFactsAsReversibleFacts)
	for _, reversedThenFact := range reversedThenFacts {
		err := exec.env.NewFact(reversedThenFact)
		if err != nil {
			return NewExecErr(""), err
		}
	}

	// run proof block
	execState, err := exec.execStmtsAtCurEnv(stmt.ClaimProveStmt.Proofs)
	if notOkExec(execState, err) {
		return execState, err
	}

	// the reversed last statement of current claim statement is true
	lastFact, ok := stmt.ClaimProveStmt.Proofs[len(stmt.ClaimProveStmt.Proofs)-1].(ast.Spec_OrFact)
	if !ok {
		return NewExecErr(""), fmt.Errorf("prove by contradiction only support fact")
	}

	reversedLastFact := lastFact.ReverseIsTrue()

	reversedLastFactStr := []string{}
	for _, curFact := range reversedLastFact {
		reversedLastFactStr = append(reversedLastFactStr, curFact.String())
	}
	reversedLastFactStrStr := strings.Join(reversedLastFactStr, "\n\t")
	exec.newMsg(fmt.Sprintf("the reversed last statement of current claim statement is(are):\n\n%s\n\nwe prove it(them)\n", reversedLastFactStrStr))

	for _, curFact := range reversedLastFact {
		execState, err = exec.factStmt(curFact)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	exec.newMsg(fmt.Sprintf("last statement of current claim statement:\n%s\nis true and false. Prove by contradiction is successful!", lastFact))

	return NewExecTrue(""), nil
}

func (exec *Executor) execClaimStmtProve(stmt *ast.ClaimProveStmt) (ExecRet, error) {
	state, err := exec.claimStmtProve(stmt)
	if notOkExec(state, err) {
		return state, err
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	err = exec.env.NewFact(stmt.ToCheckFact)
	if err != nil {
		return NewExecErr(""), err
	}
	// exec.knowStmt(ast.NewKnowStmt([]ast.CanBeKnownStmt{stmt.ToCheckFact}))

	return NewExecTrue(""), nil
}

func (exec *Executor) execClaimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) (ExecRet, error) {
	state, err := exec.claimStmtProveByContradiction(stmt)
	if notOkExec(state, err) {
		return state, err
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	exec.knowStmt(ast.NewKnowStmt([]ast.CanBeKnownStmt{stmt.ClaimProveStmt.ToCheckFact}, stmt.ClaimProveStmt.Line))

	return NewExecTrue(""), nil
}

func (exec *Executor) claimStmtProve(stmt *ast.ClaimProveStmt) (ExecRet, error) {
	err := error(nil)
	isSuccess := false

	exec.NewEnv(exec.env)
	if glob.RequireMsg() {
		defer func() {
			exec.deleteEnvAndRetainMsg()
		}()
	}

	// 需要检查stmt.ToCheckFact里的东西都是在外部声明好了的
	ok := exec.env.AreAtomsInFactAreDeclared(stmt.ToCheckFact, map[string]struct{}{})
	if !ok {
		return NewExecErr(""), fmt.Errorf(env.AtomsInFactNotDeclaredMsg(stmt.ToCheckFact))
	}

	switch stmt.ToCheckFact.(type) {
	case *ast.UniFactStmt:
		isSuccess, err = exec.claimStmtProveUniFact(stmt)
		if err != nil {
			return NewExecErr(""), err
		}
		if !isSuccess {
			return NewExecUnknown(""), nil
		}
		return NewExecTrue(""), nil
	default:
		execState, err := exec.execStmtsAtCurEnv(stmt.Proofs)
		if err != nil {
			return NewExecErr(""), err
		}
		if execState.IsUnknown() {
			return NewExecUnknown(""), nil
		}
		// check claim
		execState, err = exec.factStmt(stmt.ToCheckFact)
		if err != nil {
			return NewExecErr(""), err
		}
		if execState.IsUnknown() {
			return NewExecUnknown(""), nil
		}
		return NewExecTrue(""), nil
	}

}

// prove uniFact in claim at current env
func (exec *Executor) claimStmtProveUniFact(stmt *ast.ClaimProveStmt) (bool, error) {
	asUnivFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt)
	if !ok {
		return false, fmt.Errorf("claim stmt prove uni fact only support uni fact")
	}

	// declare parameters in asUnivFact in the env
	objDefStmt := ast.NewDefObjStmt(asUnivFact.Params, asUnivFact.ParamSets, []ast.FactStmt{}, stmt.Line)

	err := exec.defLetStmt(objDefStmt)
	if err != nil {
		if glob.RequireMsg() {
			exec.newMsg(fmt.Sprintf("Claim statement error: Failed to declare parameters in universal fact:\n%s\n", objDefStmt))
		}
		return false, err
	}

	// know dom facts
	for _, domFact := range asUnivFact.DomFacts {
		err = exec.env.NewFact(domFact)
		if err != nil {
			return false, err
		}
	}

	// exec proof block
	execState, err := exec.execStmtsAtCurEnv(stmt.Proofs)
	if err != nil {
		return false, err
	}
	if execState.IsUnknown() {
		return false, nil
	}

	// TODO: 让claim能forall if
	// if asUnivFact.IffFacts == nil || len(asUnivFact.IffFacts) == 0 {
	// execState, failedFact, err := verifier.ExecFactsAtCurEnv_retFailedFact(asUnivFact.ThenFacts, exec.env, verifier.Round0NoMsg)
	execState, failedFact, err := exec.verifyFactsAtCurEnv(asUnivFact.ThenFacts, verifier.Round0NoMsg)
	if err != nil {
		return false, fmt.Errorf("claim statement error: failed to verify fact:\n%s\n%s", failedFact, err)
	} else if execState.IsUnknown() {
		return false, fmt.Errorf("claim statement error: failed to verify fact:\n%s", failedFact)
	}

	return true, nil

}

// 也许我应该语义改成，先声明prop，然后再证明prop，而不是现在这个样子
func (exec *Executor) claimPropStmt(stmt *ast.ClaimPropStmt) (ExecRet, error) {
	var err error
	var execState ExecRet = NewExecErr("")

	// prop all atoms declared
	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.DomFacts, stmt.Prop.IffFacts, stmt.Line)
	if !exec.env.AreAtomsInFactAreDeclared(uniFact, map[string]struct{}{}) && !exec.env.IsFcAtomDeclaredByUser(ast.FcAtom(stmt.Prop.DefHeader.Name)) {
		return NewExecErr(""), fmt.Errorf("claim prop statement error: atoms in fact are not declared")
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
	err = exec.knowPropStmt(ast.NewKnowPropStmt(stmt.Prop, stmt.Line))
	if notOkExec(execState, err) {
		return execState, err
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) claimExistPropStmt(stmt *ast.ClaimExistPropStmt) (ExecRet, error) {
	execState, err := exec.claimExistPropStmtCheckProofs(stmt)
	if notOkExec(execState, err) {
		return execState, err
	}

	// declare exist prop
	err = exec.defExistPropStmt(stmt.ExistPropWithoutDom)
	if err != nil {
		return NewExecErr(""), err
	}

	// know forall
	uniFact := ast.NewUniFact(stmt.ExistPropWithoutDom.DefBody.DefHeader.Params, stmt.ExistPropWithoutDom.DefBody.DefHeader.ParamSets, stmt.ExistPropWithoutDom.DefBody.IffFacts, []ast.FactStmt{stmt.ExistPropWithoutDom.DefBody.DefHeader.ToSpecFact()}, stmt.Line)
	err = exec.env.NewFact(uniFact)
	if err != nil {
		return NewExecErr(""), err
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) claimExistPropStmtCheckProofs(stmt *ast.ClaimExistPropStmt) (ExecRet, error) {
	exec.NewEnv(exec.env)
	defer func() {
		exec.deleteEnvAndRetainMsg()
	}()

	// declare parameters in exist prop
	defObjStmt := ast.NewDefObjStmt(stmt.ExistPropWithoutDom.DefBody.DefHeader.Params, stmt.ExistPropWithoutDom.DefBody.DefHeader.ParamSets, stmt.ExistPropWithoutDom.DefBody.IffFacts, stmt.Line)

	err := exec.defLetStmt(defObjStmt)
	if err != nil {
		return NewExecErr(""), err
	}

	for _, curStmt := range stmt.Proofs {
		execState, _, err := exec.Stmt(curStmt)
		if notOkExec(execState, err) {
			if glob.RequireMsg() {
				if execState.IsUnknown() {
					exec.env.AddMsgToParent(fmt.Sprintf("unknown :( line %d\n", curStmt.GetLine()))
				} else {
					exec.env.AddMsgToParent(fmt.Sprintf("failed :( line %d:\n", curStmt.GetLine()))
				}
			}
			return execState, err
		}
	}

	// 把haveObj 代入 existParams 看看是否真的符合 then
	if len(stmt.HaveObj) != len(stmt.ExistPropWithoutDom.ExistParams) {
		return NewExecErr(""), fmt.Errorf("claim exist prop statement error: have obj length is not equal to exist params length")
	}

	uniMap := make(map[string]ast.Fc)
	for i, haveObj := range stmt.HaveObj {
		uniMap[stmt.ExistPropWithoutDom.ExistParams[i]] = haveObj
	}

	for _, fact := range stmt.ExistPropWithoutDom.DefBody.ThenFacts {
		instFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return NewExecErr(""), err
		}
		execState, err := exec.factStmt(instFact)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) checkClaimPropStmtProofs(stmt *ast.ClaimPropStmt) (ExecRet, error) {
	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.IffFacts, stmt.Prop.ThenFacts, stmt.Line)

	exec.NewEnv(exec.env)
	defer func() {
		exec.deleteEnvAndRetainMsg()
	}()

	ok, err := exec.claimStmtProveUniFact(ast.NewClaimProveStmt(uniFact, stmt.Proofs, stmt.Line))
	if err != nil {
		return NewExecErr(""), err
	}
	if !ok {
		return NewExecUnknown(""), nil
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) checkClaimPropStmtProveByContradiction(stmt *ast.ClaimPropStmt) (ExecRet, error) {
	exec.NewEnv(exec.env)
	defer func() {
		exec.deleteEnvAndRetainMsg()
	}()

	// declare parameters in prop

	objDefStmt := ast.NewDefObjStmt(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.IffFacts, stmt.Line)
	err := exec.defLetStmt(objDefStmt)
	if err != nil {
		return NewExecErr(""), err
	}

	thenFactsAsReversible := []ast.Spec_OrFact{}
	for _, fact := range stmt.Prop.ThenFacts {
		asReversible, ok := fact.(ast.Spec_OrFact)
		if !ok {
			return NewExecErr(""), fmt.Errorf("claim prop statement error: then fact is not an or statement")
		}
		thenFactsAsReversible = append(thenFactsAsReversible, asReversible)
	}

	// assume reverse of all then facts in prop or true
	reversedThenFacts := ast.ReverseSliceOfReversibleFacts(thenFactsAsReversible)
	for _, fact := range reversedThenFacts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return NewExecErr(""), err
		}
	}

	execState, err := exec.execStmtsAtCurEnv(stmt.Proofs)
	if notOkExec(execState, err) {
		return execState, err
	}

	// 最后一项的逆也对
	lastProof := stmt.Proofs[len(stmt.Proofs)-1]
	lastProofAsReversible, ok := lastProof.(ast.Spec_OrFact)
	if !ok {
		return NewExecErr(""), fmt.Errorf("claim prop statement error: last proof is not an or statement")
	}

	reverseLastProof := lastProofAsReversible.ReverseIsTrue()
	reverseLastProofAsFacts := []ast.FactStmt{}
	for _, fact := range reverseLastProof {
		reverseLastProofAsFacts = append(reverseLastProofAsFacts, fact)
	}
	// execState, failedFact, err := verifier.(reverseLastProof, exec.env)
	execState, failedFact, err := exec.verifyFactsAtCurEnv(reverseLastProofAsFacts, verifier.Round0NoMsg)
	if err != nil {
		return execState, fmt.Errorf("claim prop statement error: failed to verify reverse of last proof:\n%s\n%s", failedFact, err)
	} else if execState.IsUnknown() {
		return execState, fmt.Errorf("claim prop statement error: failed to verify reverse of last proof:\n%s", failedFact)
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) claimIffStmt(stmt *ast.ClaimIffStmt) (ExecRet, error) {
	thenToIff := stmt.UniFactWithIffStmt.NewUniFactWithThenToIff()
	iffToThen := stmt.UniFactWithIffStmt.NewUniFactWithIffToThen()
	claimThenToIff := ast.NewClaimProveStmt(thenToIff, stmt.ProofThenToIff, stmt.Line)
	claimIffToThen := ast.NewClaimProveStmt(iffToThen, stmt.ProofIffToThen, stmt.Line)
	execState, err := exec.claimStmtProve(claimThenToIff)
	if notOkExec(execState, err) {
		return execState, err
	}
	execState, err = exec.claimStmtProve(claimIffToThen)
	if notOkExec(execState, err) {
		return execState, err
	}

	err = exec.env.NewFact(thenToIff)
	if err != nil {
		return NewExecErr(""), err
	}
	err = exec.env.NewFact(iffToThen)
	if err != nil {
		return NewExecErr(""), err
	}

	return NewExecTrue(""), nil
}
