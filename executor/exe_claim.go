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

func (exec *Executor) claimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) (glob.ExecState, error) {
	isSuccess := false

	exec.newEnv(exec.env)
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
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction only support reversible fact or uni fact")
	}
}

func (exec *Executor) reversibleFactProveByContradiction(specFactStmt ast.Spec_OrFact, stmt *ast.ClaimProveByContradictionStmt) (glob.ExecState, error) {
	reversedFact := specFactStmt.ReverseIsTrue()

	for _, curFact := range reversedFact {
		err := exec.env.NewFact(curFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	execState, err := exec.execStmtsAtCurEnv(stmt.ClaimProveStmt.Proofs)
	if notOkExec(execState, err) {
		return execState, err
	}

	lastStmtAsFact, ok := stmt.ClaimProveStmt.Proofs[len(stmt.ClaimProveStmt.Proofs)-1].(ast.Spec_OrFact)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction only support fact")
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

	return glob.ExecState_True, nil
}

func (exec *Executor) uniFactProveByContradiction(specFactStmt *ast.UniFactStmt, stmt *ast.ClaimProveByContradictionStmt) (glob.ExecState, error) {
	ver := verifier.NewVerifier(exec.env)
	newStmtPtr, err := ver.PreprocessUniFactParams_DeclareParams(specFactStmt)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// know cond facts
	for _, condFact := range newStmtPtr.DomFacts {
		err := exec.env.NewFact(condFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// know reversed then facts
	thenFactsAsReversibleFacts := []ast.Spec_OrFact{}
	for _, thenFact := range newStmtPtr.ThenFacts {
		if reversibleThenFact, ok := thenFact.(ast.Spec_OrFact); ok {
			thenFactsAsReversibleFacts = append(thenFactsAsReversibleFacts, reversibleThenFact)
		} else {
			return glob.ExecState_Error, fmt.Errorf("then fact:\n%s\nis not reversible. Then section of universal fact prove by contradiction only support reversible fact", thenFact)
		}
	}
	reversedThenFacts := ast.ReverseSliceOfReversibleFacts(thenFactsAsReversibleFacts)
	for _, reversedThenFact := range reversedThenFacts {
		err := exec.env.NewFact(reversedThenFact)
		if err != nil {
			return glob.ExecState_Error, err
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
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction only support fact")
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

	return glob.ExecState_True, nil
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

func (exec *Executor) claimStmtProve(stmt *ast.ClaimProveStmt) (glob.ExecState, error) {
	err := error(nil)
	isSuccess := false

	exec.newEnv(exec.env)
	if glob.RequireMsg() {
		defer func() {
			exec.newMsg("\n")
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
		execState, err := exec.execStmtsAtCurEnv(stmt.Proofs)
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

// prove uniFact in claim at current env
func (exec *Executor) claimStmtProveUniFact(stmt *ast.ClaimProveStmt) (bool, error) {
	asUnivFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt)
	if !ok {
		return false, fmt.Errorf("claim stmt prove uni fact only support uni fact")
	}

	// declare parameters in asUnivFact in the env
	objDefStmt := ast.NewDefObjStmt(asUnivFact.Params, asUnivFact.ParamSets, []ast.FactStmt{})
	err := exec.defObjStmt(objDefStmt, false)
	if err != nil {
		if glob.RequireMsg() {
			exec.newMsg(fmt.Sprintf("Claim statement error: Failed to declare parameters in universal fact:\n%s\n", objDefStmt))
		}
		return false, err
	}

	// know dom facts
	err = exec.knowStmt(ast.NewKnowStmt(asUnivFact.DomFacts))
	if err != nil {
		return false, err
	}

	// exec proof block
	execState, err := exec.execStmtsAtCurEnv(stmt.Proofs)
	if err != nil {
		if glob.RequireMsg() {
			exec.newMsg(fmt.Sprintf("Claim statement error: Failed to execute proof block:\n%s\n", stmt))
		}
		return false, err
	}
	if execState != glob.ExecState_True {
		return false, nil
	}

	// TODO: 让claim能forall if
	// if asUnivFact.IffFacts == nil || len(asUnivFact.IffFacts) == 0 {
	execState, failedFact, err := verifier.ExecFactsAtCurEnv_retRailedFact(asUnivFact.ThenFacts, exec.env)
	if err != nil {
		return false, fmt.Errorf("claim statement error: failed to verify fact:\n%s\n%s", failedFact, err)
	} else if execState != glob.ExecState_True {
		return false, fmt.Errorf("claim statement error: failed to verify fact:\n%s", failedFact)
	}

	return true, nil

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

func (exec *Executor) claimExistPropStmt(stmt *ast.ClaimExistPropStmt) (glob.ExecState, error) {
	return exec.checkClaimExistPropStmtProofs(stmt)
}

func (exec *Executor) checkClaimExistPropStmtProofs(stmt *ast.ClaimExistPropStmt) (glob.ExecState, error) {
	panic("not implemented")
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

	thenFactsAsReversible := []ast.Spec_OrFact{}
	for _, fact := range stmt.Prop.ThenFacts {
		asReversible, ok := fact.(ast.Spec_OrFact)
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

	execState, err := exec.execStmtsAtCurEnv(stmt.Proofs)
	if notOkExec(execState, err) {
		return execState, err
	}

	// 最后一项的逆也对
	lastProof := stmt.Proofs[len(stmt.Proofs)-1]
	lastProofAsReversible, ok := lastProof.(ast.Spec_OrFact)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("claim prop statement error: last proof is not an or statement")
	}

	reverseLastProof := lastProofAsReversible.ReverseIsTrue()
	execState, failedFact, err := verifier.ExecSpecFactsAtCurEnv_retRailedFact(reverseLastProof, exec.env)
	if err != nil {
		return execState, fmt.Errorf("claim prop statement error: failed to verify reverse of last proof:\n%s\n%s", failedFact, err)
	} else if execState != glob.ExecState_True {
		return execState, fmt.Errorf("claim prop statement error: failed to verify reverse of last proof:\n%s", failedFact)
	}

	return glob.ExecState_True, nil
}
