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
	"strings"
)

func (exec *Executor) claimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) ExecRet {
	isSuccess := false

	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	var result ExecRet
	switch asStmt := stmt.ClaimProveStmt.ToCheckFact.(type) {
	case ast.Spec_OrFact:
		execState := exec.reversibleFactProveByContradiction(asStmt, stmt)
		if execState.IsNotTrue() {
			return execState
		}
		result = NewExecTrue("")
	case *ast.UniFactStmt:
		execState := exec.uniFactProveByContradiction(asStmt, stmt)
		if execState.IsNotTrue() {
			return execState
		}
		result = NewExecTrue("")
		isSuccess = true
	default:
		return NewExecErr(fmt.Errorf("prove by contradiction only support reversible fact or uni fact").Error())
	}

	// Add messages in correct order
	result = result.AddMsg("\n")
	if isSuccess {
		result = result.AddMsgAtBegin("is true\n")
	} else {
		result = result.AddMsgAtBegin("is unknown\n")
	}
	result = result.AddMsgAtBegin(stmt.ClaimProveStmt.String())
	return result
}

func (exec *Executor) reversibleFactProveByContradiction(specFactStmt ast.Spec_OrFact, stmt *ast.ClaimProveByContradictionStmt) ExecRet {
	reversedFact := specFactStmt.ReverseIsTrue()

	for _, curFact := range reversedFact {
		ret := exec.Env.NewFact(curFact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	execState := exec.execStmtsAtCurEnv(stmt.ClaimProveStmt.Proofs)
	if execState.IsNotTrue() {
		return execState
	}

	lastStmtAsFact, ok := stmt.ClaimProveStmt.Proofs[len(stmt.ClaimProveStmt.Proofs)-1].(ast.Spec_OrFact)
	if !ok {
		return NewExecErr("prove by contradiction only support fact as last statement")
	}

	reversedLastFact := lastStmtAsFact.ReverseIsTrue()

	reversedLastFactStr := []string{}
	for _, curFact := range reversedLastFact {
		reversedLastFactStr = append(reversedLastFactStr, curFact.String())
	}
	reversedLastFactStrStr := strings.Join(reversedLastFactStr, "\n\t")

	for _, curFact := range reversedLastFact {
		execState := exec.factStmt(curFact)
		if execState.IsNotTrue() {
			return execState
		}
	}

	result := NewExecTrue("")
	result = result.AddMsg(fmt.Sprintf("the reversed last statement of current claim statement is:\n%s\nwe prove it(them)\n", reversedLastFactStrStr))
	result = result.AddMsg(fmt.Sprintf("last statement of current claim statement:\n%s\nis true and false. Prove by contradiction is successful!", lastStmtAsFact))
	return result
}

func (exec *Executor) uniFactProveByContradiction(specFactStmt *ast.UniFactStmt, stmt *ast.ClaimProveByContradictionStmt) ExecRet {
	ver := NewVerifier(exec.Env)
	newStmtPtr, err := ver.PreprocessUniFactParams_DeclareParams(specFactStmt)
	if err != nil {
		return NewExecErr(err.Error())
	}

	// know cond facts
	for _, condFact := range newStmtPtr.DomFacts {
		ret := exec.Env.NewFact(condFact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	// know reversed then facts
	thenFactsAsReversibleFacts := []ast.Spec_OrFact{}
	for _, thenFact := range newStmtPtr.ThenFacts {
		if reversibleThenFact, ok := thenFact.(ast.Spec_OrFact); ok {
			thenFactsAsReversibleFacts = append(thenFactsAsReversibleFacts, reversibleThenFact)
		} else {
			return NewExecErr(fmt.Errorf("then fact:\n%s\nis not reversible. Then section of universal fact prove by contradiction only support reversible fact", thenFact).Error())
		}
	}
	reversedThenFacts := ast.ReverseSliceOfReversibleFacts(thenFactsAsReversibleFacts)
	for _, reversedThenFact := range reversedThenFacts {
		ret := exec.Env.NewFact(reversedThenFact.(ast.FactStmt))
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	// run proof block
	execState := exec.execStmtsAtCurEnv(stmt.ClaimProveStmt.Proofs)
	if execState.IsNotTrue() {
		return execState
	}

	// the reversed last statement of current claim statement is true
	lastFact, ok := stmt.ClaimProveStmt.Proofs[len(stmt.ClaimProveStmt.Proofs)-1].(ast.Spec_OrFact)
	if !ok {
		return NewExecErr(fmt.Errorf("prove by contradiction only support fact").Error())
	}

	reversedLastFact := lastFact.ReverseIsTrue()

	reversedLastFactStr := []string{}
	for _, curFact := range reversedLastFact {
		reversedLastFactStr = append(reversedLastFactStr, curFact.String())
	}
	reversedLastFactStrStr := strings.Join(reversedLastFactStr, "\n\t")

	for _, curFact := range reversedLastFact {
		execState = exec.factStmt(curFact)
		if execState.IsNotTrue() {
			return execState
		}
	}

	result := NewExecTrue("")
	result = result.AddMsg(fmt.Sprintf("the reversed last statement of current claim statement is(are):\n\n%s\n\nwe prove it(them)\n", reversedLastFactStrStr))
	result = result.AddMsg(fmt.Sprintf("last statement of current claim statement:\n%s\nis true and false. Prove by contradiction is successful!", lastFact))
	return result
}

func (exec *Executor) execClaimStmtProve(stmt *ast.ClaimProveStmt) ExecRet {
	state := exec.claimStmtProve(stmt)
	if state.IsNotTrue() {
		return state
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	ret := exec.Env.NewFact(stmt.ToCheckFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}
	// exec.knowStmt(ast.NewKnowStmt([]ast.CanBeKnownStmt{stmt.ToCheckFact}))

	return NewExecTrue("")
}

func (exec *Executor) execClaimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) ExecRet {
	state := exec.claimStmtProveByContradiction(stmt)
	if state.IsNotTrue() {
		return state
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	execRet := exec.knowStmt(ast.NewKnowStmt([]ast.CanBeKnownStmt{stmt.ClaimProveStmt.ToCheckFact.(ast.CanBeKnownStmt)}, stmt.ClaimProveStmt.Line))
	if execRet.IsNotTrue() {
		return execRet
	}

	return execRet
}

func (exec *Executor) claimStmtProve(stmt *ast.ClaimProveStmt) ExecRet {
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	// 需要检查stmt.ToCheckFact里的东西都是在外部声明好了的
	ret := exec.Env.AreAtomsInFactAreDeclared(stmt.ToCheckFact, map[string]struct{}{})
	if ret.IsErr() {
		ret.AddMsg("in claim statement")
		return NewExecErr(ret.String())
	}

	switch stmt.ToCheckFact.(type) {
	case *ast.UniFactStmt:
		isSuccess := exec.claimStmtProveUniFact(stmt)
		if isSuccess.IsNotTrue() {
			return isSuccess
		}
		return NewExecTrue("")
	default:
		execState := exec.execStmtsAtCurEnv(stmt.Proofs)
		if execState.IsNotTrue() {
			return execState
		}
		// check claim
		execState = exec.factStmt(stmt.ToCheckFact)
		if execState.IsNotTrue() {
			return execState
		}
		return NewExecTrue("")
	}

}

// prove uniFact in claim at current env
func (exec *Executor) claimStmtProveUniFact(stmt *ast.ClaimProveStmt) ExecRet {
	asUnivFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt)
	if !ok {
		return NewExecErr(fmt.Errorf("claim stmt prove uni fact only support uni fact").Error())
	}

	// declare parameters in asUnivFact in the env
	objDefStmt := ast.NewDefLetStmt(asUnivFact.Params, asUnivFact.ParamSets, []ast.FactStmt{}, stmt.Line)

	execState := exec.defLetStmt(objDefStmt)
	if execState.IsNotTrue() {
		return execState.AddMsg(fmt.Sprintf("Claim statement error: Failed to declare parameters in universal fact:\n%s\n", objDefStmt))
	}

	// know dom facts
	for _, domFact := range asUnivFact.DomFacts {
		ret := exec.Env.NewFact(domFact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	// exec proof block
	execState = exec.execStmtsAtCurEnv(stmt.Proofs)
	if execState.IsNotTrue() {
		return execState
	}

	// TODO: 让claim能forall if
	// if asUnivFact.IffFacts == nil || len(asUnivFact.IffFacts) == 0 {
	// execState, failedFact, err := verifier.ExecFactsAtCurEnv_retFailedFact(asUnivFact.ThenFacts, exec.env, verifier.Round0NoMsg)
	execState, failedFact, err := exec.verifyFactsAtCurEnv(asUnivFact.ThenFacts, Round0NoMsg)
	if err != nil {
		return NewExecErr(fmt.Errorf("claim statement error: failed to verify fact:\n%s\n%s", failedFact, err).Error())
	} else if execState.IsUnknown() {
		return NewExecErr(fmt.Errorf("claim statement error: failed to verify fact:\n%s", failedFact).Error())
	}

	return NewExecTrue("")

}

// 也许我应该语义改成，先声明prop，然后再证明prop，而不是现在这个样子
func (exec *Executor) claimPropStmt(stmt *ast.ClaimPropStmt) ExecRet {
	// prop all atoms declared
	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.DomFacts, stmt.Prop.IffFacts, stmt.Line)
	ret := exec.Env.AreAtomsInFactAreDeclared(uniFact, map[string]struct{}{})
	if ret.IsErr() && !exec.Env.IsFcAtomDeclaredByUser(ast.Atom(stmt.Prop.DefHeader.Name)) {
		ret.AddMsg("in claim prop statement")
		return NewExecErr(ret.String())
	}

	// check proofs
	// if stmt.IsProve {
	execState := exec.checkClaimPropStmtProofs(stmt)
	if execState.IsNotTrue() {
		return execState
	}
	// } else {
	// 	execState := exec.checkClaimPropStmtProveByContradiction(stmt)
	// 	if execState.IsNotTrue() {
	// 		return execState
	// 	}
	// }

	// know exec
	execRet := exec.knowPropStmt(ast.NewKnowPropStmt(stmt.Prop, stmt.Line))
	if execRet.IsNotTrue() {
		return execRet
	}

	return execRet
}

func (exec *Executor) claimExistPropStmt(stmt *ast.ClaimExistPropStmt) ExecRet {
	execState := exec.claimExistPropStmtCheckProofs(stmt)
	if execState.IsNotTrue() {
		return execState
	}

	// declare exist prop
	execState = exec.defExistPropStmt(stmt.ExistPropWithoutDom)
	if execState.IsNotTrue() {
		return execState
	}

	// know forall
	uniFact := ast.NewUniFact(stmt.ExistPropWithoutDom.DefBody.DefHeader.Params, stmt.ExistPropWithoutDom.DefBody.DefHeader.ParamSets, stmt.ExistPropWithoutDom.DefBody.IffFacts, []ast.FactStmt{stmt.ExistPropWithoutDom.DefBody.DefHeader.ToSpecFact()}, stmt.Line)
	ret := exec.Env.NewFact(uniFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue("")
}

func (exec *Executor) claimExistPropStmtCheckProofs(stmt *ast.ClaimExistPropStmt) ExecRet {
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	// declare parameters in exist prop
	defObjStmt := ast.NewDefLetStmt(stmt.ExistPropWithoutDom.DefBody.DefHeader.Params, stmt.ExistPropWithoutDom.DefBody.DefHeader.ParamSets, stmt.ExistPropWithoutDom.DefBody.IffFacts, stmt.Line)

	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	for _, curStmt := range stmt.Proofs {
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			if execState.IsUnknown() {
				return execState.AddMsg(fmt.Sprintf("unknown :( line %d\n", curStmt.GetLine()))
			} else {
				return execState.AddMsg(fmt.Sprintf("failed :( line %d:\n", curStmt.GetLine()))
			}
		}
	}

	// 把haveObj 代入 existParams 看看是否真的符合 then
	if len(stmt.HaveObj) != len(stmt.ExistPropWithoutDom.ExistParams) {
		return NewExecErr(fmt.Errorf("claim exist prop statement error: have obj length is not equal to exist params length").Error())
	}

	uniMap := make(map[string]ast.Obj)
	for i, haveObj := range stmt.HaveObj {
		uniMap[stmt.ExistPropWithoutDom.ExistParams[i]] = haveObj
	}

	for _, fact := range stmt.ExistPropWithoutDom.DefBody.ThenFacts {
		instFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return NewExecErr(err.Error())
		}
		execState := exec.factStmt(instFact)
		if execState.IsErr() {
			return execState
		}
		if notOkExec(execState, err) {
			return execState
		}
	}

	return NewExecTrue("")
}

func (exec *Executor) checkClaimPropStmtProofs(stmt *ast.ClaimPropStmt) ExecRet {
	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.IffFacts, stmt.Prop.ThenFacts, stmt.Line)

	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	execRet := exec.claimStmtProveUniFact(ast.NewClaimProveStmt(uniFact, stmt.Proofs, stmt.Line))
	if execRet.IsNotTrue() {
		return execRet
	}

	return NewExecTrue("")
}

func (exec *Executor) claimIffStmt(stmt *ast.ClaimIffStmt) ExecRet {
	thenToIff := stmt.UniFactWithIffStmt.NewUniFactWithThenToIff()
	iffToThen := stmt.UniFactWithIffStmt.NewUniFactWithIffToThen()
	claimThenToIff := ast.NewClaimProveStmt(thenToIff, stmt.ProofThenToIff, stmt.Line)
	claimIffToThen := ast.NewClaimProveStmt(iffToThen, stmt.ProofIffToThen, stmt.Line)
	execState := exec.claimStmtProve(claimThenToIff)
	if execState.IsNotTrue() {
		return execState
	}
	execState = exec.claimStmtProve(claimIffToThen)
	if execState.IsNotTrue() {
		return execState
	}

	ret := exec.Env.NewFact(thenToIff)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}
	ret = exec.Env.NewFact(iffToThen)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue("")
}
