// Copyright Jiachen Shen.
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

func (exec *Executor) claimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) *glob.StmtRet {
	// isSuccess := false

	exec.NewEnv()
	defer exec.deleteEnv()

	var result *glob.StmtRet
	switch asStmt := stmt.ClaimProveStmt.ToCheckFact.(type) {
	case ast.Spec_OrFact:
		execState := exec.reversibleFactProveByContradiction(asStmt, stmt)
		if execState.IsNotTrue() {
			return execState
		}
		result = execState
	case *ast.UniFactStmt:
		execState := exec.uniFactProveByContradiction(asStmt, stmt)
		if execState.IsNotTrue() {
			return execState
		}
		result = execState
		// isSuccess = true
	default:
		return glob.ErrRet(fmt.Sprintf("prove by contradiction only support reversible fact or uni fact"))
	}

	// Add messages in correct order
	// result = result.AddMsg("\n")
	// if isSuccess {
	// 	result = result.AddMsgAtBegin("is true\n")
	// } else {
	// 	result = result.AddMsgAtBegin("is unknown\n")
	// }

	return exec.AddStmtToStmtRet(result, stmt.ClaimProveStmt)
}

func (exec *Executor) reversibleFactProveByContradiction(specFactStmt ast.Spec_OrFact, stmt *ast.ClaimProveByContradictionStmt) *glob.StmtRet {
	innerStmtRets := []*glob.StmtRet{}

	reversedFact := specFactStmt.ReverseIsTrue()

	for _, curFact := range reversedFact {
		ret := exec.Env.NewFactWithCheckingNameDefined(curFact)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
	}

	execState := exec.execStmtsAtCurEnv(stmt.ClaimProveStmt.Proofs)
	if execState.IsNotTrue() {
		return execState
	}
	innerStmtRets = append(innerStmtRets, execState.InnerStmtRetSlice...)

	lastStmtAsFact, ok := stmt.ClaimProveStmt.Proofs[len(stmt.ClaimProveStmt.Proofs)-1].(ast.Spec_OrFact)
	if !ok {
		return glob.ErrRet("prove by contradiction only support fact as last statement")
	}

	reversedLastFact := lastStmtAsFact.ReverseIsTrue()

	reversedLastFactStr := []string{}
	for _, curFact := range reversedLastFact {
		reversedLastFactStr = append(reversedLastFactStr, curFact.String())
	}
	// reversedLastFactStrStr := strings.Join(reversedLastFactStr, "\n\t")

	for _, curFact := range reversedLastFact {
		execState := exec.factStmt(curFact)
		if execState.IsNotTrue() {
			return execState
		}
		innerStmtRets = append(innerStmtRets, execState)
	}

	return glob.NewStmtWithInnerStmtsRet(innerStmtRets, glob.StmtRetTypeTrue)
}

func (exec *Executor) uniFactProveByContradiction(specFactStmt *ast.UniFactStmt, stmt *ast.ClaimProveByContradictionStmt) *glob.StmtRet {
	innerStmtRets := []*glob.StmtRet{}

	ver := NewVerifier(exec.Env)
	newStmtPtr, err := ver.PreprocessUniFactParams_DeclareParams(specFactStmt)
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	// know cond facts
	for _, condFact := range newStmtPtr.DomFacts {
		ret := exec.Env.NewFactWithCheckingNameDefined(condFact)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
	}

	// know reversed then facts
	thenFactsAsReversibleFacts := []ast.Spec_OrFact{}
	for _, thenFact := range newStmtPtr.ThenFacts {
		if reversibleThenFact, ok := thenFact.(ast.Spec_OrFact); ok {
			thenFactsAsReversibleFacts = append(thenFactsAsReversibleFacts, reversibleThenFact)
		} else {
			return glob.ErrRet(fmt.Sprintf("then fact:\n%s\nis not reversible. Then section of universal fact prove by contradiction only support reversible fact", thenFact))
		}
	}
	reversedThenFacts := ast.ReverseSliceOfReversibleFacts(thenFactsAsReversibleFacts)
	for _, reversedThenFact := range reversedThenFacts {
		ret := exec.Env.NewFactWithCheckingNameDefined(reversedThenFact.(ast.FactStmt))
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
	}

	// run proof block
	execState := exec.execStmtsAtCurEnv(stmt.ClaimProveStmt.Proofs)
	if execState.IsNotTrue() {
		return execState
	}
	innerStmtRets = append(innerStmtRets, execState.InnerStmtRetSlice...)

	// the reversed last statement of current claim statement is true
	lastFact, ok := stmt.ClaimProveStmt.Proofs[len(stmt.ClaimProveStmt.Proofs)-1].(ast.Spec_OrFact)
	if !ok {
		return glob.ErrRet(fmt.Sprintf("prove by contradiction only support fact"))
	}

	reversedLastFact := lastFact.ReverseIsTrue()

	reversedLastFactStr := []string{}
	for _, curFact := range reversedLastFact {
		reversedLastFactStr = append(reversedLastFactStr, curFact.String())
	}

	for _, curFact := range reversedLastFact {
		execState = exec.factStmt(curFact)
		if execState.IsNotTrue() {
			return execState
		}
		innerStmtRets = append(innerStmtRets, execState)
	}

	return glob.NewStmtWithInnerStmtsRet(innerStmtRets, glob.StmtRetTypeTrue)
}

func (exec *Executor) execClaimStmtProve(stmt *ast.ClaimProveStmt) *glob.StmtRet {
	state := exec.claimStmtProve(stmt)
	if state.IsNotTrue() {
		return state
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.ToCheckFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	// exec.knowStmt(ast.NewKnowStmt([]ast.CanBeKnownStmt{stmt.ToCheckFact}))

	if ret.IsNotTrue() {
		return glob.NewStmtWithInnerStmtsRet(state.InnerStmtRetSlice, ret.RetType)
	} else {
		return glob.NewStmtWithInnerStmtsRet(state.InnerStmtRetSlice, ret.RetType)
	}

}

func (exec *Executor) execClaimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) *glob.StmtRet {
	state := exec.claimStmtProveByContradiction(stmt)
	if state.IsNotTrue() {
		return state
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.ClaimProveStmt.ToCheckFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(state.InnerStmtRetSlice)
}

func (exec *Executor) execImpossibleStmt(stmt *ast.ImpossibleStmt) *glob.StmtRet {
	state := exec.impossibleStmt(stmt)
	if state.IsNotTrue() {
		return state
	}

	// 检查 stmt fact 中的所有元素已经定义过了
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.Fact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(state.InnerStmtRetSlice)
}

func (exec *Executor) impossibleStmt(stmt *ast.ImpossibleStmt) *glob.StmtRet {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// 需要检查 stmt.Fact 里的东西都是在外部声明好了的
	ret := exec.Env.LookUpNamesInFact(stmt.Fact, map[string]struct{}{})
	if ret.IsErr() {
		ret.AddError("in impossible statement")
		return glob.ErrRet(ret.String())
	}

	innerStmtRets := []*glob.StmtRet{}
	execState := exec.execStmtsAtCurEnv(stmt.Proofs)
	if execState.IsNotTrue() {
		return execState
	}
	innerStmtRets = append(innerStmtRets, execState.InnerStmtRetSlice...)

	// check that the fact is impossible (i.e., its negation is true)
	execState = exec.factStmt(stmt.Fact)
	if execState.IsTrue() {
		// If the fact is true, then it's not impossible - this is an error
		return glob.ErrRet(fmt.Sprintf("impossible statement error: the fact is actually true, not impossible:\n%s", stmt.Fact))
	}
	if execState.IsUnknown() {
		return glob.ErrRet(fmt.Sprintf("impossible statement error: cannot determine if the fact is impossible:\n%s", stmt.Fact))
	}
	// If execState.IsNotTrue(), then the fact is indeed impossible, which is what we want
	innerStmtRets = append(innerStmtRets, execState)
	return glob.NewStmtWithInnerStmtsRet(innerStmtRets, glob.StmtRetTypeTrue)
}

func (exec *Executor) claimStmtProve(stmt *ast.ClaimProveStmt) *glob.StmtRet {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	// 需要检查stmt.ToCheckFact里的东西都是在外部声明好了的
	ret := exec.Env.LookUpNamesInFact(stmt.ToCheckFact, map[string]struct{}{})
	if ret.IsErr() {
		ret.AddError("in claim statement")
		return glob.ErrRet(ret.String())
	}

	switch stmt.ToCheckFact.(type) {
	case *ast.UniFactStmt:
		isSuccess := exec.claimStmtProveUniFact(stmt)
		if isSuccess.IsNotTrue() {
			return isSuccess
		}
		return isSuccess
	default:
		innerStmtRets := []*glob.StmtRet{}
		execState := exec.execStmtsAtCurEnv(stmt.Proofs)
		if execState.IsNotTrue() {
			return execState
		}
		innerStmtRets = append(innerStmtRets, execState.InnerStmtRetSlice...)
		// check claim
		execState = exec.factStmt(stmt.ToCheckFact)
		if execState.IsNotTrue() {
			return execState
		}
		innerStmtRets = append(innerStmtRets, execState)
		return glob.NewStmtWithInnerStmtsRet(innerStmtRets, glob.StmtRetTypeTrue)
	}

}

// prove uniFact in claim at current env
func (exec *Executor) claimStmtProveUniFact(stmt *ast.ClaimProveStmt) *glob.StmtRet {
	asUnivFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt)
	if !ok {
		return glob.ErrRet(fmt.Sprintf("claim stmt prove uni fact only support uni fact"))
	}

	innerStmtRets := []*glob.StmtRet{}

	// declare parameters in asUnivFact in the env
	objDefStmt := ast.NewDefLetStmt(asUnivFact.Params, asUnivFact.ParamSets, []ast.FactStmt{}, stmt.Line)

	execState := exec.defLetStmt(objDefStmt)
	if execState.IsNotTrue() {
		return execState.AddError(fmt.Sprintf("Claim statement error: Failed to declare parameters in universal fact:\n%s\n", objDefStmt))
	}
	innerStmtRets = append(innerStmtRets, execState)

	// know dom facts
	for _, domFact := range asUnivFact.DomFacts {
		ret := exec.Env.NewFactWithCheckingNameDefined(domFact)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
	}

	// exec proof block
	execState = exec.execStmtsAtCurEnv(stmt.Proofs)
	if execState.IsNotTrue() {
		return execState
	}
	innerStmtRets = append(innerStmtRets, execState.InnerStmtRetSlice...)

	// TODO: 让claim能forall if
	// if asUnivFact.IffFacts == nil || len(asUnivFact.IffFacts) == 0 {
	// execState, failedFact, err := verifier.ExecFactsAtCurEnv_retFailedFact(asUnivFact.ThenFacts, exec.env, verifier.Round0NoMsg)
	execState, failedFact, err := exec.verifyFactsAtCurEnv(asUnivFact.ThenFacts, Round0NoMsg())
	if err != nil {
		return glob.ErrRet(fmt.Sprintf("claim statement error: failed to verify fact:\n%s\n%s", failedFact, err))
	} else if execState.IsUnknown() {
		return glob.ErrRet(fmt.Sprintf("claim statement error: failed to verify fact:\n%s", failedFact))
	}

	return glob.NewStmtWithInnerStmtsRet(innerStmtRets, glob.StmtRetTypeTrue)

}

// 也许我应该语义改成，先声明prop，然后再证明prop，而不是现在这个样子
func (exec *Executor) claimImplyStmt(stmt *ast.ClaimImplicationStmt) *glob.StmtRet {
	// prop all atoms declared
	uniFact := ast.NewUniFact(stmt.Implication.DefHeader.Params, stmt.Implication.DefHeader.ParamSets, stmt.Implication.IffFactsOrNil, stmt.Implication.ImplicationFactsOrNil, stmt.Line)

	ret := exec.Env.LookUpNamesInFact(uniFact, map[string]struct{}{})
	if ret.IsErr() {
		ret.AddError("in claim prop statement")
		return glob.ErrRet(ret.String())
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
	prop := stmt.Implication
	execRet := exec.knowPropInferStmt(ast.NewKnowPropInferStmt(prop, stmt.Line))
	if execRet.IsNotTrue() {
		return execRet
	}

	return execRet
}

// func (exec *Executor) claimExistPropStmt(stmt *ast.ClaimExistPropStmt) *glob.StmtRet {
// 	execState := exec.claimExistPropStmtCheckProofs(stmt)
// 	if execState.IsNotTrue() {
// 		return execState
// 	}

// 	// declare exist prop
// 	execState = exec.defExistPropStmt(stmt.ExistPropWithoutDom)
// 	if execState.IsNotTrue() {
// 		return execState
// 	}

// 	// know forall
// 	uniFact := ast.NewUniFact(stmt.ExistPropWithoutDom.DefBody.DefHeader.Params, stmt.ExistPropWithoutDom.DefBody.DefHeader.ParamSets, stmt.ExistPropWithoutDom.DefBody.IffFactsOrNil, []ast.FactStmt{stmt.ExistPropWithoutDom.DefBody.DefHeader.ToSpecFact()}, stmt.Line)
// 	ret := exec.Env.NewFactWithoutCheckingNameDefined(uniFact)
// 	if ret.IsErr() {
// 		return glob.ErrRet(ret.String())
// 	}

// 	return glob.NewEmptyStmtTrue()
// }

// func (exec *Executor) claimExistPropStmtCheckProofs(stmt *ast.ClaimExistPropStmt) *glob.StmtRet {
// 	exec.NewEnv()
// 	defer func() {
// 		exec.deleteEnv()
// 	}()

// 	innerStmtRets := []*glob.StmtRet{}

// 	// declare parameters in exist prop
// 	defObjStmt := ast.NewDefLetStmt(stmt.ExistPropWithoutDom.DefBody.DefHeader.Params, stmt.ExistPropWithoutDom.DefBody.DefHeader.ParamSets, stmt.ExistPropWithoutDom.DefBody.IffFactsOrNil, stmt.Line)

// 	execState := exec.defLetStmt(defObjStmt)
// 	if execState.IsNotTrue() {
// 		return execState
// 	}
// 	innerStmtRets = append(innerStmtRets, execState)

// 	for _, curStmt := range stmt.Proofs {
// 		execState := exec.Stmt(curStmt)
// 		if execState.IsNotTrue() {
// 			if execState.IsUnknown() {
// 				return execState.AddUnknown(fmt.Sprintf("unknown :( line %d\n", curStmt.GetLine()))
// 			} else {
// 				return execState.AddError(fmt.Sprintf("failed :( line %d:\n", curStmt.GetLine()))
// 			}
// 		}
// 		innerStmtRets = append(innerStmtRets, execState)
// 	}

// 	// 把haveObj 代入 existParams 看看是否真的符合 then
// 	if len(stmt.HaveObj) != len(stmt.ExistPropWithoutDom.ExistParams) {
// 		return glob.ErrRet(fmt.Sprintf("claim exist prop statement error: have obj length is not equal to exist params length"))
// 	}

// 	uniMap := make(map[string]ast.Obj)
// 	for i, haveObj := range stmt.HaveObj {
// 		uniMap[stmt.ExistPropWithoutDom.ExistParams[i]] = haveObj
// 	}

// 	for _, fact := range stmt.ExistPropWithoutDom.DefBody.ImplicationFactsOrNil {
// 		instFact, err := fact.InstantiateFact(uniMap)
// 		if err != nil {
// 			return glob.ErrRet(err.Error())
// 		}
// 		execState := exec.factStmt(instFact)
// 		if execState.IsErr() {
// 			return execState
// 		}
// 		if notOkExec(execState, err) {
// 			return execState
// 		}
// 		innerStmtRets = append(innerStmtRets, execState)
// 	}

// 	return glob.NewStmtWithInnerStmtsRet(innerStmtRets, glob.StmtRetTypeTrue)
// }

func (exec *Executor) checkClaimPropStmtProofs(stmt *ast.ClaimImplicationStmt) *glob.StmtRet {
	uniFact := ast.NewUniFact(stmt.Implication.DefHeader.Params, stmt.Implication.DefHeader.ParamSets, stmt.Implication.IffFactsOrNil, stmt.Implication.ImplicationFactsOrNil, stmt.Line)

	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	execRet := exec.claimStmtProveUniFact(ast.NewClaimProveStmt(uniFact, stmt.Proofs, stmt.Line))
	if execRet.IsNotTrue() {
		return execRet
	}

	return execRet
}

func (exec *Executor) claimIffStmt(stmt *ast.ClaimIffStmt) *glob.StmtRet {
	innerStmtRets := []*glob.StmtRet{}

	thenToIff := stmt.UniFactWithIffStmt.NewUniFactWithThenToIff()
	iffToThen := stmt.UniFactWithIffStmt.NewUniFactWithIffToThen()
	claimThenToIff := ast.NewClaimProveStmt(thenToIff, stmt.ProofThenToIff, stmt.Line)
	claimIffToThen := ast.NewClaimProveStmt(iffToThen, stmt.ProofIffToThen, stmt.Line)
	execState := exec.claimStmtProve(claimThenToIff)
	if execState.IsNotTrue() {
		return execState
	}
	innerStmtRets = append(innerStmtRets, execState.InnerStmtRetSlice...)
	execState = exec.claimStmtProve(claimIffToThen)
	if execState.IsNotTrue() {
		return execState
	}
	innerStmtRets = append(innerStmtRets, execState.InnerStmtRetSlice...)

	ret := exec.Env.NewFactWithCheckingNameDefined(thenToIff)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	ret = exec.Env.NewFactWithCheckingNameDefined(iffToThen)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	return glob.NewStmtWithInnerStmtsRet(innerStmtRets, glob.StmtRetTypeTrue)
}
