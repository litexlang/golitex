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
)

func (exec *Executor) Stmt(stmt ast.Stmt) ExecRet {
	var execRet ExecRet = NewEmptyExecErr()

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		execRet = exec.factStmt(stmt)
	case *ast.KnowFactStmt:
		execRet = exec.knowStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddMsg("Warning: `know` saves the facts you write without verification. You may introduce incorrect facts by mistake. Use it with great caution!\n")
		}
	case *ast.KnowPropStmt:
		execRet = exec.knowPropStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddMsg("Warning: `know imply ` saves the facts you write without verification. You may introduce incorrect facts by mistake. Use it with great caution!\n")
		}
	case *ast.ClaimProveStmt:
		execRet = exec.execClaimStmtProve(stmt)
	case *ast.DefPropStmt:
		execRet = exec.defPropStmt(stmt, true)
	case *ast.ImplicationStmt:
		execRet = exec.implicationStmt(stmt)
	case *ast.DefLetStmt:
		execRet = exec.defLetStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddMsg("Warning: `let` may introduce non-existent objects. If you want to ensure the object exists, please use `have` instead!\n")
		}
	case *ast.HaveObjStStmt:
		execRet = exec.haveObjStStmt(stmt, true)
	case *ast.DefExistPropStmt:
		execRet = exec.defExistPropStmt(stmt)
	case *ast.DefFnStmt:
		execRet = exec.defFnStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddMsg("Warning: `fn` may introduce non-existent functions. If you want to ensure the function exists, please use `have fn` instead!\n")
		}
	case *ast.ProveInEachCaseStmt:
		execRet = exec.proveInEachCaseStmt(stmt)
	case *ast.ClaimImplicationStmt:
		execRet = exec.claimPropStmt(stmt)
	case *ast.ClaimExistPropStmt:
		execRet = exec.claimExistPropStmt(stmt)
	case *ast.ProveStmt:
		execRet = exec.proveStmt(stmt)
	case *ast.ClaimProveByContradictionStmt:
		execRet = exec.execClaimStmtProveByContradiction(stmt)
	case *ast.ProveByEnumStmt:
		execRet = exec.proveByEnumStmt(stmt)
	case *ast.HaveObjInNonEmptySetStmt:
		execRet = exec.haveObjInNonEmptySetStmt(stmt)
	// case *ast.NamedUniFactStmt:
	// 	execRet = exec.namedUniFactStmt(stmt)
	case *ast.KnowExistPropStmt:
		execRet = exec.knowExistPropStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddMsg("Warning: `know exist` saves the facts you write without verification. You may introduce incorrect facts by mistake. Use it with great caution!\n")
		}
	case *ast.DefFnSetStmt:
		execRet = exec.DefFnTemplateStmt(stmt)
	case *ast.ClearStmt:
		execRet = exec.ClearStmt()
	case *ast.DoNothingStmt:
		execRet = exec.DoNothingStmt()
	case *ast.InlineFactsStmt:
		execRet = exec.inlineFactsStmt(stmt)
	case *ast.ProveByInductionStmt:
		execRet = exec.proveByInductionStmt(stmt)
	case *ast.HaveObjEqualStmt:
		execRet = exec.haveObjEqualStmt(stmt)
	case *ast.HaveFnEqualStmt:
		execRet = exec.haveFnEqualStmt(stmt)
	// case *ast.HaveFnLiftStmt:
	// 	execRet = exec.haveFnLiftStmt(stmt)
	case *ast.HaveFnStmt:
		execRet = exec.haveFnStmt(stmt)
	case *ast.HaveFnCaseByCaseStmt:
		execRet = exec.haveFnCaseByCaseStmt(stmt)
	case *ast.ClaimIffStmt:
		execRet = exec.claimIffStmt(stmt)
	// case *ast.ProveInRangeSetStmt:
	// 	execRet = exec.proveInRangeSetStmt(stmt)
	case *ast.ProveIsTransitivePropStmt:
		execRet = exec.proveIsTransitivePropStmt(stmt)
	case *ast.ProveIsCommutativePropStmt:
		execRet = exec.proveIsCommutativePropStmt(stmt)
	case *ast.DefAlgoStmt:
		execRet = exec.defAlgoStmt(stmt)
	case *ast.EvalStmt:
		execRet = exec.evalStmt(stmt)
	case *ast.DefProveAlgoStmt:
		execRet = exec.defProveAlgoStmt(stmt)
	case *ast.ByStmt:
		execRet = exec.byStmt(stmt)
	case *ast.HaveFnEqualCaseByCaseStmt:
		execRet = exec.haveFnEqualCaseByCaseStmt(stmt)
	case *ast.ProveCaseByCaseStmt:
		execRet = exec.proveCaseByCaseStmt(stmt)
	case *ast.ImportDirStmt:
		execRet = NewExecErr("import statements are not allowed in local scope.")
	case *ast.RunFileStmt:
		execRet = NewExecErr("import statements are not allowed in local scope.")
	case *ast.HaveObjFromCartSetStmt:
		execRet = exec.haveObjFromCartSetStmt(stmt)
	case *ast.ProveForStmt:
		execRet = exec.proveForStmt(stmt)
	default:
		execRet = NewExecErr(fmt.Sprintf("unknown statement type: %T", stmt))
	}

	if execRet.IsTrue() {
		return execRet.AddMsg(SuccessExecStmtStr(stmt))
	} else if execRet.IsUnknown() {
		return execRet.AddMsg(UnknownExecStmtStr(stmt))
	} else {
		return execRet.AddMsg(ErrorExecStmtStr(stmt))
	}
}

func (exec *Executor) factStmt(stmt ast.FactStmt) ExecRet {
	curVerifier := NewVerifier(exec.Env)
	state := NewVerState(0, true, false)
	verRet := curVerifier.VerFactStmt(stmt, state)

	if verRet.IsErr() {
		return verRet.AddMsg(stmt.String())
	} else if verRet.IsTrue() {
		ret := exec.Env.NewFactWithoutCheckingNameDefined(stmt)
		if ret.IsErr() {
			return NewExecErr(ret.String()).AddMsg(stmt.String())
		}
		if verRet.(*ExecTrue).TrueEqualValues != nil {
			if verRet.(*ExecTrue).TrueEqualValues[0] != nil {
				exec.Env.StoreTrueEqualValues(stmt.(*ast.SpecFactStmt).Params[1], verRet.(*ExecTrue).TrueEqualValues[0])
			}
			if verRet.(*ExecTrue).TrueEqualValues[1] != nil {
				exec.Env.StoreTrueEqualValues(stmt.(*ast.SpecFactStmt).Params[0], verRet.(*ExecTrue).TrueEqualValues[1])
			}
		}
		return verRet.AddMsg(stmt.String())
	} else if verRet.IsUnknown() {
		return verRet.AddMsg(stmt.String())
	} else {
		execRet := NewExecErr("unknown ver ret")
		return execRet.AddMsg(stmt.String())
	}
}

// TODO: 再know时就检查，仅仅依赖写在dom里的事实，是否真的能让涉及到的函数和prop能真的满足条件。如果不满足条件，那就warning
func (exec *Executor) knowStmt(stmt *ast.KnowFactStmt) ExecRet {
	allDerivedFacts := []string{}

	for _, fact := range stmt.Facts {
		switch fact := fact.(type) {
		case ast.FactStmt:
			ret := exec.Env.NewFactWithoutCheckingNameDefined(fact)
			if ret.IsErr() {
				return NewExecErr(ret.String()).AddMsg(stmt.String())
			}
			// Collect derived facts from post-processing
			if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
				allDerivedFacts = append(allDerivedFacts, ret.GetMsgs()...)
			}

		case *ast.KnowPropStmt:
			execRet := exec.knowPropStmt(fact)
			if execRet.IsNotTrue() {
				return execRet.AddMsg(stmt.String())
			}
		default:
			return NewExecErr(fmt.Sprintf("unknown fact type: %T", fact)).AddMsg(stmt.String())
		}
	}

	// Build the result with all derived facts
	resultMsgs := []string{stmt.String()}
	if len(allDerivedFacts) > 0 {
		resultMsgs = append(resultMsgs, allDerivedFacts...)
	}
	return NewExecTrueWithMsgs(resultMsgs)
}

func (exec *Executor) defPropStmt(stmt *ast.DefPropStmt, generateIffUniFact bool) ExecRet {
	ret := exec.Env.NewDefProp_InsideAtomsDeclared(stmt)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	paramMap := make(map[string]struct{})
	for _, param := range stmt.DefHeader.Params {
		paramMap[param] = struct{}{}
	}

	if len(stmt.IffFactsOrNil) == 0 {
		return NewExecTrue(stmt.String())
	}

	if generateIffUniFact {
		// prop leads to iff
		propToIff, iffToProp, err := stmt.Make_PropToIff_IffToProp()
		if err != nil {
			return NewExecErr(err.Error())
		}

		ret = exec.Env.NewFactWithoutCheckingNameDefined(propToIff)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}

		ret = exec.Env.NewFactWithoutCheckingNameDefined(iffToProp)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}
	execRet := NewExecTrue(stmt.String())
	// Note: Messages about "is true by definition" are now handled in the verifier
	return execRet
}

func (exec *Executor) defLetStmt(stmt *ast.DefLetStmt) ExecRet {
	ret := exec.Env.DefLetStmt(stmt)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}
	return NewExecTrue(stmt.String()).AddMsgs(ret.GetMsgs())
}

func (exec *Executor) defExistPropStmt(stmt *ast.DefExistPropStmt) ExecRet {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	// if glob.RequireMsg() {
	// 	defer exec.newMsg(fmt.Sprintf("%s\n", stmt))
	// }

	ret := exec.Env.NewDefExistProp_InsideAtomsDeclared(stmt)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}
	return NewExecTrue(stmt.String())
}

// TODO: 我认为打印一下 claim 里面的各个语句的输出还是有道理的
func (exec *Executor) execStmtsAtCurEnv(proof []ast.Stmt) ExecRet {
	for _, curStmt := range proof {
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			return execState.AddMsg(fmt.Sprintf("%s\nfailed :( line %d\n", curStmt.String(), curStmt.GetLine()))
		}
	}
	return NewEmptyExecTrue()
}

func (exec *Executor) proveInEachCaseStmt(stmt *ast.ProveInEachCaseStmt) ExecRet {
	isSuccess := false

	// prove orFact is true
	execState := exec.factStmt(stmt.OrFact)
	if execState.IsNotTrue() {
		return execState.AddMsg(fmt.Sprintf("%s is unknown", stmt.OrFact.String()))
	}

	for i := range stmt.OrFact.Facts {
		execState, err := exec.execProofBlockForEachCase(i, stmt)
		if notOkExec(execState, err) {
			return execState
		}
	}

	// emit then fact
	execState = exec.knowStmt(ast.NewKnowStmt(stmt.ThenFacts.ToCanBeKnownStmtSlice(), stmt.Line))
	if execState.IsNotTrue() {
		return execState
	}

	isSuccess = true
	result := NewEmptyExecTrue()
	result = result.AddMsg("\n")
	if isSuccess {
		result = result.AddMsgAtBegin("is true\n")
	} else {
		result = result.AddMsgAtBegin("is unknown\n")
	}
	result = result.AddMsgAtBegin(stmt.String())
	return result
}

func (exec *Executor) execProofBlockForEachCase(index int, stmt *ast.ProveInEachCaseStmt) (ExecRet, error) {
	exec.NewEnv()
	defer exec.deleteEnv()

	caseStmt := stmt.OrFact.Facts[index]

	ret := exec.Env.NewFactWithoutCheckingNameDefined(caseStmt)
	if ret.IsErr() {
		return NewExecErr(ret.String()), fmt.Errorf(ret.String())
	}

	execState := exec.execStmtsAtCurEnv(stmt.Proofs[index])
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	// verify thenFacts are true
	// execState, failedFact, err := verifier.ExecFactsAtCurEnv_retFailedFact(stmt.ThenFacts, exec.env, verifier.Round0NoMsg)
	execState, failedFact, err := exec.verifyFactsAtCurEnv(stmt.ThenFacts, Round0NoMsg())
	if err != nil {
		return execState, fmt.Errorf("prove in each case statement error: failed to verify then facts:\n%s\n%s", failedFact, err)
	} else if execState.IsUnknown() {
		return execState, fmt.Errorf("prove in each case statement error: failed to verify then facts:\n%s", failedFact)
	}

	return NewExecTrue(stmt.String()), nil
}

func (exec *Executor) proveCaseByCaseStmt(stmt *ast.ProveCaseByCaseStmt) ExecRet {
	// Create OrStmt from CaseFacts
	orFact := ast.NewOrStmt(stmt.CaseFacts, stmt.Line)

	// Verify that the OR fact is true (fact1 or fact2 ... is true)
	execState := exec.factStmt(orFact)
	if execState.IsNotTrue() {
		return execState.AddMsg(fmt.Sprintf("%s is unknown\n", orFact.String()))
	}

	// Prove each case
	for i := range stmt.CaseFacts {
		execState, err := exec.execProofBlockForCaseByCase(i, stmt)
		if notOkExec(execState, err) {
			return execState
		}
	}

	// emit then fact
	execState = exec.knowStmt(ast.NewKnowStmt(stmt.ThenFacts.ToCanBeKnownStmtSlice(), stmt.Line))
	if execState.IsNotTrue() {
		return execState
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) execProofBlockForCaseByCase(index int, stmt *ast.ProveCaseByCaseStmt) (ExecRet, error) {
	exec.NewEnv()
	defer exec.deleteEnv()

	caseStmt := stmt.CaseFacts[index]

	ret := exec.Env.NewFactWithoutCheckingNameDefined(caseStmt)
	if ret.IsErr() {
		return NewExecErr(ret.String()), fmt.Errorf(ret.String())
	}

	execState := exec.execStmtsAtCurEnv(stmt.Proofs[index])
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	// verify thenFacts are true
	execState, failedFact, err := exec.verifyFactsAtCurEnv(stmt.ThenFacts, Round0NoMsg())
	if err != nil {
		return execState, fmt.Errorf("prove case by case statement error: failed to verify then facts:\n%s\n%s", failedFact, err)
	} else if execState.IsUnknown() {
		return execState, fmt.Errorf("prove case by case statement error: failed to verify then facts:\n%s", failedFact)
	}

	return NewExecTrue(stmt.String()), nil
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
func (exec *Executor) knowPropStmt(stmt *ast.KnowPropStmt) ExecRet {
	execRet := exec.defPropStmt(stmt.Prop, false)
	if execRet.IsNotTrue() {
		return execRet
	}

	if len(stmt.Prop.IffFactsOrNil) == 0 {
		_, iffToProp, err := stmt.Prop.Make_PropToIff_IffToProp()
		if err != nil {
			return NewExecErr(err.Error())
		}
		ret := exec.Env.NewFactWithoutCheckingNameDefined(iffToProp)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	paramsAsObj := []ast.Obj{}
	for i := range stmt.Prop.DefHeader.Params {
		paramsAsObj = append(paramsAsObj, ast.Atom(stmt.Prop.DefHeader.Params[i]))
	}

	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.Prop.DefHeader.Name), paramsAsObj, stmt.Line)}, stmt.Prop.ImplicationFactsOrNil, stmt.Line)

	ret := exec.Env.NewFactWithoutCheckingNameDefined(uniFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	uniFact2 := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.IffFactsOrNil, stmt.Prop.ImplicationFactsOrNil, stmt.Line)
	ret = exec.Env.NewFactWithoutCheckingNameDefined(uniFact2)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) proveStmt(stmt *ast.ProveStmt) ExecRet {
	// new env
	exec.NewEnv()
	defer exec.deleteEnv()

	execState := exec.execStmtsAtCurEnv(stmt.Proof)
	if execState.IsNotTrue() {
		return execState
	}
	return execState.AddMsg(stmt.String())
}

func (exec *Executor) defFnStmt(stmt *ast.DefFnStmt) ExecRet {
	ret := exec.Env.IsNameValidAndAvailable(stmt.Name)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	// 在 objMem 里记录一下
	defLetStmt := ast.NewDefLetStmt([]string{stmt.Name}, []ast.Obj{ast.Atom(glob.KeywordSet)}, []ast.FactStmt{}, stmt.Line)
	ret = exec.Env.DefLetStmt(defLetStmt)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}
	exec.Env.AllDefinedAtomObjNames[stmt.Name] = struct{}{}

	ret = exec.Env.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(ast.Atom(stmt.Name), nil, stmt.FnTemplate)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	derivedFact, err := stmt.FnTemplate.DeriveUniFact_WithGivenFn(ast.Atom(stmt.Name))
	if err != nil {
		return NewExecErr(err.Error())
	}

	ret = exec.Env.NewFactWithoutCheckingNameDefined(derivedFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) proveByEnumStmtProve(stmt *ast.ProveByEnumStmt) ExecRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	execState, err := exec.proveByEnumMainLogic(stmt)
	if notOkExec(execState, err) {
		return NewExecErr(execState.String())
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) proveByEnumStmt(stmt *ast.ProveByEnumStmt) ExecRet {
	execRet := exec.proveByEnumStmtProve(stmt)
	if execRet.IsNotTrue() {
		return execRet
	}

	// know uniFact
	ret := exec.Env.NewFactWithoutCheckingNameDefined(stmt.Fact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue(stmt.String())
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
func (exec *Executor) knowExistPropStmt(stmt *ast.KnowExistPropStmt) ExecRet {
	execState := exec.defExistPropStmt(stmt.ExistProp)
	if execState.IsNotTrue() {
		return execState
	}

	thenFacts := []ast.FactStmt{stmt.ExistProp.ToSpecFact()}
	knownUniFact := ast.NewUniFact(stmt.ExistProp.DefBody.DefHeader.Params, stmt.ExistProp.DefBody.DefHeader.ParamSets, stmt.ExistProp.DefBody.IffFactsOrNil, thenFacts, stmt.Line)

	ret := exec.Env.NewFactWithoutCheckingNameDefined(knownUniFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue(stmt.String()).AddMsg(fmt.Sprintf("%s\nis true by definition", knownUniFact))
}

func (exec *Executor) DefFnTemplateStmt(stmt *ast.DefFnSetStmt) ExecRet {
	// if glob.RequireMsg() {
	// 	defer exec.newMsg(fmt.Sprintf("%s\n", stmt))
	// }

	ret := exec.Env.NewFnTemplateInEnvMem(stmt)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) ClearStmt() ExecRet {
	newEnvMgr := env.NewBuiltinEnvMgr(exec.Env)
	exec.Env = newEnvMgr.NewEnv()
	return NewExecTrue("clear all definitions and facts")
}

func (exec *Executor) DoNothingStmt() ExecRet {
	// do_nothing statement does nothing
	return NewEmptyExecTrue()
}

func (exec *Executor) inlineFactsStmt(stmt *ast.InlineFactsStmt) ExecRet {
	for _, fact := range stmt.Facts {
		execState := exec.factStmt(fact)
		if execState.IsNotTrue() {
			return execState
		}
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) Verify(fact ast.FactStmt, requireMsg bool) ExecRet {
	ver := NewVerifier(exec.Env)
	var state *VerState
	if requireMsg {
		state = Round0Msg()
	} else {
		state = Round0NoMsg()
	}

	return ver.VerFactStmt(fact, state)
}

// func (exec *Executor) markdownStmt(stmt *ast.MarkdownStmt) ExecRet {
// 	_ = stmt
// 	return NewExecEmptyTrue()
// }

// func (exec *Executor) latexStmt(stmt *ast.LatexStmt) ExecRet {
// 	_ = stmt
// 	return NewExecEmptyTrue()
// }

func (exec *Executor) proveIsTransitivePropStmt(stmt *ast.ProveIsTransitivePropStmt) ExecRet {
	err := exec.proveIsTransitivePropStmtBody(stmt)
	if err != nil {
		return NewExecErr(err.Error())
	}

	exec.Env.CurEnv().TransitivePropMem[string(stmt.Prop)] = make(map[string][]ast.Obj)

	return NewExecTrue(stmt.String())
}

// TODO 这里的msg系统太冗杂了，需要优化
func (exec *Executor) proveIsTransitivePropStmtBody(stmt *ast.ProveIsTransitivePropStmt) error {
	exec.NewEnv()
	defer exec.deleteEnv()

	if exec.Env.IsTransitiveProp(string(stmt.Prop)) {
		return nil
	}

	def := exec.Env.GetPropDef(stmt.Prop)
	if def == nil {
		return fmt.Errorf("undefined prop: %s", stmt.Prop)
	}

	if len(def.DefHeader.Params) != 2 {
		return fmt.Errorf("prop %s has %d params, but 2 params are expected", stmt.Prop, len(def.DefHeader.Params))
	}

	// def 的 paramSet 必须相等
	state := exec.factStmt(ast.NewEqualFact(def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1]))
	if state.IsErr() {
		return fmt.Errorf(state.String())
	}
	if state.IsUnknown() {
		return fmt.Errorf("prop in %s must have equal parameter sets, but parameter sets %s and %s of %s are not equal", glob.KeywordProveIsTransitiveProp, def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1], def.DefHeader.Name)
	}

	// 这里最好检查一下，是不是 Param set 依赖了 Param，如果依赖了，那其实是要报错了，不过暂时不管了
	execState := exec.defLetStmt(ast.NewDefLetStmt(stmt.Params, []ast.Obj{def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[0]}, def.DomFactsOrNil, stmt.Line))
	if execState.IsNotTrue() {
		return fmt.Errorf(execState.String())
	}

	ret := exec.Env.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(def.DefHeader.ParamSets[0], map[string]struct{}{})
	if ret.IsErr() {
		return fmt.Errorf(ret.String())
	}
	ret = exec.Env.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(def.DefHeader.ParamSets[1], map[string]struct{}{})
	if ret.IsErr() {
		return fmt.Errorf(ret.String())
	}

	if len(def.DomFactsOrNil) > 0 {
		return fmt.Errorf("dom facts are not allowed in %s", glob.KeywordProveIsTransitiveProp)
	}

	ret = exec.Env.NewFactWithoutCheckingNameDefined(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.Prop), []ast.Obj{ast.Atom(stmt.Params[0]), ast.Atom(stmt.Params[1])}, stmt.Line))
	if ret.IsErr() {
		return fmt.Errorf(ret.String())
	}

	ret = exec.Env.NewFactWithoutCheckingNameDefined(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.Prop), []ast.Obj{ast.Atom(stmt.Params[1]), ast.Atom(stmt.Params[2])}, stmt.Line))
	if ret.IsErr() {
		return fmt.Errorf(ret.String())
	}

	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return fmt.Errorf(execState.String())
		}
	}

	// check
	finalCheckStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.Prop), []ast.Obj{ast.Atom(stmt.Params[0]), ast.Atom(stmt.Params[2])}, stmt.Line)
	state = exec.factStmt(finalCheckStmt)
	if state.IsNotTrue() {
		return fmt.Errorf("failed to prove %s is transitive: %s failed", stmt.Prop, finalCheckStmt)
	}

	return nil
}

func (exec *Executor) defAlgoStmt(stmt *ast.DefAlgoStmt) ExecRet {
	exec.Env.CurEnv().AlgoDefMem[stmt.FuncName] = struct{}{}
	exec.Env.AllDefinedAlgoNames[stmt.FuncName] = stmt
	return NewExecTrue(stmt.String())
}

func (exec *Executor) evalStmt(stmt *ast.EvalStmt) ExecRet {
	trueEvalRet := NewEmptyExecTrue()

	value, execRet := exec.evalObjInLocalEnv(stmt.ObjToEval)
	if execRet.IsNotTrue() {
		return execRet
	}
	ret := exec.Env.NewFactWithoutCheckingNameDefined(ast.NewEqualFact(stmt.ObjToEval, value))
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}
	trueEvalRet.Inherit(execRet)

	return trueEvalRet.NewVerMsgAtBegin(Round0Msg(), stmt.String())
}

func (exec *Executor) evalObjInLocalEnv(objToEval ast.Obj) (ast.Obj, ExecRet) {
	exec.NewEnv()
	defer exec.deleteEnv()

	value, execRet := exec.evalObjThenSimplify(objToEval)
	if execRet.IsNotTrue() {
		return nil, execRet
	}

	return value, NewExecTrue(fmt.Sprintf("By evaluation of algo %s\nWe get %s = %s\n", objToEval.(*ast.FnObj).FnHead.String(), objToEval.String(), value.String()))
}

func (exec *Executor) defProveAlgoStmt(stmt *ast.DefProveAlgoStmt) ExecRet {
	exec.Env.CurEnv().DefProveAlgoMem[stmt.ProveAlgoName] = struct{}{}
	exec.Env.AllDefinedProveAlgoNames[stmt.ProveAlgoName] = stmt
	return NewExecTrue(stmt.String())
}

func (exec *Executor) proveForStmt(stmt *ast.ProveForStmt) ExecRet {
	// Generate integer lists for each range
	ranges := [][]ast.Obj{}
	for i := range len(stmt.Params) {
		left, execRet := exec.GetSimplifiedValue(stmt.Lefts[i])
		if execRet.IsNotTrue() {
			return execRet
		}

		right, execRet := exec.GetSimplifiedValue(stmt.Rights[i])
		if execRet.IsNotTrue() {
			return execRet
		}

		leftAsInt, ok1 := ast.IsObjLiterallyIntNumber(left)
		rightAsInt, ok2 := ast.IsObjLiterallyIntNumber(right)
		if !ok1 || !ok2 {
			return NewExecErr(fmt.Sprintf("left value %s and right value %s must be integers", left.String(), right.String()))
		}

		if leftAsInt > rightAsInt {
			return NewExecErr(fmt.Sprintf("left value %d must be less than or equal to right value %d", leftAsInt, rightAsInt))
		}

		rightMost := rightAsInt
		if !stmt.IsProveIRange[i] {
			rightMost = rightAsInt + 1
		}

		// Generate integer list for this range
		rangeValues := []ast.Obj{}
		for j := leftAsInt; j < rightMost; j++ {
			rangeValues = append(rangeValues, ast.Atom(fmt.Sprintf("%d", j)))
		}
		ranges = append(ranges, rangeValues)
	}

	// Calculate Cartesian product of all ranges
	cartesianProductOfObjs := glob.CartesianProduct(ranges)

	// Iterate through all combinations
	for _, combination := range cartesianProductOfObjs {
		execRet := exec.proveForStmtWhenParamsAreIndices(stmt, combination)
		if execRet.IsNotTrue() {
			return execRet
		}
	}

	// Create and store the universal fact
	uniFact := stmt.UniFact()
	ret := exec.Env.NewFactWithoutCheckingNameDefined(uniFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) proveForStmtWhenParamsAreIndices(stmt *ast.ProveForStmt, indices []ast.Obj) ExecRet {
	uniMap := map[string]ast.Obj{}
	for i, param := range stmt.Params {
		uniMap[param] = indices[i]
	}

	exec.NewEnv()
	defer exec.deleteEnv()

	// Create def let statements for all parameters
	equalFacts := []ast.FactStmt{}
	paramSets := make([]ast.Obj, len(stmt.Params))
	for i, param := range stmt.Params {
		equalFacts = append(equalFacts, ast.NewEqualFact(ast.Atom(param), indices[i]))
		paramSets[i] = ast.Atom(glob.KeywordInteger)
	}

	defObjStmt := ast.NewDefLetStmt(stmt.Params, paramSets, equalFacts, stmt.Line)

	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	// Check dom facts
	for _, domFact := range stmt.DomFacts {
		instDomFact, err := domFact.InstantiateFact(uniMap)
		if err != nil {
			return NewExecErr(err.Error())
		}
		execState := exec.factStmt(instDomFact)
		if execState.IsErr() {
			return execState
		}

		if execState.IsUnknown() {
			// 如果 不OK，那必须证明是 false，绝对不能是 unknown
			specFact, ok := domFact.(*ast.SpecFactStmt)
			if !ok {
				return NewExecErr(fmt.Sprintf("dom fact in prove_for must be a SpecFactStmt to reverse: %s", domFact.String()))
			}
			revInstDomFact := specFact.ReverseIsTrue()
			for _, fact := range revInstDomFact {
				instFact, err := fact.InstantiateFact(uniMap)
				if err != nil {
					return NewExecErr(err.Error())
				}
				execState = exec.factStmt(instFact)
				if execState.IsErr() {
					return execState
				}
				if execState.IsUnknown() {
					return NewExecErr(fmt.Sprintf("dom facts in prove_for must be proved to be true or false, can not be unknown: %s", instFact.String()))
				}
			}

			return NewEmptyExecTrue()
		}

		ret := exec.Env.NewFactWithoutCheckingNameDefined(domFact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	// exec proofs
	for _, curStmt := range stmt.Proofs {
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			return execState
		}
	}

	// 满足 then
	for _, thenFact := range stmt.ThenFacts {
		instThenFact, err := thenFact.InstantiateFact(uniMap)
		if err != nil {
			return NewExecErr(err.Error())
		}

		execState = exec.factStmt(instThenFact)
		if execState.IsErr() {
			return execState
		}
		if execState.IsUnknown() {
			return NewExecErr(fmt.Sprintf("then fact in prove_for must be proved to be true or false, can not be unknown: %s", instThenFact.String()))
		}
	}

	return NewEmptyExecTrue()
}

func (exec *Executor) implicationStmt(stmt *ast.ImplicationStmt) ExecRet {
	// Convert ImplicationStmt to DefPropStmt (with dom and implication facts, but no iff facts)
	defPropStmt := ast.NewDefPropStmt(stmt.DefHeader, stmt.DomFacts, nil, stmt.ImplicationFacts, stmt.Line)
	ret := exec.Env.NewDefProp_InsideAtomsDeclared(defPropStmt)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue(stmt.String())
}
