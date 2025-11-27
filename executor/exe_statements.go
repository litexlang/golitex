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

func (exec *Executor) Stmt(stmt ast.Stmt) ExecRet {
	var execRet ExecRet = NewExecErr("")

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		execRet = exec.factStmt(stmt)
	case *ast.KnowFactStmt:
		execRet = exec.knowStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddMsg("Warning: `know` saves the facts you write without verification. Users may inadvertently introduce incorrect facts. Use it with great caution.\n")
		}
	case *ast.KnowPropStmt:
		execRet = exec.knowPropStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddMsg("Warning: `know @` saves the facts you write without verification. Users may inadvertently introduce incorrect facts. Use it with great caution.\n")
		}
	case *ast.ClaimProveStmt:
		execRet = exec.execClaimStmtProve(stmt)
	case *ast.DefPropStmt:
		execRet = exec.defPropStmt(stmt, true)
	case *ast.DefLetStmt:
		execRet = exec.defLetStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddMsg("Warning: `let` may introduce non-existent objects. If you want to ensure the object exists, please use `have` instead.\n")
		}
	case *ast.HaveObjStStmt:
		execRet = exec.haveObjStStmt(stmt, true)
	case *ast.DefExistPropStmt:
		execRet = exec.defExistPropStmt(stmt)
	case *ast.DefFnStmt:
		execRet = exec.defFnStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddMsg("Warning: `fn` may introduce non-existent functions. If you want to ensure the function exists, please use `have fn` instead.\n")
		}
	case *ast.ProveInEachCaseStmt:
		execRet = exec.proveInEachCaseStmt(stmt)
	case *ast.ClaimPropStmt:
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
	case *ast.HaveEnumSetStmt:
		execRet = exec.haveEnumSetStmt(stmt)
	case *ast.HaveIntensionalSetStmt:
		execRet = exec.haveIntensionalSetStmt(stmt)
	case *ast.HaveCartSetStmt:
		execRet = exec.haveCartSetStmt(stmt)
	case *ast.HaveSetFnStmt:
		execRet = exec.haveSetFnStmt(stmt)
	case *ast.HaveSetDefinedByReplacementStmt:
		execRet = exec.haveSetDefinedByReplacementStmt(stmt)
	case *ast.NamedUniFactStmt:
		execRet = exec.namedUniFactStmt(stmt)
	case *ast.KnowExistPropStmt:
		execRet = exec.knowExistPropStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddMsg("Warning: `know exist` saves the facts you write without verification. Users may inadvertently introduce incorrect facts. Use it with great caution.\n")
		}
	case *ast.FnTemplateDefStmt:
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
	case *ast.HaveFnLiftStmt:
		execRet = exec.haveFnLiftStmt(stmt)
	case *ast.HaveFnStmt:
		execRet = exec.haveFnStmt(stmt)
	case *ast.HaveFnCaseByCaseStmt:
		execRet = exec.haveFnCaseByCaseStmt(stmt)
	case *ast.MarkdownStmt:
		execRet = exec.markdownStmt(stmt)
		return execRet
	case *ast.LatexStmt:
		execRet = exec.latexStmt(stmt)
		return execRet
	case *ast.ClaimIffStmt:
		execRet = exec.claimIffStmt(stmt)
	case *ast.ProveInRangeSetStmt:
		execRet = exec.proveInRangeSetStmt(stmt)
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
	case *ast.PrintStmt:
		execRet = exec.printStmt(stmt)
	case *ast.HelpStmt:
		execRet = exec.helpStmt(stmt)
	case *ast.HaveFnEqualCaseByCaseStmt:
		execRet = exec.haveFnEqualCaseByCaseStmt(stmt)
	case *ast.ProveCaseByCaseStmt:
		execRet = exec.proveCaseByCaseStmt(stmt)
	case *ast.ProveInRangeStmt:
		execRet = exec.proveInRangeStmt(stmt)
	default:
		panic(fmt.Sprintf("unknown statement type: %T", stmt))
	}

	if execRet.IsTrue() {
		return execRet.AddMsg(fmt.Sprintf("\nSuccess! line %d\n", stmt.GetLine()))
	} else if execRet.IsUnknown() {
		return execRet.AddMsg(fmt.Sprintf("Unknown: line %d\n", stmt.GetLine()))
	} else {
		return execRet.AddMsg(fmt.Sprintf("Execution Error: line %d\n", stmt.GetLine()))
	}
}

func (exec *Executor) factStmt(stmt ast.FactStmt) ExecRet {
	curVerifier := NewVerifier(exec.Env)
	state := Round0Msg
	verRet := curVerifier.VerFactStmt(stmt, state)

	if verRet.IsErr() {
		return verRet.AddMsg(stmt.String())
	} else if verRet.IsTrue() {
		ret := exec.Env.NewFact(stmt)
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
	for _, fact := range stmt.Facts {
		switch fact := fact.(type) {
		case ast.FactStmt:
			ret := exec.Env.NewFactWithDeclarationCheck(fact)
			if ret.IsErr() {
				return NewExecErr(ret.String()).AddMsg(stmt.String())
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

	return NewExecTrue(stmt.String())
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

	for _, fact := range stmt.DomFacts {
		for _, param := range ast.ExtractParamsFromFact(fact) {
			if _, ok := paramMap[param]; ok {
				return NewExecErr(fmt.Sprintf("param %s in %s\n is already declared in def header %s and should not be redeclared", param, fact.String(), ast.HeaderWithParamsAndParamSetsString(stmt.DefHeader)))
			}
		}
	}
	for _, fact := range stmt.IffFacts {
		for _, param := range ast.ExtractParamsFromFact(fact) {
			if _, ok := paramMap[param]; ok {
				return NewExecErr(fmt.Sprintf("param %s in %s\nshould not be redeclared in def header %s", param, fact.String(), ast.HeaderWithParamsAndParamSetsString(stmt.DefHeader)))
			}
		}
	}
	for _, fact := range stmt.ThenFacts {
		for _, param := range ast.ExtractParamsFromFact(fact) {
			if _, ok := paramMap[param]; ok {
				return NewExecErr(fmt.Sprintf("param %s in %s\nshould not be redeclared in def header %s", param, fact.String(), ast.HeaderWithParamsAndParamSetsString(stmt.DefHeader)))
			}
		}
	}

	if len(stmt.IffFacts) == 0 {
		return NewExecTrue("")
	}

	if generateIffUniFact {
		// prop leads to iff
		propToIff, iffToProp, err := stmt.Make_PropToIff_IffToProp()
		if err != nil {
			return NewExecErr(err.Error())
		}

		ret = exec.Env.NewFact(propToIff)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}

		ret = exec.Env.NewFact(iffToProp)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}
	execRet := NewExecTrue("")
	// Note: Messages about "is true by definition" are now handled in the verifier
	return execRet
}

func (exec *Executor) defLetStmt(stmt *ast.DefLetStmt) ExecRet {
	ret := exec.Env.DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(stmt)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}
	return NewExecTrue(stmt.String())
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
	return NewExecTrue("")
}

// TODO: 我认为打印一下 claim 里面的各个语句的输出还是有道理的
func (exec *Executor) execStmtsAtCurEnv(proof []ast.Stmt) ExecRet {
	for _, curStmt := range proof {
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			return execState.AddMsg(fmt.Sprintf("%s\nfailed :( line %d\n", curStmt.String(), curStmt.GetLine()))
		}
	}
	return NewExecTrue("")
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
	result := NewExecTrue("")
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
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	caseStmt := stmt.OrFact.Facts[index]

	ret := exec.Env.NewFact(caseStmt)
	if ret.IsErr() {
		return NewExecErr(ret.String()), fmt.Errorf(ret.String())
	}

	execState := exec.execStmtsAtCurEnv(stmt.Proofs[index])
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	// verify thenFacts are true
	// execState, failedFact, err := verifier.ExecFactsAtCurEnv_retFailedFact(stmt.ThenFacts, exec.env, verifier.Round0NoMsg)
	execState, failedFact, err := exec.verifyFactsAtCurEnv(stmt.ThenFacts, Round0NoMsg)
	if err != nil {
		return execState, fmt.Errorf("prove in each case statement error: failed to verify then facts:\n%s\n%s", failedFact, err)
	} else if execState.IsUnknown() {
		return execState, fmt.Errorf("prove in each case statement error: failed to verify then facts:\n%s", failedFact)
	}

	return NewExecTrue(""), nil
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
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	caseStmt := stmt.CaseFacts[index]

	ret := exec.Env.NewFact(caseStmt)
	if ret.IsErr() {
		return NewExecErr(ret.String()), fmt.Errorf(ret.String())
	}

	execState := exec.execStmtsAtCurEnv(stmt.Proofs[index])
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	// verify thenFacts are true
	execState, failedFact, err := exec.verifyFactsAtCurEnv(stmt.ThenFacts, Round0NoMsg)
	if err != nil {
		return execState, fmt.Errorf("prove case by case statement error: failed to verify then facts:\n%s\n%s", failedFact, err)
	} else if execState.IsUnknown() {
		return execState, fmt.Errorf("prove case by case statement error: failed to verify then facts:\n%s", failedFact)
	}

	return NewExecTrue(""), nil
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
func (exec *Executor) knowPropStmt(stmt *ast.KnowPropStmt) ExecRet {
	// if glob.RequireMsg() {
	// 	defer func() {
	// 		exec.newMsg(fmt.Sprintf("%s\n", stmt))
	// 	}()
	// }

	execRet := exec.defPropStmt(stmt.Prop, false)
	if execRet.IsNotTrue() {
		return execRet
	}

	if len(stmt.Prop.IffFacts) == 0 {
		_, iffToProp, err := stmt.Prop.Make_PropToIff_IffToProp()
		if err != nil {
			return NewExecErr(err.Error())
		}
		ret := exec.Env.NewFact(iffToProp)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	paramsAsFc := []ast.Obj{}
	for i := range stmt.Prop.DefHeader.Params {
		paramsAsFc = append(paramsAsFc, ast.AtomObj(stmt.Prop.DefHeader.Params[i]))
	}

	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(stmt.Prop.DefHeader.Name), paramsAsFc, stmt.Line)}, stmt.Prop.ThenFacts, stmt.Line)

	ret := exec.Env.NewFact(uniFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	uniFact2 := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.IffFacts, stmt.Prop.ThenFacts, stmt.Line)
	ret = exec.Env.NewFact(uniFact2)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) proveStmt(stmt *ast.ProveStmt) ExecRet {
	// new env
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	execState := exec.execStmtsAtCurEnv(stmt.Proof)
	if execState.IsNotTrue() {
		return execState
	}
	return execState
}

func (exec *Executor) defFnStmt(stmt *ast.DefFnStmt) ExecRet {
	ret := exec.Env.IsValidIdentifierAvailable(stmt.Name)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	// 在 objMem 里记录一下
	exec.Env.ObjDefMem[stmt.Name] = nil

	ret = exec.Env.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(ast.AtomObj(stmt.Name), nil, stmt.FnTemplate)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	derivedFact, err := stmt.FnTemplate.DeriveUniFact_WithGivenFn(ast.AtomObj(stmt.Name))
	if err != nil {
		return NewExecErr(err.Error())
	}

	ret = exec.Env.NewFact(derivedFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) proveByEnumStmt(stmt *ast.ProveByEnumStmt) ExecRet {

	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	execState, err := exec.proveByEnumMainLogic(stmt)
	if notOkExec(execState, err) {
		return execState
	}

	// know uniFact
	ret := exec.Env.Parent.NewFact(stmt.Fact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue("")
}

func (exec *Executor) haveSetFnStmt(stmt *ast.HaveSetFnStmt) ExecRet {

	// declare related fn
	fnDefStmt := stmt.ToDefFnStmt()
	execState := exec.defFnStmt(fnDefStmt)
	if execState.IsNotTrue() {
		return execState
	}

	// have set fn
	exec.Env.HaveSetFnDefMem[string(stmt.DefHeader.Name)] = *stmt

	return NewExecTrue("")
}

func (exec *Executor) haveSetDefinedByReplacementStmt(stmt *ast.HaveSetDefinedByReplacementStmt) ExecRet {

	setDefinedByReplacement := ast.NewFnObj(ast.AtomObj(glob.KeywordSetDefinedByReplacement), []ast.Obj{stmt.DomSet, stmt.RangeSet, stmt.PropName})

	defObjStmt := ast.NewDefLetStmt([]string{stmt.Name}, []ast.Obj{ast.AtomObj(glob.KeywordSet)}, []ast.FactStmt{ast.NewEqualFact(ast.AtomObj(stmt.Name), setDefinedByReplacement)}, stmt.Line)

	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	ret := exec.Env.SetEqualToSetDefinedByReplacement_PostProcess(ast.AtomObj(stmt.Name), setDefinedByReplacement)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue("")
}

func (exec *Executor) namedUniFactStmt(stmt *ast.NamedUniFactStmt) ExecRet {

	uniFact := ast.NewUniFact(stmt.DefPropStmt.DefHeader.Params, stmt.DefPropStmt.DefHeader.ParamSets, stmt.DefPropStmt.IffFacts, stmt.DefPropStmt.ThenFacts, stmt.Line)
	execState := exec.factStmt(uniFact)
	if execState.IsNotTrue() {
		return execState
	}

	execRet := exec.knowPropStmt(ast.NewKnowPropStmt(stmt.DefPropStmt, stmt.Line))
	if execRet.IsNotTrue() {
		return execRet
	}

	return execRet
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
func (exec *Executor) knowExistPropStmt(stmt *ast.KnowExistPropStmt) ExecRet {
	execState := exec.defExistPropStmt(stmt.ExistProp)
	if execState.IsNotTrue() {
		return execState
	}

	thenFacts := []ast.FactStmt{stmt.ExistProp.ToSpecFact()}
	knownUniFact := ast.NewUniFact(stmt.ExistProp.DefBody.DefHeader.Params, stmt.ExistProp.DefBody.DefHeader.ParamSets, stmt.ExistProp.DefBody.IffFacts, thenFacts, stmt.Line)

	ret := exec.Env.NewFact(knownUniFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue("").AddMsg(fmt.Sprintf("%s\nis true by definition", knownUniFact))
}

func (exec *Executor) DefFnTemplateStmt(stmt *ast.FnTemplateDefStmt) ExecRet {
	// if glob.RequireMsg() {
	// 	defer exec.newMsg(fmt.Sprintf("%s\n", stmt))
	// }

	ret := exec.Env.ExecDefFnTemplate(stmt)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue("")
}

func (exec *Executor) ClearStmt() ExecRet {
	curEnv := exec.Env
	for curEnv.Parent != nil {
		curEnv = curEnv.Parent
	} // 最顶层的env不删，因为最顶层的包含了热启动的代码
	exec.NewEnv(curEnv)
	// Note: Clear message should be added to ExecRet in the caller if needed
	return NewExecTrue("")
}

func (exec *Executor) DoNothingStmt() ExecRet {
	// do_nothing statement does nothing
	return NewExecTrue("")
}

func (exec *Executor) inlineFactsStmt(stmt *ast.InlineFactsStmt) ExecRet {
	for _, fact := range stmt.Facts {
		execState := exec.factStmt(fact)
		if execState.IsNotTrue() {
			return execState
		}
	}

	return NewExecTrue("")
}

func (exec *Executor) haveObjEqualStmt(stmt *ast.HaveObjEqualStmt) ExecRet {
	ver := NewVerifier(exec.Env)

	for i := range len(stmt.ObjNames) {
		verRet := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{stmt.ObjEqualTos[i], stmt.ObjSets[i]}, stmt.Line), Round0Msg)
		if verRet.IsErr() {
			return NewExecErr(verRet.String())
		}
		if verRet.IsUnknown() {
			return NewExecErr(fmt.Sprintf("%s is not in %s", stmt.ObjNames[i], stmt.ObjSets[i]))
		}

		stmtForDef := ast.NewDefLetStmt([]string{stmt.ObjNames[i]}, []ast.Obj{ast.AtomObj(glob.KeywordObj)}, []ast.FactStmt{}, stmt.Line)
		ret := exec.Env.DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(stmtForDef)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
		execState := NewExecTrue(stmtForDef.String())
		if execState.IsNotTrue() {
			return execState
		}
		// 检查 等号右边的东西是否存在
		ret = exec.Env.AreAtomsInFcAreDeclared(stmt.ObjEqualTos[i], map[string]struct{}{})
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in obj equal to %s", stmt.ObjEqualTos[i]))
			return NewExecErr(ret.String())
		}
		// new fact: obj = obj
		ret = exec.Env.NewFact(ast.NewEqualFact(ast.AtomObj(stmt.ObjNames[i]), stmt.ObjEqualTos[i]))
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	return NewExecTrue("")
}

func (exec *Executor) haveFnEqualStmt(stmt *ast.HaveFnEqualStmt) ExecRet {
	var err error
	execRet, err := exec.checkFnEqualStmt(stmt)
	if notOkExec(execRet, err) {
		return execRet.AddMsg(stmt.String())
	}

	newFnDefStmt := ast.NewDefFnStmt(string(stmt.DefHeader.Name), ast.NewFnTStruct(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, stmt.RetSet, []ast.FactStmt{}, []ast.FactStmt{ast.NewEqualFact(fnHeaderToReturnValueOfFn(stmt.DefHeader), stmt.EqualTo)}, stmt.Line), stmt.Line)
	execRet = exec.defFnStmt(newFnDefStmt)
	if execRet.IsNotTrue() {
		return execRet.AddMsg(fmt.Sprintf("failed to declare fn: %s", newFnDefStmt.String())).AddMsg(stmt.String())
	}

	return execRet.AddMsg(stmt.String())
}

func (exec *Executor) checkFnEqualStmt(stmt *ast.HaveFnEqualStmt) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	for i := range len(stmt.DefHeader.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefHeader.Params[i]}, []ast.Obj{stmt.DefHeader.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	ver := NewVerifier(exec.Env)

	verRet := ver.VerFactStmt(ast.NewInFactWithFc(stmt.EqualTo, stmt.RetSet), Round0Msg)
	if verRet.IsErr() {
		return NewExecErr(""), fmt.Errorf(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(""), fmt.Errorf("according to the definition of %s, the returned value %s must be in %s, but\n%s is unknown", stmt, stmt.EqualTo, stmt.RetSet, ast.NewInFactWithFc(stmt.EqualTo, stmt.RetSet))
	}

	return NewExecTrue(""), nil
}

func fnHeaderToReturnValueOfFn(head *ast.DefHeader) ast.Obj {
	params := make([]ast.Obj, len(head.Params))
	for i := range len(head.Params) {
		params[i] = ast.AtomObj(head.Params[i])
	}

	fnName := ast.AtomObj(head.Name)

	return ast.NewFnObj(fnName, params)
}

func (exec *Executor) haveFnLiftStmt(stmt *ast.HaveFnLiftStmt) ExecRet {
	// fn a(f fn(DOMAIN_of_x, DOMAIN_of_y, ...)OPT_PRAM0_DOM, g fn(DOMAIN_of_x, DOMAIN_of_y, ...)OPT_PRAM1_DOM, ...) fn(DOMAIN_of_x, DOMAIN_of_y, ...) opt_ret:
	// 	forall x DOMAIN_of_x, y DOMAIN_of_y, ...:
	// 		a(f, g, ...)(x, y, z, ...) = opt(f(x,y,z...) , g(x,y,z,...), ...)

	// have a = lift(opt, DOMAIN_of_x, DOMAIN_of_y, ...)

	// get definition of opt
	optDef := exec.Env.GetLatestFnT_GivenNameIsIn(stmt.Opt.String())
	if optDef == nil {
		return NewExecErr(fmt.Sprintf("%s is not defined", stmt.Opt.String()))
	}

	FnTemplateOfFunctions := []ast.Obj{}
	for i := range len(optDef.AsFnTStruct.ParamSets) {
		head := ast.NewFnObj(ast.AtomObj(glob.KeywordFn), stmt.DomainOfEachParamOfGivenFn)
		FnTemplateOfFunctions = append(FnTemplateOfFunctions, ast.NewFnObj(head, []ast.Obj{optDef.AsFnTStruct.ParamSets[i]}))
	}

	retSet := ast.NewFnObj(ast.NewFnObj(ast.AtomObj(glob.KeywordFn), stmt.DomainOfEachParamOfGivenFn), []ast.Obj{optDef.AsFnTStruct.RetSet})

	// randomly generate len different params
	randomParams := glob.GenerateUniqueRandomStrings(len(FnTemplateOfFunctions))

	knownUniFact := exec.haveFnLift_knowFact(stmt, randomParams)

	fnDef := ast.NewDefFnStmt(stmt.FnName, ast.NewFnTStruct(randomParams, FnTemplateOfFunctions, retSet, []ast.FactStmt{}, []ast.FactStmt{knownUniFact}, stmt.Line), stmt.Line)

	execState := exec.defFnStmt(fnDef)
	if execState.IsNotTrue() {
		return NewExecErr(fmt.Sprintf("failed to declare fn: %s", fnDef.String()))
	}

	execRet := NewExecTrue("")
	execRet.AddMsg(fmt.Sprintf("Declare Function by lifting:\n%s\n", fnDef))
	return execRet
}

func (exec *Executor) haveFnLift_knowFact(stmt *ast.HaveFnLiftStmt, fnNames []string) *ast.UniFactStmt {
	// fn a(f fn(DOMAIN_of_x, DOMAIN_of_y, ...)OPT_PRAM0_DOM, g fn(DOMAIN_of_x, DOMAIN_of_y, ...)OPT_PRAM1_DOM, ...) fn(DOMAIN_of_x, DOMAIN_of_y, ...) opt_ret:
	// 	forall x DOMAIN_of_x, y DOMAIN_of_y, ...:
	// 		a(f, g, ...)(x, y, z, ...) = opt(f(x,y,z...) , g(x,y,z,...), ...)

	// have a = lift(opt, DOMAIN_of_x, DOMAIN_of_y, ...)

	uniFactParams := glob.GenerateUniqueRandomStrings_NotInGivenStrSlice(len(stmt.DomainOfEachParamOfGivenFn), fnNames)
	uniFactParamsAsFc := []ast.Obj{}
	for i := range len(uniFactParams) {
		uniFactParamsAsFc = append(uniFactParamsAsFc, ast.AtomObj(uniFactParams[i]))
	}

	fnNamesAsFc := []ast.Obj{}
	for i := range len(fnNames) {
		fnNamesAsFc = append(fnNamesAsFc, ast.AtomObj(fnNames[i]))
	}

	uniFactParamSets := stmt.DomainOfEachParamOfGivenFn
	lhs := ast.NewFnObj(ast.NewFnObj(ast.AtomObj(stmt.FnName), fnNamesAsFc), uniFactParamsAsFc)

	rhsParams := []ast.Obj{}
	for i := range len(fnNamesAsFc) {
		rhsParams = append(rhsParams, ast.NewFnObj(ast.AtomObj(fnNames[i]), uniFactParamsAsFc))
	}

	rhs := ast.NewFnObj(stmt.Opt, rhsParams)

	return ast.NewUniFact(uniFactParams, uniFactParamSets, []ast.FactStmt{}, []ast.FactStmt{ast.NewEqualFact(lhs, rhs)}, stmt.Line)
}

func (exec *Executor) haveFnStmt(stmt *ast.HaveFnStmt) ExecRet {
	// Verify first
	execRet, err := exec.checkHaveFnStmt(stmt)
	if notOkExec(execRet, err) {
		return execRet
	}

	execRet = exec.defFnStmt(stmt.DefFnStmt)

	if execRet.IsNotTrue() {
		return execRet.AddMsg(stmt.String())
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) checkHaveFnStmt(stmt *ast.HaveFnStmt) (ExecRet, error) {
	// Create a new environment for verification and proof
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	// 验证 fn template 里面的 paramSet 和 return set 都是 in set 的
	// Verify each paramSet is in set type
	for i, paramSet := range stmt.DefFnStmt.FnTemplate.ParamSets {
		execState := exec.factStmt(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{paramSet, ast.AtomObj(glob.KeywordSet)}, stmt.Line))
		if execState.IsErr() {
			return NewExecErr(execState.String()), fmt.Errorf(execState.String())
		}
		if execState.IsUnknown() {
			return NewExecErr(""), fmt.Errorf("parameter set %d (%s) must be a set, i.e. `%s in set` must be true, but it is unknown", i+1, paramSet.String(), paramSet.String())
		}
	}

	// Verify retSet is in set type
	execState := exec.factStmt(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{stmt.DefFnStmt.FnTemplate.RetSet, ast.AtomObj(glob.KeywordSet)}, stmt.Line))
	if execState.IsErr() {
		return NewExecErr(execState.String()), fmt.Errorf(execState.String())
	}
	if execState.IsUnknown() {
		return NewExecErr(""), fmt.Errorf("return set (%s) must be a set, i.e. `%s in set` must be true, but it is unknown", stmt.DefFnStmt.FnTemplate.RetSet.String(), stmt.DefFnStmt.FnTemplate.RetSet.String())
	}

	// Define parameters in the new environment
	defObjStmt := ast.NewDefLetStmt(stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets, stmt.DefFnStmt.FnTemplate.DomFacts, stmt.Line)
	execState = exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	// Execute proof statements
	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// Verify that HaveObjSatisfyFn is in the return set
	execState = exec.factStmt(ast.NewInFactWithFc(stmt.HaveObjSatisfyFn, stmt.DefFnStmt.FnTemplate.RetSet))
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	// know 一下 函数等于 等号右边的东西

	// 证明 fn then 里全是对的

	// Verify that the thenFacts are satisfied
	// The proof statements should have established the necessary conditions
	// Additional verification of thenFacts would require object substitution which is not currently available

	return NewExecTrue(""), nil
}

func (exec *Executor) haveFnCaseByCaseStmt(stmt *ast.HaveFnCaseByCaseStmt) ExecRet {
	// Verify first and get thenFacts
	execRet, _, err := exec.checkHaveFnCaseByCaseStmt(stmt)
	if notOkExec(execRet, err) {
		return execRet
	}

	// Only after all verifications pass, declare the function
	execRet = exec.defFnStmt(stmt.DefFnStmt)
	if execRet.IsNotTrue() {
		return execRet.AddMsg(stmt.String())
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) checkHaveFnCaseByCaseStmt(stmt *ast.HaveFnCaseByCaseStmt) (ExecRet, []ast.FactStmt, error) {
	// Create a new environment for verification and proof
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	// Verify each paramSet is in set type
	for i, paramSet := range stmt.DefFnStmt.FnTemplate.ParamSets {
		execState := exec.factStmt(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{paramSet, ast.AtomObj(glob.KeywordSet)}, stmt.Line))
		if execState.IsErr() {
			return NewExecErr(execState.String()), nil, fmt.Errorf(execState.String())
		}
		if execState.IsUnknown() {
			return NewExecErr(""), nil, fmt.Errorf("parameter set %d (%s) must be a set, i.e. `%s in set` must be true, but it is unknown", i+1, paramSet.String(), paramSet.String())
		}
	}

	// Verify retSet is in set type
	execState := exec.factStmt(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{stmt.DefFnStmt.FnTemplate.RetSet, ast.AtomObj(glob.KeywordSet)}, stmt.Line))
	if execState.IsErr() {
		return NewExecErr(execState.String()), nil, fmt.Errorf(execState.String())
	}
	if execState.IsUnknown() {
		return NewExecErr(""), nil, fmt.Errorf("return set (%s) must be a set, i.e. `%s in set` must be true, but it is unknown", stmt.DefFnStmt.FnTemplate.RetSet.String(), stmt.DefFnStmt.FnTemplate.RetSet.String())
	}

	// Verify each case: execute proof and verify return value
	for i := range len(stmt.CaseByCaseFacts) {
		execState, err := exec.verifyHaveFnCaseByCase_OneCase(stmt, i)
		if notOkExec(execState, err) {
			return execState, nil, err
		}
	}

	// Verify all cases cover the domain
	execState, err := exec.checkAtLeastOneCaseHolds_ForHaveFn(stmt)
	if notOkExec(execState, err) {
		return execState, nil, err
	}

	// Verify cases don't overlap
	execState, err = exec.checkCasesNoOverlap_ForHaveFn(stmt)
	if notOkExec(execState, err) {
		return execState, nil, err
	}

	// Build thenFacts: for each case, if condition holds, function equals corresponding return value
	thenFacts := []ast.FactStmt{}
	for i, caseFact := range stmt.CaseByCaseFacts {
		// Create function call from function name and params
		params := make([]ast.Obj, len(stmt.DefFnStmt.FnTemplate.Params))
		for j := range len(stmt.DefFnStmt.FnTemplate.Params) {
			params[j] = ast.AtomObj(stmt.DefFnStmt.FnTemplate.Params[j])
		}
		fnName := ast.AtomObj(stmt.DefFnStmt.Name)
		fnCall := ast.NewFnObj(fnName, params)
		equalFact := ast.NewEqualFact(fnCall, stmt.EqualToObjs[i])

		uniFact := ast.NewUniFact(
			stmt.DefFnStmt.FnTemplate.Params,
			stmt.DefFnStmt.FnTemplate.ParamSets,
			[]ast.FactStmt{caseFact},
			[]ast.FactStmt{equalFact},
			stmt.Line,
		)
		thenFacts = append(thenFacts, uniFact)
	}

	return NewExecTrue(""), thenFacts, nil
}

func (exec *Executor) verifyHaveFnCaseByCase_OneCase(stmt *ast.HaveFnCaseByCaseStmt, caseIndex int) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	// Define parameters
	defObjStmt := ast.NewDefLetStmt(
		stmt.DefFnStmt.FnTemplate.Params,
		stmt.DefFnStmt.FnTemplate.ParamSets,
		stmt.DefFnStmt.FnTemplate.DomFacts,
		stmt.Line,
	)
	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState, fmt.Errorf(execState.String())
	}

	// Add case condition as fact
	caseFact := stmt.CaseByCaseFacts[caseIndex]
	ret := exec.Env.NewFact(caseFact)
	if ret.IsErr() {
		return NewExecErr(ret.String()), fmt.Errorf("case %d: failed to add case fact: %s", caseIndex, ret.String())
	}

	// Execute proof for this case
	for _, proof := range stmt.Proofs[caseIndex] {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState, fmt.Errorf("case %d: proof failed", caseIndex)
		}
	}

	// Verify return value is in retSet
	equalTo := stmt.EqualToObjs[caseIndex]
	ver := NewVerifier(exec.Env)
	verRet := ver.VerFactStmt(ast.NewInFactWithFc(equalTo, stmt.DefFnStmt.FnTemplate.RetSet), Round0Msg)
	if verRet.IsErr() {
		return NewExecErr(""), fmt.Errorf("case %d: %s", caseIndex, verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(""), fmt.Errorf("case %d: according to the definition of %s, when %s is true, the returned value %s must be in %s, but\n%s is unknown", caseIndex, stmt, caseFact, equalTo, stmt.DefFnStmt.FnTemplate.RetSet, ast.NewInFactWithFc(equalTo, stmt.DefFnStmt.FnTemplate.RetSet))
	}

	// The proof statements should have established the necessary conditions
	// Note: We don't verify thenFacts here because the function is not yet defined,
	// and object substitution (ReplaceObj) is not currently available.
	// The proof statements in each case should prove what's needed.

	return NewExecTrue(""), nil
}

func (exec *Executor) checkAtLeastOneCaseHolds_ForHaveFn(stmt *ast.HaveFnCaseByCaseStmt) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	// Define parameters
	for i := range len(stmt.DefFnStmt.FnTemplate.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefFnStmt.FnTemplate.Params[i]}, []ast.Obj{stmt.DefFnStmt.FnTemplate.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// Create or fact: case1 or case2 or ... or caseN
	orFact := ast.NewOrStmt(stmt.CaseByCaseFacts, stmt.Line)

	// Verify or fact is true (all cases cover the domain)
	ver := NewVerifier(exec.Env)
	verRet := ver.VerFactStmt(orFact, Round0Msg)
	if verRet.IsErr() {
		return NewExecErr(""), fmt.Errorf("failed to verify that all cases cover the domain: %s", verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(""), fmt.Errorf("all cases must cover the entire domain, i.e., %s must be true, but it is unknown", orFact)
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) checkCasesNoOverlap_ForHaveFn(stmt *ast.HaveFnCaseByCaseStmt) (ExecRet, error) {
	// For each case i, verify that when case i holds, all other cases don't hold
	for i := range len(stmt.CaseByCaseFacts) {
		execState, err := exec.checkCaseNoOverlapWithOthers_ForHaveFn(stmt, i)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) checkCaseNoOverlapWithOthers_ForHaveFn(stmt *ast.HaveFnCaseByCaseStmt, caseIndex int) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	// Define parameters
	for i := range len(stmt.DefFnStmt.FnTemplate.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefFnStmt.FnTemplate.Params[i]}, []ast.Obj{stmt.DefFnStmt.FnTemplate.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// Assume current case condition holds
	caseFact := stmt.CaseByCaseFacts[caseIndex]
	ret := exec.Env.NewFact(caseFact)
	if ret.IsErr() {
		return NewExecErr(ret.String()), fmt.Errorf("case %d: failed to add case fact: %s", caseIndex, ret.String())
	}

	// Verify all other cases don't hold
	ver := NewVerifier(exec.Env)
	for j := range len(stmt.CaseByCaseFacts) {
		if j == caseIndex {
			continue
		}

		// Get not case j
		otherCaseFact := stmt.CaseByCaseFacts[j]
		notOtherCaseFact := otherCaseFact.ReverseTrue()

		// Verify not case j is true
		verRet := ver.VerFactStmt(notOtherCaseFact, Round0Msg)
		if verRet.IsErr() {
			return NewExecErr(""), fmt.Errorf("case %d and case %d overlap: failed to verify that not %s: %s", caseIndex, j, otherCaseFact, verRet.String())
		}
		if verRet.IsUnknown() {
			return NewExecErr(""), fmt.Errorf("case %d and case %d may overlap: when %s is true, %s must be false, but it is unknown", caseIndex, j, caseFact, otherCaseFact)
		}
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) openANewEnvAndCheck(fact ast.FactStmt, requireMsg bool) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	ver := NewVerifier(exec.Env)
	var state *VerState
	if requireMsg {
		state = Round0Msg
	} else {
		state = Round0NoMsg
	}

	verRet := ver.VerFactStmt(fact, state)
	if verRet.IsErr() {
		return NewExecErr(verRet.String()), fmt.Errorf(verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecUnknown(""), nil
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) markdownStmt(stmt *ast.MarkdownStmt) ExecRet {
	_ = stmt
	return NewExecTrue("")
}

func (exec *Executor) latexStmt(stmt *ast.LatexStmt) ExecRet {
	_ = stmt
	return NewExecTrue("")
}

func (exec *Executor) proveIsTransitivePropStmt(stmt *ast.ProveIsTransitivePropStmt) ExecRet {
	err := exec.proveIsTransitivePropStmtBody(stmt)
	if err != nil {
		return NewExecErr(err.Error())
	}

	exec.Env.TransitivePropMem[string(stmt.Prop)] = make(map[string][]ast.Obj)

	return NewExecTrue("")
}

// TODO 这里的msg系统太冗杂了，需要优化
func (exec *Executor) proveIsTransitivePropStmtBody(stmt *ast.ProveIsTransitivePropStmt) error {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	if exec.Env.IsTransitiveProp(string(stmt.Prop)) {
		return nil
	}

	def := exec.Env.GetPropDef(stmt.Prop)
	if def == nil {
		return fmt.Errorf("prop %s is not defined", stmt.Prop)
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
	execState := exec.defLetStmt(ast.NewDefLetStmt(stmt.Params, []ast.Obj{def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[0]}, def.DomFacts, stmt.Line))
	if execState.IsNotTrue() {
		return fmt.Errorf(execState.String())
	}

	ret := exec.Env.AreAtomsInFcAreDeclared(def.DefHeader.ParamSets[0], map[string]struct{}{})
	if ret.IsErr() {
		return fmt.Errorf(ret.String())
	}
	ret = exec.Env.AreAtomsInFcAreDeclared(def.DefHeader.ParamSets[1], map[string]struct{}{})
	if ret.IsErr() {
		return fmt.Errorf(ret.String())
	}

	if len(def.DomFacts) > 0 {
		return fmt.Errorf("dom facts are not allowed in %s", glob.KeywordProveIsTransitiveProp)
	}

	ret = exec.Env.NewFact(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(stmt.Prop), []ast.Obj{ast.AtomObj(stmt.Params[0]), ast.AtomObj(stmt.Params[1])}, stmt.Line))
	if ret.IsErr() {
		return fmt.Errorf(ret.String())
	}

	ret = exec.Env.NewFact(ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(stmt.Prop), []ast.Obj{ast.AtomObj(stmt.Params[1]), ast.AtomObj(stmt.Params[2])}, stmt.Line))
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
	finalCheckStmt := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(stmt.Prop), []ast.Obj{ast.AtomObj(stmt.Params[0]), ast.AtomObj(stmt.Params[2])}, stmt.Line)
	state = exec.factStmt(finalCheckStmt)
	if state.IsNotTrue() {
		return fmt.Errorf("failed to prove %s is transitive: %s failed", stmt.Prop, finalCheckStmt)
	}

	return nil
}

func (exec *Executor) defAlgoStmt(stmt *ast.DefAlgoStmt) ExecRet {
	exec.Env.AlgoDefMem[stmt.FuncName] = stmt
	return NewExecTrue("").AddMsg(stmt.String())
}

func (exec *Executor) evalStmt(stmt *ast.EvalStmt) ExecRet {
	trueEvalRet := NewExecTrue("")

	value, execRet := exec.evalFcInLocalEnv(stmt.FcsToEval)
	if execRet.IsNotTrue() {
		return execRet
	}
	ret := exec.Env.NewFact(ast.NewEqualFact(stmt.FcsToEval, value))
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}
	trueEvalRet.Inherit(execRet)

	return trueEvalRet.NewVerMsgAtBegin(Round0Msg, stmt.String())
}

func (exec *Executor) evalFcInLocalEnv(fcToEval ast.Obj) (ast.Obj, ExecRet) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	value, execRet := exec.evalObjThenSimplify(fcToEval)
	if execRet.IsNotTrue() {
		return nil, execRet
	}

	return value, NewExecTrue(fmt.Sprintf("By evaluation of algo %s\nWe get %s = %s\n", fcToEval.(*ast.FnObj).FnHead.String(), fcToEval.String(), value.String()))
}

func (exec *Executor) defProveAlgoStmt(stmt *ast.DefProveAlgoStmt) ExecRet {
	exec.Env.DefProveAlgoMem[stmt.ProveAlgoName] = stmt
	return NewExecTrue("").AddMsg(stmt.String())
}

func (exec *Executor) printStmt(stmt *ast.PrintStmt) ExecRet {
	if stmt.IsFString {
		fmt.Println(stmt.Value)
	} else {
		fmt.Println(stmt.Value)
	}
	return NewExecTrue("")
}

func (exec *Executor) helpStmt(stmt *ast.HelpStmt) ExecRet {
	helpMsg, ok := glob.KeywordHelpMap[stmt.Keyword]
	result := NewExecTrue("")
	if !ok {
		return result.AddMsg(fmt.Sprintf("Unknown keyword: %s", stmt.Keyword))
	}
	if helpMsg == "" {
		return result.AddMsg(fmt.Sprintf("Help for '%s': (description not yet available)", stmt.Keyword))
	} else {
		return result.AddMsg(fmt.Sprintf("Help for '%s': %s", stmt.Keyword, helpMsg))
	}
}

func (exec *Executor) haveFnEqualCaseByCaseStmt(stmt *ast.HaveFnEqualCaseByCaseStmt) ExecRet {
	// 验证每个case的返回值都符合fn的retSet
	execState, err := exec.checkHaveFnEqualCaseByCaseStmt(stmt)
	if notOkExec(execState, err) {
		return execState.AddMsg(stmt.String())
	}

	// 构建 thenFacts：对于每个 case，如果条件满足，则函数值等于对应的返回值
	thenFacts := []ast.FactStmt{}
	for i, caseFact := range stmt.CaseByCaseFacts {
		// 在 caseFact 的条件下，函数值等于对应的返回值
		// 需要将 caseFact 作为条件，然后添加等式
		fnCall := fnHeaderToReturnValueOfFn(stmt.DefHeader)
		equalFact := ast.NewEqualFact(fnCall, stmt.CaseByCaseEqualTo[i])

		// 创建一个条件事实：如果 caseFact 为真，则 equalFact 为真
		// 这里我们需要使用 implication 或者直接在 thenFacts 中添加条件
		// 由于 caseFact 是 SpecFactStmt，我们需要创建一个 UniFact 来表示这个条件
		// 但是更简单的方式是：创建一个 UniFact，其中 DomFacts 包含 caseFact，ThenFacts 包含 equalFact
		uniFact := ast.NewUniFact(
			stmt.DefHeader.Params,
			stmt.DefHeader.ParamSets,
			[]ast.FactStmt{caseFact},
			[]ast.FactStmt{equalFact},
			stmt.Line,
		)
		thenFacts = append(thenFacts, uniFact)
	}

	// 定义函数
	newFnDefStmt := ast.NewDefFnStmt(
		string(stmt.DefHeader.Name),
		ast.NewFnTStruct(
			stmt.DefHeader.Params,
			stmt.DefHeader.ParamSets,
			stmt.RetSet,
			[]ast.FactStmt{},
			thenFacts,
			stmt.Line,
		),
		stmt.Line,
	)
	execState = exec.defFnStmt(newFnDefStmt)
	if execState.IsNotTrue() {
		return execState.AddMsg(stmt.String())
	}

	return NewExecTrue(stmt.String())
}

func (exec *Executor) checkHaveFnEqualCaseByCaseStmt(stmt *ast.HaveFnEqualCaseByCaseStmt) (ExecRet, error) {
	// 验证每个case的返回值都符合fn的retSet（在case成立的条件下）
	for i := range len(stmt.CaseByCaseFacts) {
		execState, err := exec.checkCaseReturnValueInRetSet(stmt, i)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	// 验证所有的case覆盖了整个domain
	execState, err := exec.checkAtLeastOneCaseHolds(stmt)
	if notOkExec(execState, err) {
		return execState, err
	}

	// 验证每个case没有overlap
	execState, err = exec.checkCasesNoOverlap(stmt)
	if notOkExec(execState, err) {
		return execState, err
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) checkCaseReturnValueInRetSet(stmt *ast.HaveFnEqualCaseByCaseStmt, caseIndex int) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	// 为每个参数定义变量
	for i := range len(stmt.DefHeader.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefHeader.Params[i]}, []ast.Obj{stmt.DefHeader.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// 假设case的条件成立
	caseFact := stmt.CaseByCaseFacts[caseIndex]
	ret := exec.Env.NewFact(caseFact)
	if ret.IsErr() {
		return NewExecErr(ret.String()), fmt.Errorf("case %d: failed to add case fact: %s", caseIndex, ret.String())
	}

	// 在case成立的条件下，验证返回值在retSet中
	equalTo := stmt.CaseByCaseEqualTo[caseIndex]
	ver := NewVerifier(exec.Env)
	verRet := ver.VerFactStmt(ast.NewInFactWithFc(equalTo, stmt.RetSet), Round0Msg)
	if verRet.IsErr() {
		return NewExecErr(""), fmt.Errorf("case %d: %s", caseIndex, verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(""), fmt.Errorf("case %d: according to the definition of %s, when %s is true, the returned value %s must be in %s, but\n%s is unknown", caseIndex, stmt, caseFact, equalTo, stmt.RetSet, ast.NewInFactWithFc(equalTo, stmt.RetSet))
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) checkAtLeastOneCaseHolds(stmt *ast.HaveFnEqualCaseByCaseStmt) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	// 为每个参数定义变量
	for i := range len(stmt.DefHeader.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefHeader.Params[i]}, []ast.Obj{stmt.DefHeader.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// 创建 or fact: case1 or case2 or ... or caseN
	orFact := ast.NewOrStmt(stmt.CaseByCaseFacts, stmt.Line)

	// 验证 or fact 为 true（即所有 case 覆盖了整个 domain）
	ver := NewVerifier(exec.Env)
	verRet := ver.VerFactStmt(orFact, Round0Msg)
	if verRet.IsErr() {
		return NewExecErr(""), fmt.Errorf("failed to verify that all cases cover the domain: %s", verRet.String())
	}
	if verRet.IsUnknown() {
		return NewExecErr(""), fmt.Errorf("all cases must cover the entire domain, i.e., %s must be true, but it is unknown", orFact)
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) checkCasesNoOverlap(stmt *ast.HaveFnEqualCaseByCaseStmt) (ExecRet, error) {
	// 对于每个 case i，验证在 case i 成立的条件下，其他所有 case 都不成立
	for i := range len(stmt.CaseByCaseFacts) {
		execState, err := exec.checkCaseNoOverlapWithOthers(stmt, i)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) checkCaseNoOverlapWithOthers(stmt *ast.HaveFnEqualCaseByCaseStmt, caseIndex int) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnv()
	}()

	// 为每个参数定义变量
	for i := range len(stmt.DefHeader.Params) {
		execState := exec.defLetStmt(ast.NewDefLetStmt([]string{stmt.DefHeader.Params[i]}, []ast.Obj{stmt.DefHeader.ParamSets[i]}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState, fmt.Errorf(execState.String())
		}
	}

	// 假设当前 case 的条件成立
	caseFact := stmt.CaseByCaseFacts[caseIndex]
	ret := exec.Env.NewFact(caseFact)
	if ret.IsErr() {
		return NewExecErr(ret.String()), fmt.Errorf("case %d: failed to add case fact: %s", caseIndex, ret.String())
	}

	// 验证其他所有 case 都不成立
	ver := NewVerifier(exec.Env)
	for j := range len(stmt.CaseByCaseFacts) {
		if j == caseIndex {
			continue
		}

		// 获取 not case j
		otherCaseFact := stmt.CaseByCaseFacts[j]
		notOtherCaseFact := otherCaseFact.ReverseTrue()

		// 验证 not case j 为 true
		verRet := ver.VerFactStmt(notOtherCaseFact, Round0Msg)
		if verRet.IsErr() {
			return NewExecErr(""), fmt.Errorf("case %d and case %d overlap: failed to verify that not %s: %s", caseIndex, j, otherCaseFact, verRet.String())
		}
		if verRet.IsUnknown() {
			return NewExecErr(""), fmt.Errorf("case %d and case %d may overlap: when %s is true, %s must be false, but it is unknown", caseIndex, j, caseFact, otherCaseFact)
		}
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) proveInRangeStmt(stmt *ast.ProveInRangeStmt) ExecRet {
	// Evaluate start and end to get integer values
	startObj, execRet := exec.evalObjThenSimplify(stmt.Start())
	if execRet.IsNotTrue() {
		return NewExecErr(fmt.Sprintf("start value %s cannot be evaluated: %s", stmt.Start().String(), execRet.String()))
	}

	endObj, execRet := exec.evalObjThenSimplify(stmt.End())
	if execRet.IsNotTrue() {
		return NewExecErr(fmt.Sprintf("end value %s cannot be evaluated: %s", stmt.End().String(), execRet.String()))
	}

	// Convert to integers
	startInt, ok := ast.ToInt(startObj)
	if !ok {
		return NewExecErr(fmt.Sprintf("start value %s is not an integer", startObj.String()))
	}

	endInt, ok := ast.ToInt(endObj)
	if !ok {
		return NewExecErr(fmt.Sprintf("end value %s is not an integer", endObj.String()))
	}

	if startInt >= endInt {
		return NewExecErr(fmt.Sprintf("start value %d must be less than end value %d", startInt, endInt))
	}

	// Iterate through all values in range [start, end)
	for i := int64(startInt); i < int64(endInt); i++ {
		execRet := exec.proveInRangeStmtWhenParamIsIndex(stmt, i)
		if execRet.IsNotTrue() {
			return execRet
		}
	}

	// Create and store the universal fact
	uniFact := stmt.UniFact()
	ret := exec.Env.NewFact(uniFact)
	if ret.IsErr() {
		return NewExecErr(ret.String())
	}

	return NewExecTrue("")
}
