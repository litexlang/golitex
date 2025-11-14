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
	"strings"
)

func (exec *Executor) Stmt(stmt ast.Stmt) ExecRet {
	// var err error = nil
	var execState ExecRet = NewExecTrue("")

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		execState = exec.factStmt(stmt)
	case *ast.KnowFactStmt:
		exec.newMsg("Warning: `know` is design in such a way that it is possible to introduce invalid facts without verification If you want to introduce default facts, then use it; otherwise, use it carefully.")
		execState = exec.knowStmt(stmt)
	case *ast.KnowPropStmt:
		exec.newMsg("Warning: `know @` is design in such a way that it is possible to introduce invalid facts without verification If you want to introduce default facts, then use it; otherwise, use it carefully.")
		execState = exec.knowPropStmt(stmt)
	case *ast.ClaimProveStmt:
		execState = exec.execClaimStmtProve(stmt)
	case *ast.DefPropStmt:
		execState = exec.defPropStmt(stmt, true)
	case *ast.DefLetStmt:
		exec.newMsg("Warning: `let` is design in such a way that it is possible to introduce non-existent objects. If you want to ensure the existence of this object, use `have` instead.")
		execState = exec.defLetStmt(stmt)
	case *ast.HaveObjStStmt:
		execState = exec.haveObjStStmt(stmt, true)
	case *ast.DefExistPropStmt:
		execState = exec.defExistPropStmt(stmt)
	case *ast.DefFnStmt:
		exec.newMsg("Warning: `fn` is design in such a way that it is possible to introduce non-existent objects. If you want to ensure the existence of this function, use `have fn` instead.")
		execState = exec.defFnStmt(stmt)
	case *ast.ProveInEachCaseStmt:
		execState = exec.proveInEachCaseStmt(stmt)
	case *ast.ClaimPropStmt:
		execState = exec.claimPropStmt(stmt)
	case *ast.ClaimExistPropStmt:
		execState = exec.claimExistPropStmt(stmt)
	case *ast.ProveStmt:
		execState = exec.proveStmt(stmt)
	case *ast.ClaimProveByContradictionStmt:
		execState = exec.execClaimStmtProveByContradiction(stmt)
	case *ast.ProveByEnumStmt:
		execState = exec.proveByEnumStmt(stmt)
	case *ast.HaveObjInNonEmptySetStmt:
		execState = exec.haveObjInNonEmptySetStmt(stmt)
	case *ast.HaveEnumSetStmt:
		execState = exec.haveEnumSetStmt(stmt)
	case *ast.HaveIntensionalSetStmt:
		execState = exec.haveIntensionalSetStmt(stmt)
	case *ast.HaveSetFnStmt:
		execState = exec.haveSetFnStmt(stmt)
	case *ast.HaveSetDefinedByReplacementStmt:
		execState = exec.haveSetDefinedByReplacementStmt(stmt)
	case *ast.NamedUniFactStmt:
		execState = exec.namedUniFactStmt(stmt)
	case *ast.KnowExistPropStmt:
		exec.newMsg("Warning: `know exist` is design in such a way that it is possible to introduce invalid facts without verification If you want to introduce default facts, then use it; otherwise, use it carefully.")
		execState = exec.knowExistPropStmt(stmt)
	case *ast.FnTemplateDefStmt:
		execState = exec.DefFnTemplateStmt(stmt)
	case *ast.ClearStmt:
		exec.ClearStmt()
	case *ast.InlineFactsStmt:
		execState = exec.inlineFactsStmt(stmt)
	case *ast.ProveByInductionStmt:
		execState = exec.proveByInductionStmt(stmt)
	case *ast.HaveObjEqualStmt:
		execState = exec.haveObjEqualStmt(stmt)
	case *ast.HaveFnEqualStmt:
		execState = exec.haveFnEqualStmt(stmt)
	case *ast.HaveFnLiftStmt:
		execState = exec.haveFnLiftStmt(stmt)
	case *ast.HaveFnStmt:
		execState = exec.haveFnStmt(stmt)
	case *ast.MarkdownStmt:
		execState = exec.markdownStmt(stmt)
		return execState
	case *ast.LatexStmt:
		execState = exec.latexStmt(stmt)
		return execState
	case *ast.ClaimIffStmt:
		execState = exec.claimIffStmt(stmt)
	case *ast.ProveInRangeStmt:
		execState = exec.proveInRangeStmt(stmt)
	case *ast.ProveIsTransitivePropStmt:
		execState = exec.proveIsTransitivePropStmt(stmt)
	case *ast.ProveIsCommutativePropStmt:
		execState = exec.proveIsCommutativePropStmt(stmt)
	case *ast.DefAlgoStmt:
		execState = exec.defAlgoStmt(stmt)
	case *ast.EvalStmt:
		execState = exec.evalStmt(stmt)
	case *ast.DefProveAlgoStmt:
		execState = exec.defProveAlgoStmt(stmt)
	case *ast.ByStmt:
		execState = exec.byStmt(stmt)
	case *ast.PrintStmt:
		execState = exec.printStmt(stmt)
	case *ast.HaveFnEqualCaseByCaseStmt:
		execState = exec.haveFnEqualCaseByCaseStmt(stmt)
	default:
		panic(fmt.Sprintf("unknown statement type: %T", stmt))
	}

	// if err != nil || execState.IsErr() {
	// 	if err != nil && err.Error() != "" {
	// 		return NewExecErr(""), "", fmt.Errorf("failed: line %d:\n%w", stmt.GetLine(), err)
	// 	} else {
	// 		return NewExecErr(""), "", fmt.Errorf("failed: line %d", stmt.GetLine())
	// 	}
	// } else
	if execState.IsTrue() {
		exec.newMsg(fmt.Sprintf("%s\n", execState.String()))
		return NewExecTrue(fmt.Sprintf("Success! line %d\n", stmt.GetLine()))
	} else if execState.IsUnknown() {
		return NewExecUnknown(fmt.Sprintf("Unknown: line %d\n", stmt.GetLine()))
	} else {
		return NewExecErr(fmt.Sprintf("Execution Error: line %d\n%s", stmt.GetLine(), execState.String()))
	}
}

func (exec *Executor) factStmt(stmt ast.FactStmt) ExecRet {
	curVerifier := NewVerifier(exec.Env)
	state := Round0Msg
	verRet := curVerifier.VerFactStmt(stmt, state)

	if verRet.IsErr() {
		return NewExecErr(verRet.String())
	} else if verRet.IsTrue() {
		err := exec.Env.NewFact(stmt)
		if err != nil {
			return NewExecErr(err.Error())
		}
		if verRet.(*ExecTrue).TrueEqualValues != nil {
			if verRet.(*ExecTrue).TrueEqualValues[0] != nil {
				exec.Env.StoreTrueEqualValues(stmt.(*ast.SpecFactStmt).Params[1], verRet.(*ExecTrue).TrueEqualValues[0])
			}
			if verRet.(*ExecTrue).TrueEqualValues[1] != nil {
				exec.Env.StoreTrueEqualValues(stmt.(*ast.SpecFactStmt).Params[0], verRet.(*ExecTrue).TrueEqualValues[1])
			}
		}
		return NewExecTrue("")
	} else if verRet.IsUnknown() {
		return NewExecUnknown("")
	} else {
		panic("unknown ver ret")
	}
}

// TODO: 再know时就检查，仅仅依赖写在dom里的事实，是否真的能让涉及到的函数和prop能真的满足条件。如果不满足条件，那就warning
func (exec *Executor) knowStmt(stmt *ast.KnowFactStmt) ExecRet {
	for _, fact := range stmt.Facts {
		switch fact := fact.(type) {
		case ast.FactStmt:
			if !exec.Env.AreAtomsInFactAreDeclared(fact, map[string]struct{}{}) {
				return NewExecErr(env.AtomsInFactNotDeclaredMsg(fact))
			}

			err := exec.Env.NewFact(fact)
			if err != nil {
				return NewExecErr(err.Error())
			}

		case *ast.KnowPropStmt:
			execRet := exec.knowPropStmt(fact)
			if execRet.IsNotTrue() {
				return execRet
			}
		default:
			return NewExecErr(fmt.Sprintf("unknown fact type: %T", fact))
		}
	}

	exec.newMsg(fmt.Sprintf("%s\n", stmt.String()))
	return NewExecTrue(fmt.Sprintf("%s\n", stmt.String()))
}

func (exec *Executor) GetMsgAsStr0ToEnd() string {
	ret := strings.Join(exec.Env.Msgs, "\n")
	exec.Env.Msgs = []string{}
	return ret
}

func (exec *Executor) defPropStmt(stmt *ast.DefPropStmt, generateIffUniFact bool) ExecRet {
	err := exec.Env.NewDefProp_InsideAtomsDeclared(stmt)
	if err != nil {
		return NewExecErr(err.Error())
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

		err = exec.Env.NewFact(propToIff)
		if err != nil {
			return NewExecErr(err.Error())
		}
		exec.newMsg(fmt.Sprintf("%s\nis true by definition", propToIff))

		err = exec.Env.NewFact(iffToProp)
		if err != nil {
			return NewExecErr(err.Error())
		}
		exec.newMsg(fmt.Sprintf("%s\nis true by definition", iffToProp))
	}
	return NewExecTrue("")
}

func (exec *Executor) defLetStmt(stmt *ast.DefLetStmt) ExecRet {
	// if glob.RequireMsg() && requireMsg {
	// 	defer exec.newMsg(fmt.Sprintf("%s\n", stmt))
	// }

	return NewDefObj_InsideAtomsDeclared(exec.Env, stmt)
}

func (exec *Executor) defExistPropStmt(stmt *ast.DefExistPropStmt) ExecRet {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	// if glob.RequireMsg() {
	// 	defer exec.newMsg(fmt.Sprintf("%s\n", stmt))
	// }

	err := exec.Env.NewDefExistProp_InsideAtomsDeclared(stmt)
	if err != nil {
		return NewExecErr(err.Error())
	}
	return NewExecTrue("")
}

// TODO: 我认为打印一下 claim 里面的各个语句的输出还是有道理的
func (exec *Executor) execStmtsAtCurEnv(proof []ast.Stmt) ExecRet {
	for _, curStmt := range proof {
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			exec.newMsg(fmt.Sprintf("%s\nfailed :( line %d\n", curStmt.String(), curStmt.GetLine()))
			return execState
		}
	}
	return NewExecTrue("")
}

func (exec *Executor) proveInEachCaseStmt(stmt *ast.ProveInEachCaseStmt) ExecRet {
	isSuccess := false
	defer func() {
		exec.newMsg("\n")
		if isSuccess {
			exec.appendNewMsgAtBegin("is true\n")
		} else {
			exec.appendNewMsgAtBegin("is unknown\n")
		}
		exec.appendNewMsgAtBegin(stmt.String())
	}()

	// prove orFact is true
	execState := exec.factStmt(stmt.OrFact)
	if execState.IsNotTrue() {
		exec.newMsg(fmt.Sprintf("%s is unknown", stmt.OrFact.String()))
		return execState
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
	return NewExecTrue("")
}

func (exec *Executor) execProofBlockForEachCase(index int, stmt *ast.ProveInEachCaseStmt) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndRetainMsg()

	caseStmt := stmt.OrFact.Facts[index]

	err := exec.Env.NewFact(caseStmt)
	if err != nil {
		return NewExecErr(""), err
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
		err = exec.Env.NewFact(iffToProp)
		if err != nil {
			return NewExecErr(err.Error())
		}
	}

	paramsAsFc := []ast.Obj{}
	for i := range stmt.Prop.DefHeader.Params {
		paramsAsFc = append(paramsAsFc, ast.FcAtom(stmt.Prop.DefHeader.Params[i]))
	}

	uniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(stmt.Prop.DefHeader.Name), paramsAsFc, stmt.Line)}, stmt.Prop.ThenFacts, stmt.Line)

	err := exec.Env.NewFact(uniFact)
	if err != nil {
		return NewExecErr(err.Error())
	}

	uniFact2 := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.ParamSets, stmt.Prop.IffFacts, stmt.Prop.ThenFacts, stmt.Line)
	err = exec.Env.NewFact(uniFact2)
	if err != nil {
		return NewExecErr(err.Error())
	}

	return NewExecTrue(fmt.Sprintf("%s\n", stmt.String()))
}

func (exec *Executor) proveStmt(stmt *ast.ProveStmt) ExecRet {
	// new env
	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndRetainMsg()

	execState := exec.execStmtsAtCurEnv(stmt.Proof)
	if execState.IsNotTrue() {
		return execState
	}
	return execState
}

func (exec *Executor) defFnStmt(stmt *ast.DefFnStmt) ExecRet {
	err := exec.Env.IsValidIdentifierAvailable(stmt.Name)
	if err != nil {
		return NewExecErr(err.Error())
	}

	// 在 objMem 里记录一下
	exec.Env.ObjDefMem[stmt.Name] = nil

	err = exec.Env.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(ast.FcAtom(stmt.Name), nil, stmt.FnTemplate)
	if err != nil {
		return NewExecErr(err.Error())
	}

	derivedFact, err := stmt.FnTemplate.DeriveUniFact_WithGivenFn(ast.FcAtom(stmt.Name))
	if err != nil {
		return NewExecErr(err.Error())
	}

	err = exec.Env.NewFact(derivedFact)
	if err != nil {
		return NewExecErr(err.Error())
	}

	return NewExecTrue("")
}

func (exec *Executor) proveByEnumStmt(stmt *ast.ProveByEnumStmt) ExecRet {
	// exec.newMsg(stmt.String())

	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndRetainMsg()

	execState, err := exec.proveByEnumMainLogic(stmt)
	if notOkExec(execState, err) {
		return execState
	}

	// know uniFact
	err = exec.Env.Parent.NewFact(stmt.Fact)
	if err != nil {
		return NewExecErr(err.Error())
	}

	return NewExecTrue("")
}

func (exec *Executor) haveSetFnStmt(stmt *ast.HaveSetFnStmt) ExecRet {
	// exec.newMsg(stmt.String())

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
	// exec.newMsg(stmt.String())

	setDefinedByReplacement := ast.NewFcFn(ast.FcAtom(glob.KeywordSetDefinedByReplacement), []ast.Obj{stmt.DomSet, stmt.RangeSet, stmt.PropName})

	defObjStmt := ast.NewDefLetStmt([]string{stmt.Name}, []ast.Obj{ast.FcAtom(glob.KeywordSet)}, []ast.FactStmt{ast.NewEqualFact(ast.FcAtom(stmt.Name), setDefinedByReplacement)}, stmt.Line)

	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	err := exec.Env.SetEqualToSetDefinedByReplacement_PostProcess(ast.FcAtom(stmt.Name), setDefinedByReplacement)
	if err != nil {
		return NewExecErr(err.Error())
	}

	return NewExecTrue("")
}

func (exec *Executor) namedUniFactStmt(stmt *ast.NamedUniFactStmt) ExecRet {
	// exec.newMsg(stmt.String())

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

	err := exec.Env.NewFact(knownUniFact)
	if err != nil {
		return NewExecErr(err.Error())
	}

	exec.newMsg(fmt.Sprintf("%s\nis true by definition", knownUniFact))

	return NewExecTrue("")
}

func (exec *Executor) DefFnTemplateStmt(stmt *ast.FnTemplateDefStmt) ExecRet {
	// if glob.RequireMsg() {
	// 	defer exec.newMsg(fmt.Sprintf("%s\n", stmt))
	// }

	err := exec.Env.ExecDefFnTemplate(stmt)
	if err != nil {
		return NewExecErr(err.Error())
	}

	return NewExecTrue("")
}

func (exec *Executor) ClearStmt() error {
	curEnv := exec.Env
	for curEnv.Parent != nil {
		curEnv = curEnv.Parent
	} // 最顶层的env不删，因为最顶层的包含了热启动的代码
	exec.NewEnv(curEnv)
	exec.newMsg("clear\n")
	return nil
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
		verRet := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Obj{stmt.ObjEqualTos[i], stmt.ObjSets[i]}, stmt.Line), Round0Msg)
		if verRet.IsErr() {
			return NewExecErr(verRet.String())
		}
		if verRet.IsUnknown() {
			return NewExecErr(fmt.Sprintf("%s is not in %s", stmt.ObjNames[i], stmt.ObjSets[i]))
		}

		execState := NewDefObj_InsideAtomsDeclared(exec.Env, ast.NewDefLetStmt([]string{stmt.ObjNames[i]}, []ast.Obj{ast.FcAtom(glob.KeywordObj)}, []ast.FactStmt{}, stmt.Line))
		if execState.IsNotTrue() {
			return execState
		}
		// 检查 等号右边的东西是否存在
		ok := exec.Env.AreAtomsInFcAreDeclared(stmt.ObjEqualTos[i], map[string]struct{}{})
		if !ok {
			return NewExecErr(fmt.Sprintf("%s is not declared", stmt.ObjEqualTos[i]))
		}
		// new fact: obj = obj
		err := exec.Env.NewFact(ast.NewEqualFact(ast.FcAtom(stmt.ObjNames[i]), stmt.ObjEqualTos[i]))
		if err != nil {
			return NewExecErr(err.Error())
		}
	}

	return NewExecTrue("")
}

func (exec *Executor) haveFnEqualStmt(stmt *ast.HaveFnEqualStmt) ExecRet {
	execState, err := exec.checkFnEqualStmt(stmt)
	if notOkExec(execState, err) {
		return execState
	}

	newFnDefStmt := ast.NewDefFnStmt(string(stmt.DefHeader.Name), ast.NewFnTStruct(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, stmt.RetSet, []ast.FactStmt{}, []ast.FactStmt{ast.NewEqualFact(fnHeaderToReturnValueOfFn(stmt.DefHeader), stmt.EqualTo)}, stmt.Line), stmt.Line)
	execState = exec.defFnStmt(newFnDefStmt)
	if execState.IsNotTrue() {
		return NewExecErr(fmt.Sprintf("failed to declare fn: %s", newFnDefStmt.String()))
	}

	return NewExecTrue("")
}

func (exec *Executor) checkFnEqualStmt(stmt *ast.HaveFnEqualStmt) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer func() {
		exec.deleteEnvAndRetainMsg()
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
		params[i] = ast.FcAtom(head.Params[i])
	}

	fnName := ast.FcAtom(head.Name)

	return ast.NewFcFn(fnName, params)
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
		head := ast.NewFcFn(ast.FcAtom(glob.KeywordFn), stmt.DomainOfEachParamOfGivenFn)
		FnTemplateOfFunctions = append(FnTemplateOfFunctions, ast.NewFcFn(head, []ast.Obj{optDef.AsFnTStruct.ParamSets[i]}))
	}

	retSet := ast.NewFcFn(ast.NewFcFn(ast.FcAtom(glob.KeywordFn), stmt.DomainOfEachParamOfGivenFn), []ast.Obj{optDef.AsFnTStruct.RetSet})

	// randomly generate len different params
	randomParams := glob.GenerateUniqueRandomStrings(len(FnTemplateOfFunctions))

	knownUniFact := exec.haveFnLift_knowFact(stmt, randomParams)

	fnDef := ast.NewDefFnStmt(stmt.FnName, ast.NewFnTStruct(randomParams, FnTemplateOfFunctions, retSet, []ast.FactStmt{}, []ast.FactStmt{knownUniFact}, stmt.Line), stmt.Line)

	execState := exec.defFnStmt(fnDef)
	if execState.IsNotTrue() {
		return NewExecErr(fmt.Sprintf("failed to declare fn: %s", fnDef.String()))
	}

	exec.newMsg(fmt.Sprintf("Declare Function by lifting:\n%s\n", fnDef))

	return NewExecTrue("")
}

func (exec *Executor) haveFnLift_knowFact(stmt *ast.HaveFnLiftStmt, fnNames []string) *ast.UniFactStmt {
	// fn a(f fn(DOMAIN_of_x, DOMAIN_of_y, ...)OPT_PRAM0_DOM, g fn(DOMAIN_of_x, DOMAIN_of_y, ...)OPT_PRAM1_DOM, ...) fn(DOMAIN_of_x, DOMAIN_of_y, ...) opt_ret:
	// 	forall x DOMAIN_of_x, y DOMAIN_of_y, ...:
	// 		a(f, g, ...)(x, y, z, ...) = opt(f(x,y,z...) , g(x,y,z,...), ...)

	// have a = lift(opt, DOMAIN_of_x, DOMAIN_of_y, ...)

	uniFactParams := glob.GenerateUniqueRandomStrings_NotInGivenStrSlice(len(stmt.DomainOfEachParamOfGivenFn), fnNames)
	uniFactParamsAsFc := []ast.Obj{}
	for i := range len(uniFactParams) {
		uniFactParamsAsFc = append(uniFactParamsAsFc, ast.FcAtom(uniFactParams[i]))
	}

	fnNamesAsFc := []ast.Obj{}
	for i := range len(fnNames) {
		fnNamesAsFc = append(fnNamesAsFc, ast.FcAtom(fnNames[i]))
	}

	uniFactParamSets := stmt.DomainOfEachParamOfGivenFn
	lhs := ast.NewFcFn(ast.NewFcFn(ast.FcAtom(stmt.FnName), fnNamesAsFc), uniFactParamsAsFc)

	rhsParams := []ast.Obj{}
	for i := range len(fnNamesAsFc) {
		rhsParams = append(rhsParams, ast.NewFcFn(ast.FcAtom(fnNames[i]), uniFactParamsAsFc))
	}

	rhs := ast.NewFcFn(stmt.Opt, rhsParams)

	return ast.NewUniFact(uniFactParams, uniFactParamSets, []ast.FactStmt{}, []ast.FactStmt{ast.NewEqualFact(lhs, rhs)}, stmt.Line)
}

func (exec *Executor) haveFnStmt(stmt *ast.HaveFnStmt) ExecRet {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndRetainMsg()

	defObjStmt := ast.NewDefLetStmt(stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets, stmt.DefFnStmt.FnTemplate.DomFacts, stmt.Line)
	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState
		}
	}

	fcDerivedFromFnName := ast.NewFcFn(ast.FcAtom(stmt.DefFnStmt.Name), stmt.DefFnStmt.FnTemplate.Params.ToFcSlice())

	// prove return value in newRetFc
	execState = exec.factStmt(ast.NewInFactWithFc(stmt.HaveObjSatisfyFn, stmt.DefFnStmt.FnTemplate.RetSet))
	if execState.IsNotTrue() {
		return execState
	}

	newThenFacts := []ast.FactStmt{}
	for _, thenFact := range stmt.DefFnStmt.FnTemplate.ThenFacts {
		newThenFacts = append(newThenFacts, thenFact.ReplaceFc(fcDerivedFromFnName, stmt.HaveObjSatisfyFn))
	}

	for _, thenFact := range newThenFacts {
		execState := exec.factStmt(thenFact)
		if execState.IsNotTrue() {
			return execState
		}
	}

	return NewExecTrue("")
}

func (exec *Executor) openANewEnvAndCheck(fact ast.FactStmt, requireMsg bool) (ExecRet, error) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndRetainMsg()

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
	defer exec.deleteEnvAndRetainMsg()

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

	ok := exec.Env.AreAtomsInFcAreDeclared(def.DefHeader.ParamSets[0], map[string]struct{}{})
	if !ok {
		return fmt.Errorf("param %s is not declared", def.DefHeader.ParamSets[0])
	}
	ok = exec.Env.AreAtomsInFcAreDeclared(def.DefHeader.ParamSets[1], map[string]struct{}{})
	if !ok {
		return fmt.Errorf("param %s is not declared", def.DefHeader.ParamSets[1])
	}

	if len(def.DomFacts) > 0 {
		return fmt.Errorf("dom facts are not allowed in %s", glob.KeywordProveIsTransitiveProp)
	}

	err := exec.Env.NewFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(stmt.Prop), []ast.Obj{ast.FcAtom(stmt.Params[0]), ast.FcAtom(stmt.Params[1])}, stmt.Line))
	if err != nil {
		return err
	}

	err = exec.Env.NewFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(stmt.Prop), []ast.Obj{ast.FcAtom(stmt.Params[1]), ast.FcAtom(stmt.Params[2])}, stmt.Line))
	if err != nil {
		return err
	}

	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if notOkExec(execState, err) {
			return fmt.Errorf(execState.String())
		}
	}

	// check
	finalCheckStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(stmt.Prop), []ast.Obj{ast.FcAtom(stmt.Params[0]), ast.FcAtom(stmt.Params[2])}, stmt.Line)
	state = exec.factStmt(finalCheckStmt)
	if state.IsNotTrue() {
		return fmt.Errorf("failed to prove %s is transitive: %s failed", stmt.Prop, finalCheckStmt)
	}

	return nil
}

func (exec *Executor) defAlgoStmt(stmt *ast.DefAlgoStmt) ExecRet {
	exec.Env.AlgoDefMem[stmt.FuncName] = stmt
	exec.newMsg(stmt.String())
	return NewExecTrue("")
}

func (exec *Executor) evalStmt(stmt *ast.EvalStmt) ExecRet {
	trueEvalRet := NewExecTrue("")

	value, execRet := exec.evalFcInLocalEnv(stmt.FcsToEval)
	if execRet.IsNotTrue() {
		return execRet
	}
	err := exec.Env.NewFact(ast.NewEqualFact(stmt.FcsToEval, value))
	if err != nil {
		return NewExecErrWithErr(err)
	}
	trueEvalRet.Inherit(execRet)

	return trueEvalRet.NewVerMsgAtBegin(Round0Msg, stmt.String())
}

func (exec *Executor) evalFcInLocalEnv(fcToEval ast.Obj) (ast.Obj, ExecRet) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndRetainMsg()

	value, execRet := exec.evalFcThenSimplify(fcToEval)
	if execRet.IsNotTrue() {
		return nil, execRet
	}

	return value, NewExecTrue(fmt.Sprintf("By evaluation of algo %s\nWe get %s = %s\n", fcToEval.(*ast.FcFn).FnHead.String(), fcToEval.String(), value.String()))
}

func (exec *Executor) defProveAlgoStmt(stmt *ast.DefProveAlgoStmt) ExecRet {
	exec.Env.DefProveAlgoMem[stmt.ProveAlgoName] = stmt
	exec.newMsg(stmt.String())
	return NewExecTrue("")
}

func (exec *Executor) printStmt(stmt *ast.PrintStmt) ExecRet {
	if stmt.IsFString {
		fmt.Println(stmt.Value)
	} else {
		fmt.Println(stmt.Value)
	}
	return NewExecTrue("")
}

func (exec *Executor) haveFnEqualCaseByCaseStmt(stmt *ast.HaveFnEqualCaseByCaseStmt) ExecRet {
	// 所有的case覆盖了整个domain

	// 每个case没有overlap

	// 每个case的返回值都符合fn的retSet

	panic("not implemented")
}
