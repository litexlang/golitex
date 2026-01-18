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
	litex_env "golitex/environment"
	glob "golitex/glob"
	"slices"
)

func (exec *Executor) Stmt(stmt ast.Stmt) *glob.StmtRet {
	var execRet *glob.StmtRet = glob.NewEmptyStmtError()

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		execRet = exec.factStmt(stmt)
	case *ast.KnowFactStmt:
		execRet = exec.knowStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddWarning("`know` saves the facts you write without verification. You may introduce incorrect facts by mistake. Use it with great caution!\n")
		}
	case *ast.KnowPropInferStmt:
		execRet = exec.knowPropInferStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddWarning("`know imply ` saves the facts you write without verification. You may introduce incorrect facts by mistake. Use it with great caution!\n")
		}
	case *ast.KnowInferStmt:
		execRet = exec.knowInferStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddWarning("`know infer` saves the facts you write without verification. You may introduce incorrect facts by mistake. Use it with great caution!\n")
		}
	case *ast.ClaimProveStmt:
		execRet = exec.execClaimStmtProve(stmt)
	// case *ast.ImpossibleStmt:
	// 	execRet = exec.execImpossibleStmt(stmt)
	case *ast.DefPropStmt:
		execRet = exec.defPropStmt(stmt, true)
	case *ast.DefLetStmt:
		execRet = exec.defLetStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddWarning("`let` may introduce non-existent objects. If you want to ensure the object exists, please use `have` instead!\n")
		}
	case *ast.LetFnStmt:
		execRet = exec.lefDefFnStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddWarning("`let fn` may introduce non-existent functions. If you want to ensure the function exists, please use `have fn` instead!\n")
		}
	case *ast.ClaimImplicationStmt:
		execRet = exec.claimImplyStmt(stmt)
	case *ast.ProveStmt:
		execRet = exec.proveStmt(stmt)
	case *ast.ClaimProveByContradictionStmt:
		execRet = exec.execClaimStmtProveByContradiction(stmt)
	case *ast.ProveByEnumStmt:
		execRet = exec.proveByEnumStmt(stmt)
	case *ast.HaveObjInNonEmptySetStmt:
		execRet = exec.haveObjInNonEmptySetStmt(stmt)
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
	case *ast.HaveFnStmt:
		execRet = exec.haveFnStmt(stmt)
	case *ast.HaveFnCaseByCaseStmt:
		execRet = exec.haveFnCaseByCaseStmt(stmt)
	case *ast.ClaimIffStmt:
		execRet = exec.claimIffStmt(stmt)
	case *ast.ProveIsTransitivePropStmt:
		execRet = exec.proveIsTransitivePropStmt(stmt)
	case *ast.ProveIsCommutativePropStmt:
		execRet = exec.proveIsCommutativePropStmt(stmt)
	case *ast.DefAlgoStmt:
		execRet = exec.defAlgoStmt(stmt)
	case *ast.EvalStmt:
		execRet = exec.evalStmt(stmt)
	case *ast.HaveFnEqualCaseByCaseStmt:
		execRet = exec.haveFnEqualCaseByCaseStmt(stmt)
	case *ast.ProveCaseByCaseStmt:
		execRet = exec.proveCaseByCaseStmt(stmt)
	case *ast.ImportDirStmt:
		execRet = glob.ErrRet("import statements are not allowed in local scope.")
	case *ast.RunFileStmt:
		execRet = glob.ErrRet("run statements are not allowed in local scope.")
	case *ast.EqualSetStmt:
		execRet = exec.equalSetStmt(stmt)
	case *ast.WitnessNonemptyStmt:
		execRet = exec.witnessNonemptyStmt(stmt)
	case *ast.ProveForStmt:
		execRet = exec.proveForStmt(stmt)
	case *ast.ProveInferStmt:
		execRet = exec.proveImplyStmt(stmt)
	case *ast.HaveShortStmt:
		execRet = exec.haveShortStmt(stmt)
	case *ast.HaveObjStStmt:
		execRet = exec.haveObjStStmt(stmt)
	case *ast.WitnessStmt:
		execRet = exec.proveExistStmt(stmt)
	case *ast.InferStmt:
		execRet = exec.inferStmt(stmt)
	case *ast.InferTemplateStmt:
		execRet = exec.inferTemplateStmt(stmt)
	case *ast.WitnessShortStmt:
		execRet = exec.witnessShortStmt(stmt)
	default:
		execRet = glob.ErrRet(fmt.Sprintf("unknown statement type: %T", stmt))
	}

	return execRet
}

func (exec *Executor) factStmt(stmt ast.FactStmt) *glob.StmtRet {
	curVerifier := NewVerifier(exec.Env)
	state := NewVerState(0, true, false)
	verRet := curVerifier.VerFactStmt(stmt, state)

	if verRet.IsErr() {
		return exec.AddStmtToStmtRet(verRet.ToStmtRet(), stmt)
	} else if verRet.IsTrue() {
		ret := exec.Env.NewFactWithCheckingNameDefined(stmt)
		if ret.IsErr() {
			return glob.ErrRet(ret.String()).AddError(stmt.String())
		}
		return exec.NewTrueStmtRet(stmt).AddNewFact((stmt.String())).AddVerifyProcess(verRet).AddNewFacts(ret.NewFact).AddInfers(ret.Infer)
	} else if verRet.IsUnknown() {
		return exec.AddStmtToStmtRet(verRet.ToStmtRet(), stmt).AddUnknown(stmt.String())
	} else {
		execRet := glob.ErrRet("unknown ver ret")
		return execRet.AddError(fmt.Sprintf("%s\n", stmt.String())).AddError(stmt.String())
	}
}

// TODO: 再know时就检查，仅仅依赖写在dom里的事实，是否真的能让涉及到的函数和prop能真的满足条件。如果不满足条件，那就warning
func (exec *Executor) knowStmt(stmt *ast.KnowFactStmt) *glob.StmtRet {
	newFactMsgs := []string{}
	implicationMsgs := []string{}

	for _, fact := range stmt.Facts {
		switch fact := fact.(type) {
		case ast.FactStmt:
			ret := exec.Env.NewFactWithCheckingNameDefined(fact)
			if ret.IsErr() {
				return glob.ErrRet(ret.String()).AddError(stmt.String())
			}
			// Collect derived facts from post-processing
			newFactMsgs = append(newFactMsgs, fact.String())
			implicationMsgs = append(implicationMsgs, ret.Infer...)
		default:
			return glob.ErrRet(fmt.Sprintf("unknown fact type: %T", fact)).AddError(stmt.String())
		}
	}

	// Build the result with all derived facts
	return exec.NewTrueStmtRet(stmt).AddNewFacts(newFactMsgs).AddInfers(implicationMsgs)
}

func (exec *Executor) defPropStmt(stmt *ast.DefPropStmt, generateIffUniFact bool) *glob.StmtRet {
	defineMsgs := []string{}
	newFactMsgs := []string{}

	ret := exec.Env.NewDefProp_InsideAtomsDeclared(stmt)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	defineMsgs = append(defineMsgs, glob.IsANewPropMsg(stmt.DefHeader.Name))

	paramMap := make(map[string]struct{})
	for _, param := range stmt.DefHeader.Params {
		paramMap[param] = struct{}{}
	}

	if (stmt.IffFactsOrNil) == nil {
		return exec.NewTrueStmtRet(stmt).AddDefineMsgs(defineMsgs)
	}

	if generateIffUniFact {
		// prop leads to iff
		propToIff, iffToProp, err := stmt.Make_PropToIff_IffToProp()
		if err != nil {
			return glob.ErrRet(err.Error())
		}

		ret = exec.Env.NewFactWithCheckingNameDefined(propToIff)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}

		ret = exec.Env.NewFactWithCheckingNameDefined(iffToProp)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
		newFactMsgs = append(newFactMsgs, propToIff.String())
		newFactMsgs = append(newFactMsgs, iffToProp.String())
	}

	return exec.NewTrueStmtRet(stmt).AddDefineMsgs(defineMsgs).AddNewFacts(newFactMsgs)
}

func (exec *Executor) defLetStmt(stmt *ast.DefLetStmt) *glob.StmtRet {
	ret := exec.Env.DefLetStmt(stmt)
	if ret.IsUnknown() || ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	return exec.NewTrueStmtRet(stmt).AddDefineMsgs(ret.Define).AddInfers(ret.Infer)
}

// func (exec *Executor) defExistPropStmt(stmt *ast.DefExistPropStmt) *glob.StmtRet {
// 	ret := exec.Env.NewDefExistProp_InsideAtomsDeclared(stmt)
// 	if ret.IsErr() {
// 		return exec.AddStmtToStmtRet(ret, stmt).AddErrors(ret.Error)
// 	}

// 	defineMsgs := []string{}
// 	defineMsgs = append(defineMsgs, glob.IsANewExistPropMsg(stmt.DefBody.DefHeader.Name))
// 	defineMsgs = append(defineMsgs, stmt.String())

// 	return exec.NewTrueStmtRet(stmt).AddDefineMsgs(defineMsgs)
// }

// TODO: 我认为打印一下 claim 里面的各个语句的输出还是有道理的
func (exec *Executor) execStmtsAtCurEnv(proof []ast.Stmt) *glob.StmtRet {
	innerExecRets := []*glob.StmtRet{}

	for _, curStmt := range proof {
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			return execState.AddError(fmt.Sprintf("failed :( line %d\n", curStmt.GetLine()))
		}
		innerExecRets = append(innerExecRets, execState)
	}
	return glob.NewStmtWithInnerStmtsRet(innerExecRets, glob.StmtRetTypeTrue)
}

func (exec *Executor) proveCaseByCaseStmt_checkOr(stmt *ast.ProveCaseByCaseStmt) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	for _, stmt := range stmt.ProveCases {
		ret := exec.Stmt(stmt)
		if ret.IsNotTrue() {
			return ret
		}
	}

	orFact := ast.NewOrStmt(stmt.CaseFacts, glob.BuiltinLine0)

	ret := exec.factStmt(orFact)
	return ret
}

func (exec *Executor) proveCaseByCaseStmt(stmt *ast.ProveCaseByCaseStmt) *glob.StmtRet {
	innerExecRetMsgs := []*glob.StmtRet{}
	verifyProcessMsgs := []*glob.VerRet{}
	newFactsMsgs := []string{}

	// Verify that cases cover all possibilities and don't overlap
	// For ProveCaseByCaseStmt, we don't have params/paramSets, so we use empty slices
	execState := exec.proveCaseByCaseStmt_checkOr(stmt)
	if execState.IsNotTrue() {
		return execState
	}
	verifyProcessMsgs = append(verifyProcessMsgs, execState.VerifyProcess...)

	// Prove each case
	for i := range stmt.CaseFacts {
		execState := exec.checkCaseInProveCaseByCase(stmt, i)
		if execState.IsNotTrue() {
			return execState
		}
		innerExecRetMsgs = append(innerExecRetMsgs, execState.InnerStmtRetSlice...)
	}

	// emit then fact
	for _, thenFact := range stmt.ThenFacts {
		ret := exec.Env.NewFactWithCheckingNameDefined(thenFact)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
		newFactsMsgs = append(newFactsMsgs, thenFact.String())
	}

	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(innerExecRetMsgs).AddVerifyProcesses(verifyProcessMsgs).AddNewFacts(newFactsMsgs)
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
func (exec *Executor) knowPropInferStmt(stmt *ast.KnowPropInferStmt) *glob.StmtRet {
	innerStmtRets := []*glob.StmtRet{}
	defineMsgs := []string{}
	newFactMsgs := []string{}

	execRet := exec.defPropStmt(stmt.DefProp, false)
	if execRet.IsNotTrue() {
		return execRet
	}
	innerStmtRets = append(innerStmtRets, execRet.InnerStmtRetSlice...)
	defineMsgs = append(defineMsgs, execRet.Define...)
	newFactMsgs = append(newFactMsgs, execRet.NewFact...)

	if len(stmt.DefProp.IffFactsOrNil) == 0 {
		_, iffToProp, err := stmt.DefProp.Make_PropToIff_IffToProp()
		if err != nil {
			return glob.ErrRet(err.Error())
		}
		ret := exec.Env.NewFactWithCheckingNameDefined(iffToProp)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
		newFactMsgs = append(newFactMsgs, iffToProp.String())
	}

	paramsAsObj := []ast.Obj{}
	for i := range stmt.DefProp.DefHeader.Params {
		paramsAsObj = append(paramsAsObj, ast.Atom(stmt.DefProp.DefHeader.Params[i]))
	}

	uniFact := ast.NewUniFact(stmt.DefProp.DefHeader.Params, stmt.DefProp.DefHeader.ParamSets, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.DefProp.DefHeader.Name), paramsAsObj, stmt.Line)}, stmt.DefProp.ImplicationFactsOrNil, stmt.Line)

	ret := exec.Env.NewFactWithCheckingNameDefined(uniFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	newFactMsgs = append(newFactMsgs, uniFact.String())

	uniFact2 := ast.NewUniFact(stmt.DefProp.DefHeader.Params, stmt.DefProp.DefHeader.ParamSets, stmt.DefProp.IffFactsOrNil, stmt.DefProp.ImplicationFactsOrNil, stmt.Line)
	ret = exec.Env.NewFactWithCheckingNameDefined(uniFact2)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	newFactMsgs = append(newFactMsgs, uniFact2.String())

	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(innerStmtRets).AddDefineMsgs(defineMsgs).AddNewFacts(newFactMsgs)
}

func (exec *Executor) knowInferStmt(stmt *ast.KnowInferStmt) *glob.StmtRet {
	newInferTemplate := ast.NewInferTemplateStmt(stmt.Params, stmt.ParamSets, stmt.DomFacts, stmt.ThenFacts, stmt.IfFacts, []ast.Stmt{}, stmt.Line)

	return exec.implyTemplateStmtStore(newInferTemplate)
}

func (exec *Executor) proveStmt(stmt *ast.ProveStmt) *glob.StmtRet {
	// new env
	exec.NewEnv()
	defer exec.deleteEnv()

	execState := exec.execStmtsAtCurEnv(stmt.Proof)
	if execState.IsNotTrue() {
		return execState
	}
	return exec.AddStmtToStmtRet(execState, stmt)
}

func (exec *Executor) lefDefFnStmt(stmt *ast.LetFnStmt) *glob.StmtRet {
	defineMsgs := []string{}
	newFactMsgs := []string{}

	ret := exec.Env.IsValidAndAvailableName(stmt.Name)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	shortRet := checkParamsInFnDefNotDefinedAndParamSetsDefined(exec, stmt.FnTemplate.Params, stmt.FnTemplate.ParamSets)
	if shortRet.IsNotTrue() {
		return glob.ErrRet(shortRet.String())
	}

	// 在 objMem 里记录一下
	defLetStmt := ast.NewDefLetStmt([]string{stmt.Name}, []ast.Obj{ast.Atom(glob.KeywordSet)}, []ast.FactStmt{}, stmt.Line)
	ret = exec.Env.DefLetStmt(defLetStmt)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	exec.Env.AllDefinedAtomObjNames[stmt.Name] = litex_env.NewDefinedStuff(struct{}{}, exec.Env.CurEnvDepth())
	defineMsgs = append(defineMsgs, glob.IsANewObjectMsg(stmt.Name))

	ret = exec.Env.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(ast.Atom(stmt.Name), nil, stmt.FnTemplate)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	derivedFact, err := stmt.FnTemplate.DeriveUniFact_WithGivenFn(ast.Atom(stmt.Name))
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	ret = exec.Env.NewFactWithCheckingNameDefined(derivedFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	newFactMsgs = append(newFactMsgs, derivedFact.String())

	return exec.NewTrueStmtRet(stmt).AddDefineMsgs(defineMsgs).AddNewFacts(newFactMsgs)
}

func (exec *Executor) proveByEnumStmtProve(stmt *ast.ProveByEnumStmt) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	execState, err := exec.proveByEnumMainLogic(stmt)
	if notOkExec(execState, err) {
		return glob.ErrRet(execState.String())
	}

	return execState
}

func (exec *Executor) proveByEnumStmt(stmt *ast.ProveByEnumStmt) *glob.StmtRet {
	innerStmtRets := []*glob.StmtRet{}
	verifyProcessMsgs := []*glob.VerRet{}
	newFactMsgs := []string{}

	execRet := exec.proveByEnumStmtProve(stmt)
	if execRet.IsNotTrue() {
		return execRet
	}
	innerStmtRets = append(innerStmtRets, execRet.InnerStmtRetSlice...)
	verifyProcessMsgs = append(verifyProcessMsgs, execRet.VerifyProcess...)

	// know uniFact
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.Fact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	newFactMsgs = append(newFactMsgs, stmt.Fact.String())

	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(innerStmtRets).AddVerifyProcesses(verifyProcessMsgs).AddNewFacts(newFactMsgs)
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
// func (exec *Executor) knowExistPropStmt(stmt *ast.KnowExistPropStmt) *glob.StmtRet {
// 	execState := exec.defExistPropStmt(stmt.ExistProp)
// 	if execState.IsNotTrue() {
// 		return execState
// 	}

// 	thenFacts := []ast.FactStmt{stmt.ExistProp.ToSpecFact()}
// 	knownUniFact := ast.NewUniFact(stmt.ExistProp.DefBody.DefHeader.Params, stmt.ExistProp.DefBody.DefHeader.ParamSets, stmt.ExistProp.DefBody.IffFactsOrNil, thenFacts, stmt.Line)

// 	ret := exec.Env.NewFactWithoutCheckingNameDefined(knownUniFact)
// 	if ret.IsErr() {
// 		return glob.ErrRet(ret.String())
// 	}

// 	return exec.NewTrueStmtRet(stmt).AddNewFact(fmt.Sprintf("%s\nis true by definition", knownUniFact))
// }

func (exec *Executor) DefFnTemplateStmt(stmt *ast.DefFnSetStmt) *glob.StmtRet {

	ret := exec.Env.NewFnTemplateInEnvMem(stmt)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) ClearStmt() *glob.StmtRet {
	// newEnvMgr := env.CopyEnvMgrAndOwnPkgMgr(env.BuiltinEnvMgrWithEmptyEnvPkgMgr, exec.Env.EnvPkgMgr)
	// exec.Env = newEnvMgr.NewEnv()
	exec.Env = litex_env.NewEmptyEnvMgr(exec.Env.EnvPkgMgr)
	return glob.NewStmtTrueWithStmt("clear all definitions and facts")
}

func (exec *Executor) DoNothingStmt() *glob.StmtRet {
	// do_nothing statement does nothing
	return glob.NewEmptyStmtTrue()
}

func (exec *Executor) inlineFactsStmt(stmt *ast.InlineFactsStmt) *glob.StmtRet {
	verifyProcessMsgs := []*glob.VerRet{}
	newFactMsgs := []string{}

	for _, fact := range stmt.Facts {
		execState := exec.factStmt(fact)
		if execState.IsNotTrue() {
			return execState
		}
		verifyProcessMsgs = append(verifyProcessMsgs, execState.VerifyProcess...)
		newFactMsgs = append(newFactMsgs, fact.String())
	}

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs).AddNewFacts(newFactMsgs)
}

func (exec *Executor) Verify(fact ast.FactStmt) *glob.StmtRet {
	ver := NewVerifier(exec.Env)
	state := Round0Msg()
	return ver.VerFactStmt(fact, state).ToStmtRet()
}

// func (exec *Executor) markdownStmt(stmt *ast.MarkdownStmt) *glob.GlobRet {
// 	_ = stmt
// 	return NewExecEmptyTrue()
// }

// func (exec *Executor) latexStmt(stmt *ast.LatexStmt) *glob.GlobRet {
// 	_ = stmt
// 	return NewExecEmptyTrue()
// }

func (exec *Executor) proveIsTransitivePropStmt(stmt *ast.ProveIsTransitivePropStmt) *glob.StmtRet {
	innerStmtRets := []*glob.StmtRet{}
	verifyProcessMsgs := []*glob.VerRet{}
	newFactMsgs := []string{}

	exec.NewEnv()
	defer exec.deleteEnv()

	if exec.Env.IsTransitiveProp(string(stmt.Prop)) {
		newFactMsgs = append(newFactMsgs, fmt.Sprintf("%s is transitive prop", stmt.Prop.String()))
		return exec.NewTrueStmtRet(stmt).AddNewFacts(newFactMsgs)
	}

	definedStuff, ok := exec.Env.GetPropDef(stmt.Prop)
	if !ok {
		return glob.ErrRet(fmt.Sprintf("undefined prop: %s", stmt.Prop))
	}

	def := definedStuff.Defined

	if len(def.DefHeader.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("prop %s has %d params, but 2 params are expected", stmt.Prop, len(def.DefHeader.Params)))
	}

	// def 的 paramSet 必须相等
	state := exec.factStmt(ast.NewEqualFact(def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1]))
	if state.IsErr() {
		return state
	}
	if state.IsUnknown() {
		return glob.ErrRet(fmt.Sprintf("prop in %s must have equal parameter sets, but parameter sets %s and %s of %s are not equal", glob.KeywordTransProp, def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1], def.DefHeader.Name))
	}
	verifyProcessMsgs = append(verifyProcessMsgs, state.VerifyProcess...)

	// 这里最好检查一下，是不是 Param set 依赖了 Param，如果依赖了，那其实是要报错了，不过暂时不管了
	execState := exec.defLetStmt(ast.NewDefLetStmt(stmt.Params, []ast.Obj{def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[0]}, def.DomFactsOrNil, stmt.Line))
	if execState.IsNotTrue() {
		return execState
	}
	innerStmtRets = append(innerStmtRets, execState.InnerStmtRetSlice...)

	ret := exec.Env.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(def.DefHeader.ParamSets[0], map[string]struct{}{})
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	ret = exec.Env.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(def.DefHeader.ParamSets[1], map[string]struct{}{})
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	if len(def.DomFactsOrNil) > 0 {
		return glob.ErrRet(fmt.Sprintf("dom facts are not allowed in %s", glob.KeywordTransProp))
	}

	ret = exec.Env.NewFactWithCheckingNameDefined(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.Prop), []ast.Obj{ast.Atom(stmt.Params[0]), ast.Atom(stmt.Params[1])}, stmt.Line))
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	ret = exec.Env.NewFactWithCheckingNameDefined(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.Prop), []ast.Obj{ast.Atom(stmt.Params[1]), ast.Atom(stmt.Params[2])}, stmt.Line))
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState
		}
		innerStmtRets = append(innerStmtRets, execState)
	}

	// check
	finalCheckStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.Prop), []ast.Obj{ast.Atom(stmt.Params[0]), ast.Atom(stmt.Params[2])}, stmt.Line)
	state = exec.factStmt(finalCheckStmt)
	if state.IsNotTrue() {
		return glob.ErrRet(fmt.Sprintf("failed to prove %s is transitive: %s failed", stmt.Prop, finalCheckStmt))
	}
	verifyProcessMsgs = append(verifyProcessMsgs, state.VerifyProcess...)

	exec.Env.CurEnv().TransitivePropMem[string(stmt.Prop)] = make(map[string][]ast.Obj)

	newFactMsgs = append(newFactMsgs, fmt.Sprintf("%s is transitive prop", stmt.Prop.String()))

	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(innerStmtRets).AddVerifyProcesses(verifyProcessMsgs).AddNewFacts(newFactMsgs)
}

func (exec *Executor) defAlgoStmt(stmt *ast.DefAlgoStmt) *glob.StmtRet {
	exec.Env.CurEnv().AlgoDefMem[stmt.FuncName] = struct{}{}
	exec.Env.AllDefinedAlgoNames[stmt.FuncName] = litex_env.NewDefinedStuff(stmt, exec.Env.CurEnvDepth())
	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) evalStmt(stmt *ast.EvalStmt) *glob.StmtRet {
	trueEvalRet := glob.NewEmptyStmtTrue()

	value, execRet := exec.evalObjInLocalEnv(stmt.ObjToEval)
	if execRet.IsNotTrue() {
		return execRet
	}
	ret := exec.Env.NewFactWithCheckingNameDefined(ast.NewEqualFact(stmt.ObjToEval, value))
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	trueEvalRet = trueEvalRet.AddInnerStmtRet(execRet)

	return exec.AddStmtToStmtRet(trueEvalRet, stmt)
}

func (exec *Executor) evalObjInLocalEnv(objToEval ast.Obj) (ast.Obj, *glob.StmtRet) {
	exec.NewEnv()
	defer exec.deleteEnv()

	value, execRet := exec.evalObjThenSimplify(objToEval)
	if execRet.IsNotTrue() {
		return nil, execRet
	}

	return value, glob.NewStmtTrueWithStmt(fmt.Sprintf("By evaluation of algo %s\nWe get %s = %s\n", objToEval.(*ast.FnObj).FnHead.String(), objToEval.String(), value.String()))
}

// func (exec *Executor) defProveAlgoStmt(stmt *ast.DefProveAlgoStmt) *glob.StmtRet {
// 	exec.Env.CurEnv().DefProveAlgoMem[stmt.ProveAlgoName] = struct{}{}
// 	exec.Env.AllDefinedProveAlgoNames[stmt.ProveAlgoName] = litex_env.NewDefinedStuff(stmt, exec.Env.CurEnvDepth())
// 	return exec.NewTrueStmtRet(stmt)
// }

func (exec *Executor) proveForStmt(stmt *ast.ProveForStmt) *glob.StmtRet {
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
			return glob.ErrRet(fmt.Sprintf("left value %s and right value %s must be integers", left.String(), right.String()))
		}

		if leftAsInt > rightAsInt {
			verMsg := glob.NewVerMsg(glob.StmtRetTypeTrue, "", glob.BuiltinLine0, []string{fmt.Sprintf("left value %d is larger than right value %d, so the %s statement is iterating on an empty range, so it is true", leftAsInt, rightAsInt, glob.KeywordFor)})

			uniFact := stmt.UniFact()
			ret := exec.Env.NewFactWithCheckingNameDefined(uniFact)
			if ret.IsErr() {
				return glob.ErrRet(ret.String())
			}

			return exec.AddStmtToStmtRet(glob.NewStmtTrueWithVerifyProcess(verMsg), stmt).AddNewFact(uniFact.String())
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

	innerStmtRets := []*glob.StmtRet{}
	newFactMsgs := []string{}

	// Iterate through all combinations
	for _, combination := range cartesianProductOfObjs {
		execRet := exec.proveForStmtWhenParamsAreIndices(stmt, combination)
		if execRet.IsNotTrue() {
			return execRet
		}
		innerStmtRets = append(innerStmtRets, execRet)
	}

	// Create and store the universal fact
	uniFact := stmt.UniFact()
	ret := exec.Env.NewFactWithCheckingNameDefined(uniFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	newFactMsgs = append(newFactMsgs, uniFact.String())

	return exec.NewTrueStmtRet(stmt).AddNewFacts(newFactMsgs)
}

func (exec *Executor) proveForStmtWhenParamsAreIndices(stmt *ast.ProveForStmt, indices []ast.Obj) *glob.StmtRet {
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
			return glob.ErrRet(err.Error())
		}
		execState := exec.factStmt(instDomFact)
		if execState.IsErr() {
			return execState
		}

		if execState.IsUnknown() {
			// 如果 不OK，那必须证明是 false，绝对不能是 unknown
			specFact, ok := domFact.(*ast.SpecFactStmt)
			if !ok {
				return glob.ErrRet(fmt.Sprintf("dom fact in for must be a SpecFactStmt to reverse: %s", domFact.String()))
			}
			revInstDomFact := specFact.ReverseIsTrue()
			for _, fact := range revInstDomFact {
				instFact, err := fact.InstantiateFact(uniMap)
				if err != nil {
					return glob.ErrRet(err.Error())
				}
				execState = exec.factStmt(instFact)
				if execState.IsErr() {
					return execState
				}
				if execState.IsUnknown() {
					return glob.ErrRet(fmt.Sprintf("dom facts in for must be proved to be true or false, can not be unknown: %s", instFact.String()))
				}
			}

			return glob.NewEmptyStmtTrue()
		}

		ret := exec.Env.NewFactWithCheckingNameDefined(domFact)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
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
			return glob.ErrRet(err.Error())
		}

		execState = exec.factStmt(instThenFact)
		if execState.IsErr() {
			return execState
		}
		if execState.IsUnknown() {
			return glob.ErrRet(fmt.Sprintf("then fact in for must be proved to be true or false, can not be unknown: %s", instThenFact.String()))
		}
	}

	return glob.NewEmptyStmtTrue()
}

func (exec *Executor) proveImplyStmt(stmt *ast.ProveInferStmt) *glob.StmtRet {
	ret := exec.proveImplyStmtProveProcess(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	ret = exec.Env.ProveImplyNewThenFactInPropDef(stmt)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	return exec.NewTrueStmtRet(stmt).AddWarning(fmt.Sprintf("%s is a powerful feature. The implication section will be automatically generated after every time %s is true later. Don't use it too much, since it is very memory consuming.", glob.KeywordProvePropInfer, stmt.SpecFact.PropName))
}

func (exec *Executor) proveImplyStmtProveProcess(stmt *ast.ProveInferStmt) *glob.StmtRet {

	exec.NewEnv()
	defer exec.deleteEnv()

	if stmt.SpecFact.FactType != ast.TruePure {
		return glob.ErrRet(fmt.Sprintf("expect true pure fact in prove_infer"))
	}

	specFactAsParams, err := ast.ParamsInSpecFactAreStrings(stmt.SpecFact)
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	// prop 的定义
	definedStuff, ok := exec.Env.GetPropDef(stmt.SpecFact.PropName)
	if !ok {
		return glob.ErrRet(fmt.Sprintf("undefined prop: %s", stmt.SpecFact.PropName))
	}
	def := definedStuff.Defined
	if len(def.DefHeader.Params) != len(specFactAsParams) {
		return glob.ErrRet(fmt.Sprintf("prop %s has %d params, but %d params are expected", stmt.SpecFact.PropName, len(def.DefHeader.Params), len(specFactAsParams)))
	}

	if len(def.DefHeader.ParamSets) != len(stmt.SpecFact.Params) {
		return glob.ErrRet(fmt.Sprintf("prop %s has %d param sets, but %d params are expected", stmt.SpecFact.PropName, len(def.DefHeader.ParamSets), len(stmt.SpecFact.Params)))
	}

	// define params in env
	for _, param := range specFactAsParams {
		ret := exec.defLetStmt(ast.NewDefLetStmt([]string{param}, []ast.Obj{ast.Atom(glob.KeywordSet)}, []ast.FactStmt{}, stmt.Line))
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
	}

	// 让这些param符合 def domain
	uniMap := map[string]ast.Obj{}

	// 让 param 都在 set 里
	for i, param := range def.DefHeader.Params {
		instParamSet, err := def.DefHeader.ParamSets[i].Instantiate(uniMap)
		if err != nil {
			return glob.ErrRet(err.Error())
		}

		newInFact := ast.NewInFactWithObj(stmt.SpecFact.Params[i], instParamSet)
		ret := exec.Env.NewFactWithCheckingNameDefined(newInFact)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}

		uniMap[param] = stmt.SpecFact.Params[i]
	}

	for _, domFact := range def.DomFactsOrNil {
		instDomFact, err := domFact.InstantiateFact(uniMap)
		if err != nil {
			return glob.ErrRet(err.Error())
		}
		ret := exec.Env.NewFactWithCheckingNameDefined(instDomFact)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
	}

	// itself is true
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.SpecFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	// exec proofs
	for _, curStmt := range stmt.Proofs {
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			return execState
		}
	}

	// exec then
	for _, thenFact := range stmt.ImplicationFact {
		instThenFact, err := thenFact.InstantiateFact(uniMap)
		if err != nil {
			return glob.ErrRet(err.Error())
		}
		execState := exec.factStmt(instThenFact)
		if execState.IsNotTrue() {
			return execState
		}
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) equalSetStmt(stmt *ast.EqualSetStmt) *glob.StmtRet {
	// 1. prove 过程（在局部环境中）
	ret := exec.equalSetStmtProveProcess(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	// 2. 存储过程（在原地存储）
	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{stmt.Left, stmt.Right}, stmt.Line)
	ret2 := exec.Env.NewFactWithCheckingNameDefined(equalFact)
	if ret2.IsErr() {
		return glob.ErrRet(ret2.String())
	}

	return exec.NewTrueStmtRet(stmt).AddNewFacts(ret2.Infer)
}

func (exec *Executor) equalSetStmtProveProcess(stmt *ast.EqualSetStmt) *glob.StmtRet {
	// 开局部环境
	exec.NewEnv()
	defer exec.deleteEnv()

	// 1. 先执行 proofs
	for _, proofStmt := range stmt.Proofs {
		execRet := exec.Stmt(proofStmt)
		if execRet.IsNotTrue() {
			return execRet
		}
	}

	// 2. 验证：验证 forall t a : t $in b 和 forall t b : t $in a
	a := stmt.Left
	b := stmt.Right

	ver := NewVerifier(exec.Env)
	state := Round0Msg()

	// Create forall t a : t $in b
	forall1 := ast.NewUniFact(
		[]string{"t"},
		[]ast.Obj{a},
		[]ast.FactStmt{},
		[]ast.FactStmt{
			ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{ast.Atom("t"), b}, stmt.Line),
		},
		stmt.Line,
	)

	// Create forall t b : t $in a
	forall2 := ast.NewUniFact(
		[]string{"t"},
		[]ast.Obj{b},
		[]ast.FactStmt{},
		[]ast.FactStmt{
			ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{ast.Atom("t"), a}, stmt.Line),
		},
		stmt.Line,
	)

	// Verify both forall statements
	verRet1 := ver.VerFactStmt(forall1, state)
	if verRet1.IsNotTrue() {
		return glob.ErrRet(verRet1.String())
	}

	verRet2 := ver.VerFactStmt(forall2, state)
	if verRet2.IsNotTrue() {
		return glob.ErrRet(verRet2.String())
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) witnessNonemptyStmt(stmt *ast.WitnessNonemptyStmt) *glob.StmtRet {
	// 1. prove 过程（在局部环境中）
	ret := exec.witnessNonemptyStmtProveProcess(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	// 2. 存储过程（在原地存储）
	isNonEmptyFact := ast.NewIsANonEmptySetFact(stmt.ObjSet, stmt.Line)
	ret2 := exec.Env.NewFactWithCheckingNameDefined(isNonEmptyFact)
	if ret2.IsErr() {
		return glob.ErrRet(ret2.String())
	}

	return exec.NewTrueStmtRet(stmt).AddNewFacts(ret2.Infer)
}

func (exec *Executor) witnessNonemptyStmtProveProcess(stmt *ast.WitnessNonemptyStmt) *glob.StmtRet {
	// 开局部环境
	exec.NewEnv()
	defer exec.deleteEnv()

	// 1. 先执行 proofs
	for _, proofStmt := range stmt.Proofs {
		execRet := exec.Stmt(proofStmt)
		if execRet.IsNotTrue() {
			return execRet
		}
	}

	// 2. 验证：验证 obj $in objSet
	ver := NewVerifier(exec.Env)
	state := Round0Msg()

	inFact := ast.NewInFactWithObj(stmt.Obj, stmt.ObjSet)
	verRet := ver.VerFactStmt(inFact, state)
	if verRet.IsErr() {
		return glob.ErrRet(verRet.String())
	}
	if verRet.IsUnknown() {
		return glob.ErrRet(fmt.Sprintf("cannot verify that %s $in %s", stmt.Obj, stmt.ObjSet))
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) checkCaseInProveCaseByCase(stmt *ast.ProveCaseByCaseStmt, caseI int) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	// 默认 stmt at caseI is true
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.CaseFacts[caseI])
	if ret.IsNotTrue() {
		return ret
	}

	proof := stmt.Proofs[caseI]

	if len(proof) == 0 {
		// check thens
		for _, thenFact := range stmt.ThenFacts {
			ret := exec.factStmt(thenFact)
			if ret.IsNotTrue() {
				return ret
			}
		}

		return glob.NewEmptyStmtTrue()
	}

	for i := 0; i < len(proof)-1; i++ {
		ret := exec.Stmt(proof[i])
		if ret.IsNotTrue() {
			return ret
		}
	}

	if asStmt, ok := proof[len(proof)-1].(*ast.ImpossibleStmt); ok {
		ret := exec.factStmt(asStmt.Fact)
		if ret.IsNotTrue() {
			return ret
		}

		for _, fact := range asStmt.Fact.ReverseIsTrue() {
			ret := exec.factStmt(fact)
			if ret.IsNotTrue() {
				return ret
			}
		}

		return glob.NewEmptyStmtTrue()

	} else {
		ret := exec.Stmt(proof[len(proof)-1])
		if ret.IsNotTrue() {
			return ret
		}

		// check thens
		for _, thenFact := range stmt.ThenFacts {
			ret := exec.factStmt(thenFact)
			if ret.IsNotTrue() {
				return ret
			}
		}

		return glob.NewEmptyStmtTrue()
	}
}

func (exec *Executor) witnessShortStmt(stmt *ast.WitnessShortStmt) *glob.StmtRet {
	ret := exec.witnessShortStmt_Verify(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	ret = exec.witnessShortStmt_NewFact(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) witnessShortStmt_Verify(witnessShortStmt *ast.WitnessShortStmt) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	for _, proof := range witnessShortStmt.Proofs {
		ret := exec.Stmt(proof)
		if ret.IsNotTrue() {
			return ret
		}
	}

	ret := exec.factStmt(witnessShortStmt.SpecFact)
	if ret.IsNotTrue() {
		return ret
	}

	return exec.NewTrueStmtRet(witnessShortStmt)
}

func (exec *Executor) witnessShortStmt_NewFact(witnessShortStmt *ast.WitnessShortStmt) *glob.StmtRet {
	lenOfParams := len(witnessShortStmt.SpecFact.Params)
	// 生成 lenOfParams 个 random obj

	randomParams := []string{}
	for i := 0; i < lenOfParams; i++ {
		for {
			randomObj := ast.Atom(exec.Env.GenerateUndeclaredRandomName())
			if !slices.Contains(randomParams, string(randomObj)) {
				randomParams = append(randomParams, string(randomObj))
				break
			}
		}
	}

	// 生成 exist a set, b set, c set ... st $p(a, b, c, ...)

	// 生成 randomParams 个 set
	randomParamSets := []ast.Obj{}
	for i := 0; i < len(randomParams); i++ {
		randomParamSets = append(randomParamSets, ast.Atom(glob.KeywordSet))
	}

	// 生成 randomParams 个 paramAsObj
	randomParamAsObj := []ast.Obj{}
	for i := 0; i < len(randomParams); i++ {
		randomParamAsObj = append(randomParamAsObj, ast.Atom(randomParams[i]))
	}

	existStruct := ast.NewExistStFactStruct(ast.TrueExist_St, witnessShortStmt.SpecFact.PropName, witnessShortStmt.SpecFact.IsTrue(), randomParams, randomParamSets, randomParamAsObj, witnessShortStmt.Line)
	existFact := existStruct.ToExistStFact()

	ret := exec.Env.NewFactWithCheckingNameDefined(existFact)
	if ret.IsNotTrue() {
		return glob.ErrRet(ret.String())
	}

	return exec.NewTrueStmtRet(witnessShortStmt).AddNewFacts(ret.Infer)
}

func (exec *Executor) haveShortStmt(stmt *ast.HaveShortStmt) *glob.StmtRet {
	ret := exec.haveShortStmt_Verify(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	ret = exec.haveShortStmt_Define(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) haveShortStmt_Verify(haveShortStmt *ast.HaveShortStmt) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	params := []string{}
	for _, param := range haveShortStmt.SpecFact.Params {
		if _, ok := param.(ast.Atom); !ok {
			return glob.ErrRet(fmt.Sprintf("param %s must be a string", param))
		}
		params = append(params, string(param.(ast.Atom)))
	}

	paramSets := []ast.Obj{}
	for i := 0; i < len(haveShortStmt.SpecFact.Params); i++ {
		paramSets = append(paramSets, ast.Atom(glob.KeywordSet))
	}

	paramAsObj := []ast.Obj{}
	for _, param := range haveShortStmt.SpecFact.Params {
		paramAsObj = append(paramAsObj, param)
	}

	ret := exec.factStmt(ast.NewExistStFactStruct(ast.TrueExist_St, haveShortStmt.SpecFact.PropName, haveShortStmt.SpecFact.IsTrue(), params, paramSets, paramAsObj, haveShortStmt.Line).ToExistStFact())
	if ret.IsNotTrue() {
		return ret
	}

	return exec.NewTrueStmtRet(haveShortStmt)
}

func (exec *Executor) haveShortStmt_Define(haveShortStmt *ast.HaveShortStmt) *glob.StmtRet {
	// spec fact 里的 params 必须都是 string
	params := []string{}
	for _, param := range haveShortStmt.SpecFact.Params {
		if _, ok := param.(ast.Atom); !ok {
			return glob.ErrRet(fmt.Sprintf("param %s must be a string", param))
		}
		params = append(params, string(param.(ast.Atom)))
	}

	// 获得 prop 的定义
	propDef, ok := exec.Env.GetPropDef(haveShortStmt.SpecFact.PropName)
	if !ok {
		return glob.ErrRet(fmt.Sprintf("prop %s not found", haveShortStmt.SpecFact.PropName))
	}

	uniMap := map[string]ast.Obj{}
	paramSets := []ast.Obj{}
	for i, param := range propDef.Defined.DefHeader.Params {
		curSet, err := propDef.Defined.DefHeader.ParamSets[i].Instantiate(uniMap)
		if err != nil {
			return glob.ErrRet(err.Error())
		}
		paramSets = append(paramSets, curSet)
		uniMap[string(param)] = haveShortStmt.SpecFact.Params[i]
	}

	return exec.Env.DefLetStmt(ast.NewDefLetStmt(params, paramSets, []ast.FactStmt{haveShortStmt.SpecFact}, haveShortStmt.Line))
}
