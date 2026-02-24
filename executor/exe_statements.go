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
)

func (exec *Executor) Stmt(stmt ast.Stmt) ast.StmtRet {
	var execRet ast.StmtRet = newErrStmtRetWithCaller("")

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		execRet = exec.factStmt(stmt)
	case *ast.KnowFactStmt:
		execRet = exec.knowStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddExtraInfo("Warning: The `know` statement stores facts without verification. Incorrect facts may be introduced unintentionally. Use with caution.\n")
		}
	case *ast.KnowPropInferStmt:
		execRet = exec.knowPropInferStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddExtraInfo("Warning: The `know imply` statement stores facts without verification. Incorrect facts may be introduced unintentionally. Use with caution.\n")
		}
	case *ast.KnowInferStmt:
		execRet = exec.knowInferStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddExtraInfo("Warning: The `know infer` statement stores facts without verification. Incorrect facts may be introduced unintentionally. Use with caution.\n")
		}
	case *ast.ClaimProveStmt:
		execRet = exec.execClaimStmtProve(stmt)
	case *ast.DefPropStmt:
		execRet = exec.defPropStmt(stmt)
	case *ast.DefLetStmt:
		execRet = exec.defLetStmt(stmt)
		if execRet.IsTrue() {
			execRet = execRet.AddExtraInfo("Note: The `let` statement may introduce objects without existence verification. To ensure object existence, use `have` instead.\n")
		}
	// case *ast.LetFnStmt:
	// 	execRet = exec.lefDefFnStmt(stmt)
	// 	if execRet.IsTrue() {
	// 		execRet = execRet.AddExtraInfo("Note: The `let fn` statement may introduce functions without existence verification. To ensure function existence, use `have fn` instead.\n")
	// 	}
	case *ast.ProveStmt:
		execRet = exec.proveStmt(stmt)
	case *ast.ClaimProveByContradictionStmt:
		execRet = exec.execClaimStmtProveByContradiction(stmt)
	case *ast.ProveByEnumStmt:
		execRet = exec.proveByEnumStmt(stmt)
	case *ast.HaveObjInNonEmptySetStmt:
		execRet = exec.haveObjInNonEmptySetStmt(stmt)
	// case *ast.DefFnSetStmt:
	// 	execRet = exec.DefFnTemplateStmt(stmt)
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
	// case *ast.HaveFnEqualStmt:
	// 	execRet = exec.haveFnEqualStmt(stmt)
	case *ast.HaveFnStmt:
		execRet = exec.haveFnStmt(stmt)
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
	// case *ast.HaveFnEqualCaseByCaseStmt:
	// execRet = exec.haveFnEqualCaseByCaseStmt(stmt)
	case *ast.ProveCaseByCaseStmt:
		// execRet = exec.proveCaseByCaseStmt(stmt)
		execRet = exec.execCases(stmt)
	case *ast.ImportDirStmt:
		execRet = ast.StmtErrRet(stmt, "import statements are not allowed in local scope.")
	case *ast.RunFileStmt:
		execRet = ast.StmtErrRet(stmt, "run statements are not allowed in local scope.")
	case *ast.EqualSetStmt:
		execRet = exec.equalSetStmt(stmt)
	case *ast.WitnessNonemptyStmt:
		execRet = exec.witnessNonemptyStmt(stmt)
	case *ast.ProveForStmt:
		execRet = exec.proveForStmt(stmt)
	case *ast.ProveInferStmt:
		execRet = exec.proveImplyStmt(stmt)
	case *ast.HaveObjStStmt:
		execRet = exec.haveObjStStmt(stmt)
	case *ast.WitnessStmt:
		execRet = exec.proveExistStmt(stmt)
	case *ast.InferStmt:
		execRet = exec.inferStmt(stmt)
	case *ast.InferTemplateStmt:
		execRet = exec.inferTemplateStmt(stmt)
	case *ast.SetIsFnStmt:
		execRet = exec.setIsFnStmt(stmt)
	case *ast.FnIsSubsetOfCartStmt:
		execRet = exec.fnIsSubsetOfCartStmt(stmt)
	case *ast.HaveFnEqual:
		execRet = exec.haveFnEqual(stmt)
	case *ast.HaveFnEqualCaseByCase:
		execRet = exec.haveFnEqualCaseByCase(stmt)
	case *ast.LetFn:
		execRet = exec.letFn(stmt)
	default:
		execRet = ast.StmtErrRet(stmt, fmt.Sprintf("unknown statement type: %T", stmt))
	}

	return execRet
}

func (exec *Executor) factStmt(stmt ast.FactStmt) ast.StmtRet {
	curVerifier := NewVerifier(exec.Env)
	state := NewVerState(0, true, false)
	verRet := curVerifier.VerFactStmt(stmt, state)

	if verRet.IsErr() {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(verRet.String())
		// return exec.AddStmtToStmtRet(verRet.ToStmtRet(), stmt)
	} else if verRet.IsTrue() {
		ret := exec.Env.NewFactWithCheckingNameDefined(stmt)
		if ret.IsErr() {
			return ast.StmtErrRet(stmt, ret.String()).AddExtraInfo(stmt.String())
		}
		inferRets := []ast.InferRet{ret}
		return exec.NewTrueStmtRet(stmt).AddVerifyProcesses([]ast.VerRet{verRet}).AddInfers(inferRets)
	} else if verRet.IsUnknown() {
		return ast.NewUnknownStmtEmptyRet(stmt).AddExtraInfo(verRet.String())
		// return exec.AddStmtToStmtRet(verRet.ToStmtRet(), stmt).AddExtraInfo(stmt.String())
	} else {
		execRet := ast.StmtErrRet(stmt, "unknown ver ret")
		return execRet.AddExtraInfo(fmt.Sprintf("%s\n", stmt.String()))
	}
}

// TODO: 再know时就检查，仅仅依赖写在dom里的事实，是否真的能让涉及到的函数和prop能真的满足条件。如果不满足条件，那就warning
func (exec *Executor) knowStmt(stmt *ast.KnowFactStmt) ast.StmtRet {
	newFactMsgs := []string{}
	implicationRets := []ast.InferRet{}

	for _, fact := range stmt.Facts {
		switch fact := fact.(type) {
		case ast.FactStmt:
			ret := exec.Env.NewFactWithCheckingNameDefined(fact)
			if ret.IsErr() {
				return ast.StmtErrRet(stmt, ret.String()).AddExtraInfo(stmt.String())
			}
			// Collect derived facts from post-processing
			newFactMsgs = append(newFactMsgs, fact.String())
			if trueRet, ok := ret.(*ast.TrueInferRet); ok {
				for _, inferFact := range trueRet.Infer {
					newFactMsgs = append(newFactMsgs, inferFact.String())
				}
			}
			implicationRets = append(implicationRets, ret)
		default:
			return ast.StmtErrRet(stmt, fmt.Sprintf("unknown fact type: %T", fact)).AddExtraInfo(stmt.String())
		}
	}

	// Build the result with all derived facts
	return exec.NewTrueStmtRet(stmt).AddInfers(implicationRets)
}

func (exec *Executor) defPropStmt(stmt *ast.DefPropStmt) ast.StmtRet {
	defineMsgs := []string{}

	// check fn req of facts inside
	ret1 := exec.checkFnReqInsideDefProp(stmt, Round0NoMsg())
	if ret1.IsNotTrue() {
		return ast.StmtErrRet(stmt, ret1.String())
	}

	ret := exec.Env.NewDefProp_InsideAtomsDeclared(stmt)
	if ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
	}
	defineMsgs = append(defineMsgs, glob.IsANewPropMsg(stmt.DefHeader.Name))

	paramMap := make(map[string]struct{})
	for _, param := range stmt.DefHeader.Params {
		paramMap[param] = struct{}{}
	}

	return exec.NewTrueStmtRet(stmt).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) defLetStmt(stmt *ast.DefLetStmt) ast.StmtRet {
	ret := exec.Env.DefLetStmt(stmt)
	if ret.IsUnknown() || ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
	}

	defineMsgs := []string{}
	inferRets := []ast.InferRet{}
	if trueRet, ok := ret.(*ast.TrueStmtRet); ok {
		defineMsgs = trueRet.Define
		inferRets = trueRet.Infer
	}

	return exec.NewTrueStmtRet(stmt).AddDefineMsgs(defineMsgs).AddInfers(inferRets)
}

// func (exec *Executor) defExistPropStmt(stmt *ast.DefExistPropStmt) ast.StmtRet{
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
func (exec *Executor) execStmtsAtCurEnv(proof []ast.Stmt) ast.StmtRet {
	innerExecRets := []ast.StmtRet{}

	for _, curStmt := range proof {
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			return execState.AddExtraInfo(fmt.Sprintf("Execution failed at line %d:\n%s\n", curStmt.GetLine(), curStmt.String()))
		}
		innerExecRets = append(innerExecRets, execState)
	}
	return newTrueStmtRetWithCaller().AddInnerStmtRets(innerExecRets)
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
func (exec *Executor) knowPropInferStmt(stmt *ast.KnowPropInferStmt) ast.StmtRet {
	innerStmtRets := []ast.StmtRet{}
	defineMsgs := []string{}

	execRet := exec.defPropStmt(stmt.DefProp)
	if execRet.IsNotTrue() {
		return execRet
	}
	if trueRet, ok := execRet.(*ast.TrueStmtRet); ok {
		innerStmtRets = append(innerStmtRets, trueRet.InnerStmtRetSlice...)
		defineMsgs = append(defineMsgs, trueRet.Define...)
	}

	paramsAsObj := []ast.Obj{}
	for i := range stmt.DefProp.DefHeader.Params {
		paramsAsObj = append(paramsAsObj, ast.Atom(stmt.DefProp.DefHeader.Params[i]))
	}

	uniFact := ast.NewUniFact(stmt.DefProp.DefHeader.Params, stmt.DefProp.DefHeader.ParamSets, []ast.Spec_OrFact{ast.NewPureSpecificFactStmt(true, ast.Atom(stmt.DefProp.DefHeader.Name), paramsAsObj, stmt.Line)}, stmt.DefProp.ImplicationFactsOrNil, stmt.Line)

	ret := exec.Env.NewFactWithCheckingNameDefined(uniFact)
	if ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
	}

	iffFacts := []ast.Spec_OrFact{}
	for _, iffFact := range stmt.DefProp.IffFactsOrNil {
		iffFact, err := iffFact.InstantiateFact(map[string]ast.Obj{})
		if err != nil {
			return ast.StmtErrRet(stmt, err.Error())
		}
		iffFacts = append(iffFacts, iffFact.(ast.Spec_OrFact))
	}

	uniFact2 := ast.NewUniFact(stmt.DefProp.DefHeader.Params, stmt.DefProp.DefHeader.ParamSets, iffFacts, stmt.DefProp.ImplicationFactsOrNil, stmt.Line)
	ret = exec.Env.NewFactWithCheckingNameDefined(uniFact2)
	if ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
	}

	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(innerStmtRets).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) knowInferStmt(stmt *ast.KnowInferStmt) ast.StmtRet {
	newInferTemplate := ast.NewInferTemplateStmt(stmt.Params, stmt.ParamSets, stmt.DomFacts, stmt.ThenFacts, stmt.IfFacts, []ast.Stmt{}, stmt.Line)

	return exec.implyTemplateStmtStore(newInferTemplate)
}

func (exec *Executor) proveStmt(stmt *ast.ProveStmt) ast.StmtRet {
	// new env
	exec.NewEnv()
	defer exec.deleteEnv()

	execState := exec.execStmtsAtCurEnv(stmt.Proof)
	if execState.IsNotTrue() {
		return execState
	}
	return ast.NewTrueStmtEmptyRet(stmt).AddInnerStmtRets([]ast.StmtRet{execState})
	// return exec.AddStmtToStmtRet(execState, stmt)
}

// func (exec *Executor) lefDefFnStmt(stmt *ast.LetFnStmt) ast.StmtRet {
// 	defineMsgs := []string{}

// 	ret := exec.Env.IsValidAndAvailableName(stmt.Name)
// 	if !ret {
// 		return ast.StmtErrRet(stmt, fmt.Sprintf("invalid or unavailable name: %s", stmt.Name))
// 	}

// 	shortRet := checkParamsInFnDefNotDefinedAndParamSetsDefined(exec, stmt.FnTemplate.Params, stmt.FnTemplate.ParamSets)
// 	if shortRet.IsNotTrue() {
// 		return ast.StmtErrRet(stmt, shortRet.String())
// 	}

// 	// 在 objMem 里记录一下
// 	defLetStmt := ast.NewDefLetStmt([]string{stmt.Name}, []ast.Obj{ast.Atom(glob.KeywordSet)}, []ast.FactStmt{}, stmt.Line)
// 	retStmt := exec.Env.DefLetStmt(defLetStmt)
// 	if retStmt.IsErr() {
// 		return ast.StmtErrRet(stmt, retStmt.String())
// 	}
// 	exec.Env.AllDefinedAtomObjNames[stmt.Name] = litex_env.NewDefinedStuff(struct{}{}, exec.Env.CurEnvDepth())
// 	defineMsgs = append(defineMsgs, glob.IsANewObjectMsg(stmt.Name))

// 	retInfer := exec.Env.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(ast.Atom(stmt.Name), nil, stmt.FnTemplate)
// 	if retInfer.IsErr() {
// 		return ast.StmtErrRet(stmt, retInfer.String())
// 	}

// 	derivedFact, err := stmt.FnTemplate.DeriveUniFact_WithGivenFn(ast.Atom(stmt.Name))
// 	if err != nil {
// 		return ast.StmtErrRet(stmt, err.Error())
// 	}

// 	retInfer2 := exec.Env.NewFactWithCheckingNameDefined(derivedFact)
// 	if retInfer2.IsErr() {
// 		return ast.StmtErrRet(stmt, retInfer2.String())
// 	}

// 	return exec.NewTrueStmtRet(stmt).AddDefineMsgs(defineMsgs)
// }

func (exec *Executor) proveByEnumStmtProve(stmt *ast.ProveByEnumStmt) ast.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	execState, err := exec.proveByEnumMainLogic(stmt)
	if notOkExec(execState, err) {
		return ast.StmtErrRet(stmt, execState.String())
	}

	return execState
}

func (exec *Executor) proveByEnumStmt(stmt *ast.ProveByEnumStmt) ast.StmtRet {
	innerStmtRets := []ast.StmtRet{}
	verifyProcessMsgs := []ast.VerRet{}

	execRet := exec.proveByEnumStmtProve(stmt)
	if execRet.IsNotTrue() {
		return execRet
	}
	if trueRet, ok := execRet.(*ast.TrueStmtRet); ok {
		innerStmtRets = append(innerStmtRets, trueRet.InnerStmtRetSlice...)
		verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
	}

	// know uniFact
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.Fact)
	if ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
	}

	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(innerStmtRets).AddVerifyProcesses(verifyProcessMsgs)
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
// func (exec *Executor) knowExistPropStmt(stmt *ast.KnowExistPropStmt) ast.StmtRet{
// 	execState := exec.defExistPropStmt(stmt.ExistProp)
// 	if execState.IsNotTrue() {
// 		return execState
// 	}

// 	thenFacts := []ast.FactStmt{stmt.ExistProp.ToSpecFact()}
// 	knownUniFact := ast.NewUniFact(stmt.ExistProp.DefBody.DefHeader.Params, stmt.ExistProp.DefBody.DefHeader.ParamSets, stmt.ExistProp.DefBody.IffFactsOrNil, thenFacts, stmt.Line)

// 	ret := exec.Env.NewFactWithoutCheckingNameDefined(knownUniFact)
// 	if ret.IsErr() {
// 		return ast.StmtErrRet(ret.String())
// 	}

// 	return exec.NewTrueStmtRet(stmt).AddNewFact(fmt.Sprintf("%s\nis true by definition", knownUniFact))
// }

// func (exec *Executor) DefFnTemplateStmt(stmt *ast.DefFnSetStmt) ast.StmtRet {

// 	// ret := exec.Env.NewFnTemplateInEnvMem(stmt)
// 	// if ret.IsErr() {
// 	// 	return ast.StmtErrRet(stmt, ret.String())
// 	// }

// 	// return exec.NewTrueStmtRet(stmt)
// 	panic("")
// }

func (exec *Executor) ClearStmt() ast.StmtRet {
	// newEnvMgr := env.CopyEnvMgrAndOwnPkgMgr(env.BuiltinEnvMgrWithEmptyEnvPkgMgr, exec.Env.EnvPkgMgr)
	// exec.Env = newEnvMgr.NewEnv()
	exec.Env = litex_env.NewEmptyEnvMgr(exec.Env.EnvPkgMgr)
	return newTrueStmtRetWithCaller().AddExtraInfo("All definitions and facts have been cleared.\n")
}

func (exec *Executor) DoNothingStmt() ast.StmtRet {
	// do_nothing statement does nothing
	return newTrueStmtRetWithCaller()
}

func (exec *Executor) inlineFactsStmt(stmt *ast.InlineFactsStmt) ast.StmtRet {
	verifyProcessMsgs := []ast.VerRet{}

	for _, fact := range stmt.Facts {
		execState := exec.factStmt(fact)
		if execState.IsNotTrue() {
			return execState
		}
		if trueRet, ok := execState.(*ast.TrueStmtRet); ok {
			verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
		}
	}

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs)
}

func (exec *Executor) Verify(fact ast.FactStmt) ast.StmtRet {
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

func (exec *Executor) proveIsTransitivePropStmt(stmt *ast.ProveIsTransitivePropStmt) ast.StmtRet {
	innerStmtRets := []ast.StmtRet{}
	verifyProcessMsgs := []ast.VerRet{}

	exec.NewEnv()
	defer exec.deleteEnv()

	if exec.Env.IsTransitiveProp(string(stmt.Prop)) {
		return exec.NewTrueStmtRet(stmt).AddExtraInfo(fmt.Sprintf("Property %s is already known to be transitive.\n", stmt.Prop.String()))
	}

	definedStuff, ok := exec.Env.GetPropDef(stmt.Prop)
	if !ok {
		return ast.StmtErrRet(stmt, fmt.Sprintf("undefined prop: %s", stmt.Prop))
	}

	def := definedStuff.Defined

	if len(def.DefHeader.Params) != 2 {
		return ast.StmtErrRet(stmt, fmt.Sprintf("prop %s has %d params, but 2 params are expected", stmt.Prop, len(def.DefHeader.Params)))
	}

	// def 的 paramSet 必须相等
	state := exec.factStmt(ast.NewEqualFact(def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1]))
	if state.IsErr() {
		return state
	}
	if state.IsUnknown() {
		return ast.StmtErrRet(stmt, fmt.Sprintf("prop in %s must have equal parameter sets, but parameter sets %s and %s of %s are not equal", glob.KeywordTransProp, def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1], def.DefHeader.Name))
	}
	if trueRet, ok := state.(*ast.TrueStmtRet); ok {
		verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
	}

	// 这里最好检查一下，是不是 Param set 依赖了 Param，如果依赖了，那其实是要报错了，不过暂时不管了
	execState := exec.defLetStmt(ast.NewDefLetStmt(stmt.Params, []ast.Obj{def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[0]}, []ast.FactStmt{}, stmt.Line))
	if execState.IsNotTrue() {
		return execState
	}
	if trueRet, ok := execState.(*ast.TrueStmtRet); ok {
		innerStmtRets = append(innerStmtRets, trueRet.InnerStmtRetSlice...)
	}

	ret := exec.Env.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(def.DefHeader.ParamSets[0], map[string]struct{}{})
	if ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
	}
	ret = exec.Env.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(def.DefHeader.ParamSets[1], map[string]struct{}{})
	if ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
	}

	retInfer := exec.Env.NewFactWithCheckingNameDefined(ast.NewPureSpecificFactStmt(true, ast.Atom(stmt.Prop), []ast.Obj{ast.Atom(stmt.Params[0]), ast.Atom(stmt.Params[1])}, stmt.Line))
	if retInfer.IsErr() {
		return ast.StmtErrRet(stmt, retInfer.String())
	}

	retInfer = exec.Env.NewFactWithCheckingNameDefined(ast.NewPureSpecificFactStmt(true, ast.Atom(stmt.Prop), []ast.Obj{ast.Atom(stmt.Params[1]), ast.Atom(stmt.Params[2])}, stmt.Line))
	if retInfer.IsErr() {
		return ast.StmtErrRet(stmt, retInfer.String())
	}

	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState
		}
		innerStmtRets = append(innerStmtRets, execState)
	}

	// check
	finalCheckStmt := ast.NewPureSpecificFactStmt(true, ast.Atom(stmt.Prop), []ast.Obj{ast.Atom(stmt.Params[0]), ast.Atom(stmt.Params[2])}, stmt.Line)
	state = exec.factStmt(finalCheckStmt)
	if state.IsNotTrue() {
		return ast.StmtErrRet(stmt, fmt.Sprintf("failed to prove %s is transitive: %s failed", stmt.Prop, finalCheckStmt))
	}
	if trueRet, ok := state.(*ast.TrueStmtRet); ok {
		verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
	}

	exec.Env.CurEnv().TransitivePropMem[string(stmt.Prop)] = make(map[string][]ast.Obj)

	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(innerStmtRets).AddVerifyProcesses(verifyProcessMsgs).AddExtraInfo(fmt.Sprintf("Property %s has been proven to be transitive.\n", stmt.Prop.String()))
}

func (exec *Executor) evalStmt(stmt *ast.EvalStmt) ast.StmtRet {
	value, execRet := exec.evalObjInLocalEnv(stmt.ObjToEval)
	if execRet.IsNotTrue() {
		return execRet
	}
	ret := exec.Env.NewFactWithCheckingNameDefined(ast.NewEqualFact(stmt.ObjToEval, value))
	if ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
	}
	trueEvalRet := newTrueStmtRetWithCaller().AddInnerStmtRets([]ast.StmtRet{execRet})

	// return exec.AddStmtToStmtRet(trueEvalRet, stmt)
	return trueEvalRet
}

func (exec *Executor) evalObjInLocalEnv(objToEval ast.Obj) (ast.Obj, ast.StmtRet) {
	exec.NewEnv()
	defer exec.deleteEnv()

	value, execRet := exec.evalObjThenSimplify(objToEval)
	if execRet.IsNotTrue() {
		return nil, execRet
	}

	return value, newTrueStmtRetWithCaller().AddExtraInfo(fmt.Sprintf("Evaluation result: %s = %s (via algorithm %s)\n", objToEval.String(), value.String(), objToEval.(*ast.FnObj).FnHead.String()))
}

// func (exec *Executor) defProveAlgoStmt(stmt *ast.DefProveAlgoStmt) ast.StmtRet{
// 	exec.Env.CurEnv().DefProveAlgoMem[stmt.ProveAlgoName] = struct{}{}
// 	exec.Env.AllDefinedProveAlgoNames[stmt.ProveAlgoName] = litex_env.NewDefinedStuff(stmt, exec.Env.CurEnvDepth())
// 	return exec.NewTrueStmtRet(stmt)
// }

func (exec *Executor) proveForStmt(stmt *ast.ProveForStmt) ast.StmtRet {
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
			return ast.StmtErrRet(stmt, fmt.Sprintf("left value %s and right value %s must be integers", left.String(), right.String()))
		}

		if leftAsInt > rightAsInt {
			verMsg := ast.NewTrueVerRet(nil, nil, fmt.Sprintf("left value %d is larger than right value %d, so the %s statement is iterating on an empty range, so it is true", leftAsInt, rightAsInt, glob.KeywordFor))

			uniFact := stmt.UniFact()
			ret := exec.Env.NewFactWithCheckingNameDefined(uniFact)
			if ret.IsErr() {
				return ast.StmtErrRet(stmt, ret.String())
			}

			return ast.NewTrueStmtEmptyRet(stmt).AddVerifyProcesses([]ast.VerRet{verMsg})
			// return exec.AddStmtToStmtRet(ast.NewTrueStmtEmptyRet(stmt).AddVerifyProcesses([]ast.VerRet{verMsg}), stmt).AddNewFacts([]string{uniFact.String()})
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

	innerStmtRets := []ast.StmtRet{}
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
		return ast.StmtErrRet(stmt, ret.String())
	}
	newFactMsgs = append(newFactMsgs, uniFact.String())

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) proveForStmtWhenParamsAreIndices(stmt *ast.ProveForStmt, indices []ast.Obj) ast.StmtRet {
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
			return ast.StmtErrRet(stmt, err.Error())
		}
		execState := exec.factStmt(instDomFact)
		if execState.IsErr() {
			return execState
		}

		if execState.IsUnknown() {
			// 如果 不OK，那必须证明是 false，绝对不能是 unknown
			specFact, ok := domFact.(ast.SpecificFactStmt)
			if !ok {
				return ast.StmtErrRet(stmt, fmt.Sprintf("dom fact in for must be a SpecFactStmt to reverse: %s", domFact.String()))
			}
			revInstDomFact := specFact.ReverseIsTrue()
			for _, fact := range revInstDomFact {
				instFact, err := fact.InstantiateFact(uniMap)
				if err != nil {
					return ast.StmtErrRet(stmt, err.Error())
				}
				execState = exec.factStmt(instFact)
				if execState.IsErr() {
					return execState
				}
				if execState.IsUnknown() {
					return ast.StmtErrRet(stmt, fmt.Sprintf("dom facts in for must be proved to be true or false, can not be unknown: %s", instFact.String()))
				}
			}

			return newTrueStmtRetWithCaller()
		}

		ret := exec.Env.NewFactWithCheckingNameDefined(domFact)
		if ret.IsErr() {
			return ast.StmtErrRet(stmt, ret.String())
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
			return ast.StmtErrRet(stmt, err.Error())
		}

		execState = exec.factStmt(instThenFact)
		if execState.IsErr() {
			return execState
		}
		if execState.IsUnknown() {
			return ast.StmtErrRet(stmt, fmt.Sprintf("then fact in for must be proved to be true or false, can not be unknown: %s", instThenFact.String()))
		}
	}

	return newTrueStmtRetWithCaller()
}

func (exec *Executor) proveImplyStmt(stmt *ast.ProveInferStmt) ast.StmtRet {
	ret := exec.proveImplyStmtProveProcess(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	retInfer := exec.Env.ProveImplyNewThenFactInPropDef(stmt)
	if retInfer.IsErr() {
		return ast.StmtErrRet(stmt, retInfer.String())
	}

	return exec.NewTrueStmtRet(stmt).AddExtraInfo(fmt.Sprintf("Note: %s is a powerful feature. The implication section will be automatically generated whenever %s becomes true. Use sparingly as it is memory-intensive.\n", glob.KeywordProvePropInfer, stmt.SpecFact.PropName))
}

func (exec *Executor) proveImplyStmtProveProcess(stmt *ast.ProveInferStmt) ast.StmtRet {

	exec.NewEnv()
	defer exec.deleteEnv()

	if stmt.SpecFact.GetFactType() != ast.TruePure {
		return ast.StmtErrRet(stmt, fmt.Sprintf("expect true pure fact in prove_infer"))
	}

	specFactAsParams, err := ast.ParamsInSpecFactAreStrings(stmt.SpecFact)
	if err != nil {
		return ast.StmtErrRet(stmt, err.Error())
	}

	// prop 的定义
	definedStuff, ok := exec.Env.GetPropDef(stmt.SpecFact.PropName)
	if !ok {
		return ast.StmtErrRet(stmt, fmt.Sprintf("undefined prop: %s", stmt.SpecFact.PropName))
	}
	def := definedStuff.Defined
	if len(def.DefHeader.Params) != len(specFactAsParams) {
		return ast.StmtErrRet(stmt, fmt.Sprintf("prop %s has %d params, but %d params are expected", stmt.SpecFact.PropName, len(def.DefHeader.Params), len(specFactAsParams)))
	}

	if len(def.DefHeader.ParamSets) != len(stmt.SpecFact.Params) {
		return ast.StmtErrRet(stmt, fmt.Sprintf("prop %s has %d param sets, but %d params are expected", stmt.SpecFact.PropName, len(def.DefHeader.ParamSets), len(stmt.SpecFact.Params)))
	}

	// define params in env
	for _, param := range specFactAsParams {
		ret := exec.defLetStmt(ast.NewDefLetStmt([]string{param}, []ast.Obj{ast.Atom(glob.KeywordSet)}, []ast.FactStmt{}, stmt.Line))
		if ret.IsErr() {
			return ast.StmtErrRet(stmt, ret.String())
		}
	}

	// 让这些param符合 def domain
	uniMap := map[string]ast.Obj{}

	// 让 param 都在 set 里
	for i, param := range def.DefHeader.Params {
		instParamSet, err := def.DefHeader.ParamSets[i].Instantiate(uniMap)
		if err != nil {
			return ast.StmtErrRet(stmt, err.Error())
		}

		newInFact := ast.NewInFactWithObj(stmt.SpecFact.Params[i], instParamSet)
		ret := exec.Env.NewFactWithCheckingNameDefined(newInFact)
		if ret.IsErr() {
			return ast.StmtErrRet(stmt, ret.String())
		}

		uniMap[param] = stmt.SpecFact.Params[i]
	}

	// itself is true
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.SpecFact)
	if ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
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
			return ast.StmtErrRet(stmt, err.Error())
		}
		execState := exec.factStmt(instThenFact)
		if execState.IsNotTrue() {
			return execState
		}
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) equalSetStmt(stmt *ast.EqualSetStmt) ast.StmtRet {
	// 1. prove 过程（在局部环境中）
	ret := exec.equalSetStmtProveProcess(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	// 2. 存储过程（在原地存储）
	equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{stmt.Left, stmt.Right}, stmt.Line)
	ret2 := exec.Env.NewFactWithCheckingNameDefined(equalFact)
	if ret2.IsErr() {
		return ast.StmtErrRet(stmt, ret2.String())
	}

	newFactMsgs := []string{}
	if trueRet, ok := ret2.(*ast.TrueInferRet); ok {
		for _, inferFact := range trueRet.Infer {
			newFactMsgs = append(newFactMsgs, inferFact.String())
		}
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) equalSetStmtProveProcess(stmt *ast.EqualSetStmt) ast.StmtRet {
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
		[]ast.Spec_OrFact{},
		[]ast.Spec_OrFact{
			ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{ast.Atom("t"), b}, stmt.Line),
		},
		stmt.Line,
	)

	// Create forall t b : t $in a
	forall2 := ast.NewUniFact(
		[]string{"t"},
		[]ast.Obj{b},
		[]ast.Spec_OrFact{},
		[]ast.Spec_OrFact{
			ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{ast.Atom("t"), a}, stmt.Line),
		},
		stmt.Line,
	)

	// Verify both forall statements
	verRet1 := ver.VerFactStmt(forall1, state)
	if verRet1.IsNotTrue() {
		return ast.StmtErrRet(stmt, verRet1.String())
	}

	verRet2 := ver.VerFactStmt(forall2, state)
	if verRet2.IsNotTrue() {
		return ast.StmtErrRet(stmt, verRet2.String())
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) witnessNonemptyStmt(stmt *ast.WitnessNonemptyStmt) ast.StmtRet {
	// 1. prove 过程（在局部环境中）
	ret := exec.witnessNonemptyStmtProveProcess(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	// 2. 存储过程（在原地存储）
	isNonEmptyFact := ast.NewIsANonEmptySetFact(stmt.ObjSet, stmt.Line)
	ret2 := exec.Env.NewFactWithCheckingNameDefined(isNonEmptyFact)
	if ret2.IsErr() {
		return ast.StmtErrRet(stmt, ret2.String())
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) witnessNonemptyStmtProveProcess(stmt *ast.WitnessNonemptyStmt) ast.StmtRet {
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
		return ast.StmtErrRet(stmt, verRet.String())
	}
	if verRet.IsUnknown() {
		return ast.StmtErrRet(stmt, fmt.Sprintf("cannot verify that %s $in %s", stmt.Obj, stmt.ObjSet))
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) setIsFnStmt(stmt *ast.SetIsFnStmt) ast.StmtRet {
	// fnSetObj 是 fnSetObj
	if !ast.IsFnSet(stmt.FnSetObj) {
		return ast.StmtErrRet(stmt, fmt.Sprintf("%s is not a fn set object", stmt.FnSetObj))
	}

	verRet := exec.setIsFnStmt_ver(stmt)
	if verRet.IsNotTrue() {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(verRet.String())
	}

	defRet := exec.setIsFnStmt_NewFact(stmt)
	if defRet.IsNotTrue() {
		return ast.NewErrStmtEmptyRet(stmt).AddExtraInfo(defRet.String())
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) setIsFnStmt_ver(stmt *ast.SetIsFnStmt) ast.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	for _, curStmt := range stmt.Proof {
		ret := exec.Stmt(curStmt)
		if ret.IsNotTrue() {
			return ret
		}
	}

	fnParamSets := stmt.FnSetObj.FnHead.(*ast.FnObj).Params
	retSet := stmt.FnSetObj.Params[0]

	// 如果证明 x $in fn(A, B, C) D，那么要证明
	// 1. x subset_of cart(A, B, C, D)
	// 2. forall a A, b B, c C, d1 D, d2 D: (a, b, c, d1) $in x, (a, b, c, d2) $in x => d1 = d2
	// 3. forall a A, b B, c C: exist d D st (a, b, c, d) $in x
	allParamSets := append([]ast.Obj{}, fnParamSets...)
	allParamSets = append(allParamSets, retSet)
	subsetOfFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordSubsetOf), []ast.Obj{stmt.Obj, ast.NewFnObj(ast.Atom(glob.KeywordCart), allParamSets)}, glob.BuiltinLine0)
	ret := exec.factStmt(subsetOfFact)
	if ret.IsNotTrue() {
		return ret
	}

	// 生成随机参数名
	randomParams := exec.Env.GenerateNUnusedRandomNames(len(fnParamSets) + 2) // a, b, c, d1, d2

	// 创建元组 (a, b, c, d1) 和 (a, b, c, d2)
	tupleParams1 := make([]ast.Obj, len(fnParamSets)+1)
	tupleParams2 := make([]ast.Obj, len(fnParamSets)+1)
	for i := range len(fnParamSets) {
		tupleParams1[i] = ast.Atom(randomParams[i])
		tupleParams2[i] = ast.Atom(randomParams[i])
	}
	tupleParams1[len(fnParamSets)] = ast.Atom(randomParams[len(fnParamSets)])   // d1
	tupleParams2[len(fnParamSets)] = ast.Atom(randomParams[len(fnParamSets)+1]) // d2

	tuple1 := ast.NewFnObj(ast.Atom(glob.KeywordTuple), tupleParams1)
	tuple2 := ast.NewFnObj(ast.Atom(glob.KeywordTuple), tupleParams2)

	// 2. forall a A, b B, c C, d1 D, d2 D: (a, b, c, d1) $in x, (a, b, c, d2) $in x => d1 = d2
	paramSetsForUniFact1 := append([]ast.Obj{}, fnParamSets...)
	paramSetsForUniFact1 = append(paramSetsForUniFact1, retSet, retSet) // d1 D, d2 D

	domFacts1 := []ast.Spec_OrFact{
		ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{tuple1, stmt.Obj}, glob.BuiltinLine0),
		ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{tuple2, stmt.Obj}, glob.BuiltinLine0),
	}
	thenFacts1 := []ast.Spec_OrFact{
		ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{ast.Atom(randomParams[len(fnParamSets)]), ast.Atom(randomParams[len(fnParamSets)+1])}, glob.BuiltinLine0),
	}

	paramMapToTheSameImage := ast.NewUniFact(randomParams, paramSetsForUniFact1, domFacts1, thenFacts1, stmt.Line)
	ver := NewVerifier(exec.Env)
	verRet1 := ver.VerFactStmt(paramMapToTheSameImage, Round0Msg())
	if verRet1.IsNotTrue() {
		return ast.StmtErrRet(stmt, verRet1.String())
	}

	// 3. forall a A, b B, c C: exist d D st (a, b, c, d) $in x
	randomParamsForExist := randomParams[:len(fnParamSets)+1] // a, b, c, d
	tupleParamsForExist := make([]ast.Obj, len(fnParamSets)+1)
	for i := range len(fnParamSets) {
		tupleParamsForExist[i] = ast.Atom(randomParamsForExist[i])
	}
	tupleParamsForExist[len(fnParamSets)] = ast.Atom(randomParamsForExist[len(fnParamSets)]) // d
	tupleForExist := ast.NewFnObj(ast.Atom(glob.KeywordTuple), tupleParamsForExist)

	existFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{tupleForExist, stmt.Obj}, glob.BuiltinLine0)
	existStFact := ast.NewExistSpecificFactStmt(true, []string{randomParamsForExist[len(fnParamSets)]}, []ast.Obj{retSet}, []*ast.PureSpecificFactStmt{existFact}, stmt.Line)

	paramSetsForUniFact2 := fnParamSets
	domFacts2 := []ast.Spec_OrFact{}
	thenFacts2 := []ast.Spec_OrFact{existStFact}

	paramMapToExistImage := ast.NewUniFact(randomParamsForExist[:len(fnParamSets)], paramSetsForUniFact2, domFacts2, thenFacts2, stmt.Line)
	verRet2 := ver.VerFactStmt(paramMapToExistImage, Round0Msg())
	if verRet2.IsNotTrue() {
		return ast.StmtErrRet(stmt, verRet2.String())
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) setIsFnStmt_NewFact(stmt *ast.SetIsFnStmt) ast.StmtRet {
	// x $in fn(A, B, C) D
	inFact := ast.NewInFactWithObj(stmt.Obj, stmt.FnSetObj)
	ret := exec.Env.NewFactWithCheckingNameDefined(inFact)
	if ret.IsNotTrue() {
		return ast.StmtErrRet(stmt, ret.String())
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) fnIsSubsetOfCartStmt(stmt *ast.FnIsSubsetOfCartStmt) ast.StmtRet {
	// 证明 obj 在 setObj
	inFact := ast.NewInFactWithObj(stmt.Obj, stmt.FnSetObj)
	verRet := exec.factStmt(inFact)
	if verRet.IsNotTrue() {
		return ast.StmtErrRet(stmt, verRet.String())
	}

	// setObj 确实是 形如 fn(X1, X2, ..., Xn) Y 的 obj
	switch stmt.FnSetObj.(type) {
	case *ast.FnSetObjWithName:
		panic("not implemented: fnIsSubsetOfCartStmt: FnSetObjWithName is not implemented")
	case *ast.FnSetObjWithoutName:
		return exec.fnIsSubsetOfCartStmt_FnSetObjWithOutName(stmt)
	default:
		return ast.StmtErrRet(stmt, fmt.Sprintf("unknown FnSetObj type: %T", stmt.FnSetObj))
	}

}

func (exec *Executor) fnIsSubsetOfCartStmt_FnSetObjWithOutName(stmt *ast.FnIsSubsetOfCartStmt) ast.StmtRet {
	newFacts := []ast.InferRet{}

	fnSetObjWithOutName, ok := stmt.FnSetObj.(*ast.FnSetObjWithoutName)
	if !ok {
		return ast.StmtErrRet(stmt, fmt.Sprintf("fnSetObj is not a FnSetObjWithoutName: %s", stmt.FnSetObj.String()))
	}

	// obj subset_of cart(X1, X2, ..., Xn, Y) 中
	doms := fnSetObjWithOutName.ParamSets
	fName := stmt.Obj
	carXToYParams := []ast.Obj{}
	for _, dom := range doms {
		carXToYParams = append(carXToYParams, dom)
	}
	carXToYParams = append(carXToYParams, fnSetObjWithOutName.RetSet)
	cartSet := ast.NewFnObj(ast.Atom(glob.KeywordCart), carXToYParams)
	subsetOfFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordSubsetOf), []ast.Obj{stmt.Obj, cartSet}, stmt.Line)
	inferRet := exec.Env.NewFactWithCheckingNameDefined(subsetOfFact)
	if inferRet.IsNotTrue() {
		return ast.StmtErrRet(stmt, inferRet.String())
	}
	newFacts = append(newFacts, inferRet)

	// obj 满足： forall x1, x2, ..., xn X: (x1, x2, ..., xn, f(x1, x2, ..., xn)) $in obj
	nRandomParams := exec.Env.GenerateNUnusedRandomNames(len(doms))
	tupleParams := []ast.Obj{}
	for _, param := range nRandomParams {
		tupleParams = append(tupleParams, ast.Atom(param))
	}
	tupleParams = append(tupleParams, ast.NewFnObj(fName, tupleParams))
	tupleOfX := ast.NewFnObj(ast.Atom(glob.KeywordTuple), tupleParams)
	forallFact := ast.NewUniFact(nRandomParams, doms, []ast.Spec_OrFact{}, []ast.Spec_OrFact{ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{tupleOfX, stmt.Obj}, stmt.Line)}, stmt.Line)
	inferRet = exec.Env.NewFactWithCheckingNameDefined(forallFact)
	if inferRet.IsNotTrue() {
		return ast.StmtErrRet(stmt, inferRet.String())
	}

	newFacts = append(newFacts, inferRet)

	// obj 满足: forall x1, x2, ..., xn X, y Y: (x1, x2, ..., xn, y) $in obj => y = obj(x1, x2, ..., xn)
	nPlus1RandomParams := exec.Env.GenerateNUnusedRandomNames(len(doms) + 1)
	tupleParamsForEqual := []ast.Obj{}
	for _, param := range nPlus1RandomParams {
		tupleParamsForEqual = append(tupleParamsForEqual, ast.Atom(param))
	}
	fX1ToXn := ast.NewFnObj(fName, tupleParamsForEqual[:len(doms)])
	y := ast.Atom(nPlus1RandomParams[len(doms)])
	tupleFromXToY := ast.NewFnObj(ast.Atom(glob.KeywordTuple), tupleParamsForEqual)
	equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{y, fX1ToXn}, stmt.Line)
	dom2 := append([]ast.Obj{}, doms...)
	dom2 = append(dom2, fnSetObjWithOutName.RetSet)
	forallFact2 := ast.NewUniFact(nPlus1RandomParams, dom2, []ast.Spec_OrFact{ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{tupleFromXToY, stmt.Obj}, stmt.Line)}, []ast.Spec_OrFact{equalFact}, stmt.Line)
	inferRet = exec.Env.NewFactWithCheckingNameDefined(forallFact2)
	if inferRet.IsNotTrue() {
		return ast.StmtErrRet(stmt, inferRet.String())
	}

	newFacts = append(newFacts, inferRet)

	return exec.NewTrueStmtRet(stmt).AddInfers(newFacts)
}

func (exec *Executor) haveFnEqual(stmt *ast.HaveFnEqual) ast.StmtRet {
	fnObj := ast.NewFnObj(ast.Atom(stmt.DefHeaderWithDom.Name), stmt.DefHeaderWithDom.Params.ToObjSlice())
	equalFact := ast.NewEqualFact(fnObj, stmt.EqualTo)

	fnSetWithName := ast.NewFnSetObjWithName(stmt.DefHeaderWithDom.Name, stmt.DefHeaderWithDom.Params, stmt.DefHeaderWithDom.ParamSets, stmt.DefHeaderWithDom.DomFacts, stmt.RetSet, []ast.Spec_OrFact{equalFact})

	ret, msg := exec.Env.CheckAtomObjNameIsValidAndAvailableThenDefineIt(stmt.DefHeaderWithDom.Name)
	if !ret {
		return ast.StmtErrRet(stmt, msg)
	}

	inFact := ast.NewInFactWithObj(ast.Atom(stmt.DefHeaderWithDom.Name), fnSetWithName)
	ret2 := exec.Env.NewFactWithCheckingNameDefined(inFact)
	if ret2.IsNotTrue() {
		return ast.StmtErrRet(stmt, ret2.String())
	}

	return exec.NewTrueStmtRet(stmt).AddInfers([]ast.InferRet{ret2})
}

func (exec *Executor) haveFnEqualCaseByCase(stmt *ast.HaveFnEqualCaseByCase) ast.StmtRet {
	// Verify first
	ret := exec.haveFnEqualCaseByCase_Verify(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	// Then define
	newRet := exec.haveFnEqualCaseByCase_Define(stmt)
	if newRet.IsNotTrue() {
		return newRet
	}

	verifyProcessMsgs := []ast.VerRet{}
	defineMsgs := []string{}
	if trueRet, ok := ret.(*ast.TrueStmtRet); ok {
		verifyProcessMsgs = append(verifyProcessMsgs, trueRet.VerifyProcess...)
	}
	if trueRet, ok := newRet.(*ast.TrueStmtRet); ok {
		defineMsgs = append(defineMsgs, trueRet.Define...)
	}

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessMsgs).AddDefineMsgs(defineMsgs)
}

func (exec *Executor) haveFnEqualCaseByCase_Verify(stmt *ast.HaveFnEqualCaseByCase) ast.StmtRet {
	verifyProcessMsgs := []ast.VerRet{}

	exec.NewEnv()
	defer exec.deleteEnv()

	// 申明所有的param
	newLetStmt := ast.NewDefLetStmt(stmt.DefHeaderWithDom.Params, stmt.DefHeaderWithDom.ParamSets, stmt.DefHeaderWithDom.DomFacts.ToFactStmtSlice(), stmt.Line)
	execState := exec.defLetStmt(newLetStmt)
	if execState.IsNotTrue() {
		return ast.StmtErrRet(stmt, execState.String())
	}

	verRet := exec.haveFnEqualCaseByCase_CheckAllCasesCoverDomain_CasesNoOverlap_ReturnValueInRetSet(stmt)
	if verRet.IsNotTrue() {
		return verRet
	}

	return newTrueStmtRetWithCaller().AddVerifyProcesses(verifyProcessMsgs)
}

func (exec *Executor) haveFnEqualCaseByCase_CheckAllCasesCoverDomain_CasesNoOverlap_ReturnValueInRetSet(stmt *ast.HaveFnEqualCaseByCase) ast.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	// 证明 proof
	for _, proof := range stmt.ProveCases {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return ast.StmtErrRet(stmt, execState.String())
		}
	}

	// 证明 or cases 成立
	orFact := ast.NewOrStmt(stmt.CaseByCaseFacts, stmt.Line)
	execState := exec.factStmt(orFact)
	if execState.IsNotTrue() {
		return ast.StmtErrRet(stmt, execState.String())
	}

	// 证明 cases 互相不冲突
	for i := range len(stmt.CaseByCaseFacts) {
		execState = exec.haveFnEqualCaseByCase_CheckCasesNotOverlap_ReturnValueInRetSet(stmt, i)
		if execState.IsNotTrue() {
			return ast.StmtErrRet(stmt, execState.String())
		}
	}

	return exec.NewTrueStmtRet(orFact)
}

func (exec *Executor) haveFnEqualCaseByCase_CheckCasesNotOverlap_ReturnValueInRetSet(stmt *ast.HaveFnEqualCaseByCase, index int) ast.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	// index known是对的
	retInfer := exec.Env.NewFactWithCheckingNameDefined(stmt.CaseByCaseFacts[index])
	if retInfer.IsNotTrue() {
		return ast.StmtErrRet(stmt, retInfer.String())
	}

	// 其他index的逆都是错的
	for i := range len(stmt.CaseByCaseFacts) {
		if i == index {
			continue
		}
		notOtherCaseFacts := stmt.CaseByCaseFacts[i].ReverseIsTrue()
		for _, notOtherCaseFact := range notOtherCaseFacts {
			execState := exec.factStmt(notOtherCaseFact)
			if execState.IsNotTrue() {
				return ast.StmtErrRet(stmt, execState.String())
			}
		}
	}

	// 跑case proof
	for _, curStmt := range stmt.Proofs[index] {
		retStmt := exec.Stmt(curStmt)
		if retStmt.IsNotTrue() {
			return retStmt
		}
	}

	// 返回值在 retSet里
	inFact := ast.NewInFactWithObj(stmt.CaseByCaseEqualTo[index], stmt.RetSet)
	retStmt := exec.factStmt(inFact)
	if retStmt.IsNotTrue() {
		return retStmt
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) haveFnEqualCaseByCase_Define(stmt *ast.HaveFnEqualCaseByCase) ast.StmtRet {
	fnObj := ast.NewFnObj(ast.Atom(stmt.DefHeaderWithDom.Name), stmt.DefHeaderWithDom.Params.ToObjSlice())

	// // Create equal facts for each case
	// equalFacts := []ast.Spec_OrFact{}
	// for i := range len(stmt.CaseByCaseFacts) {
	// 	equalFact := ast.NewEqualFact(fnObj, stmt.CaseByCaseEqualTo[i])
	// 	equalFacts = append(equalFacts, equalFact)
	// }

	fnSetWithName := ast.NewFnSetObjWithName(stmt.DefHeaderWithDom.Name, stmt.DefHeaderWithDom.Params, stmt.DefHeaderWithDom.ParamSets, stmt.DefHeaderWithDom.DomFacts, stmt.RetSet, []ast.Spec_OrFact{})

	ret, msg := exec.Env.CheckAtomObjNameIsValidAndAvailableThenDefineIt(stmt.DefHeaderWithDom.Name)
	if !ret {
		return ast.StmtErrRet(stmt, msg)
	}

	inFact := ast.NewInFactWithObj(ast.Atom(stmt.DefHeaderWithDom.Name), fnSetWithName)
	ret2 := exec.Env.NewFactWithCheckingNameDefined(inFact)
	if ret2.IsNotTrue() {
		return ast.StmtErrRet(stmt, ret2.String())
	}

	// forall params, paramSets
	for i, caseFact := range stmt.CaseByCaseFacts {
		domFact := append([]ast.Spec_OrFact{}, stmt.DefHeaderWithDom.DomFacts...)
		domFact = append(domFact, caseFact)
		equalFact := ast.NewEqualFact(fnObj, stmt.CaseByCaseEqualTo[i])
		forallFact := ast.NewUniFact(stmt.DefHeaderWithDom.Params, stmt.DefHeaderWithDom.ParamSets, domFact, []ast.Spec_OrFact{equalFact}, stmt.Line)
		ret3 := exec.Env.NewFactWithCheckingNameDefined(forallFact)
		if ret3.IsNotTrue() {
			return ast.StmtErrRet(stmt, ret3.String()).AddExtraInfo(forallFact.String())
		}
	}

	return exec.NewTrueStmtRet(stmt).AddInfers([]ast.InferRet{ret2})
}

func (exec *Executor) letFn(stmt *ast.LetFn) ast.StmtRet {
	fnWithName := ast.NewFnSetObjWithName(stmt.DefHeaderWithDom.Name, stmt.DefHeaderWithDom.Params, stmt.DefHeaderWithDom.ParamSets, stmt.DefHeaderWithDom.DomFacts, stmt.RetSet, stmt.ThenFacts)

	// 先定义f
	defLetStmt := ast.NewDefLetStmt([]string{stmt.DefHeaderWithDom.Name}, []ast.Obj{fnWithName}, []ast.FactStmt{}, stmt.Line)

	ret := exec.defLetStmt(defLetStmt)
	if ret.IsNotTrue() {
		return ast.StmtErrRet(stmt, ret.String())
	}

	return exec.NewTrueStmtRet(stmt).AddDefineMsgs(ret.GetDefineMsgs()).AddInfers(ret.GetInfers())
}
