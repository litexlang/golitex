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
		err = exec.defPropStmt(stmt, true)
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
	case *ast.NamedUniFactStmt:
		execState, err = exec.namedUniFactStmt(stmt)
	case *ast.KnowExistPropStmt:
		_, err = exec.knowExistPropStmt(stmt)
	case *ast.FnTemplateDefStmt:
		err = exec.fnTemplateStmt(stmt)
	case *ast.ClearStmt:
		exec.clearStmt()
	case *ast.InlineFactsStmt:
		execState, err = exec.inlineFactsStmt(stmt)
	case *ast.ProveByInductionStmt:
		execState, err = exec.proveByInductionStmt(stmt)
	case *ast.HaveObjEqualStmt:
		execState, err = exec.haveObjEqualStmt(stmt)
	default:
		err = fmt.Errorf("unknown statement type: %T", stmt)
	}

	if err != nil {
		return glob.ExecState_Error, fmt.Errorf("execution error: %w", err)
	} else {
		return execState, nil
	}
}

func (exec *Executor) factStmt(stmt ast.FactStmt) (glob.ExecState, error) {
	if glob.RequireMsg() {
		defer exec.newMsg("\n")
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

	if glob.RequireMsg() {
		exec.newMsg(stmt.String() + "\nis unknown")
	}

	return glob.ExecState_Unknown, nil
}

// TODO: 再know时就检查，仅仅依赖写在dom里的事实，是否真的能让涉及到的函数和prop能真的满足条件。如果不满足条件，那就warning
func (exec *Executor) knowStmt(stmt *ast.KnowFactStmt) error {
	if glob.RequireMsg() {
		defer exec.newMsg("\n")
	}

	for _, fact := range stmt.Facts {
		switch fact := fact.(type) {
		case ast.FactStmt:
			if !exec.env.AreAtomsInFactAreDeclared(fact, map[string]struct{}{}) {
				return fmt.Errorf(env.AtomsInFactNotDeclaredMsg(fact))
			}

			err := exec.env.NewFact(fact)
			if err != nil {
				return err
			}
		case *ast.KnowPropStmt:
			err := exec.knowPropStmt(fact)
			if err != nil {
				return err
			}
		default:
			return fmt.Errorf("unknown fact type: %T", fact)
		}
	}

	if glob.RequireMsg() {
		exec.newMsg(stmt.String())
	}
	return nil
}

func (exec *Executor) GetMsgAsStr0ToEnd() string {
	ret := strings.Join(exec.env.Msgs, "\n")
	exec.env.Msgs = []string{}
	return ret
}

func (exec *Executor) defPropStmt(stmt *ast.DefPropStmt, generateIffUniFact bool) error {
	if glob.RequireMsg() {
		defer exec.newMsg(stmt.String() + "\n")
	}

	err := exec.env.NewDefProp_InsideAtomsDeclared(stmt)
	if err != nil {
		return err
	}

	if len(stmt.IffFacts) == 0 {
		return nil
	}

	if generateIffUniFact {
		// prop leads to iff
		propToIff, iffToProp, err := stmt.Make_PropToIff_IffToProp()
		if err != nil {
			return err
		}

		err = exec.env.NewFact(propToIff)
		if err != nil {
			return err
		}
		if glob.RequireMsg() {
			exec.newMsg(fmt.Sprintf("%s\nis true by definition", propToIff))
		}

		err = exec.env.NewFact(iffToProp)
		if err != nil {
			return err
		}
		if glob.RequireMsg() {
			exec.newMsg(fmt.Sprintf("%s\nis true by definition", iffToProp))
		}
	}
	return nil
}

func (exec *Executor) defObjStmt(stmt *ast.DefObjStmt, requireMsg bool) error {
	if glob.RequireMsg() && requireMsg {
		defer exec.newMsg(fmt.Sprintf("%s\n", stmt))
	}

	ver := verifier.NewVerifier(exec.env)
	return ver.NewDefObj_InsideAtomsDeclared(stmt)
}

func (exec *Executor) defExistPropStmt(stmt *ast.DefExistPropStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	if glob.RequireMsg() {
		defer exec.newMsg(fmt.Sprintf("%s\n", stmt))
	}

	return exec.env.NewDefExistProp_InsideAtomsDeclared(stmt)
}

func (exec *Executor) execStmtsAtCurEnv(proof []ast.Stmt) (glob.ExecState, error) {
	for _, curStmt := range proof {
		execState, err := exec.Stmt(curStmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			if execState == glob.ExecState_Unknown && glob.ContinueExecutionIfExecUnknown {
				exec.appendWarningMsg(fmt.Sprintf("unknown fact:\n%s", curStmt))
				return glob.ExecState_Unknown, nil
			} else {
				return execState, nil
			}
		}
	}
	return glob.ExecState_True, nil
}

func (exec *Executor) proveInEachCaseStmt(stmt *ast.ProveInEachCaseStmt) (glob.ExecState, error) {
	isSuccess := false
	defer func() {
		if glob.RequireMsg() {
			exec.newMsg("\n")
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
		if glob.RequireMsg() {
			exec.newMsg(fmt.Sprintf("%s is unknown", stmt.OrFact))
		}
		return execState, err
	}

	for i := range stmt.OrFact.Facts {
		execState, err := exec.execProofBlockForEachCase(i, stmt)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	// emit then fact
	err = exec.knowStmt(ast.NewKnowStmt(stmt.ThenFacts.ToCanBeKnownStmtSlice()))
	if err != nil {
		return glob.ExecState_Error, err
	}

	isSuccess = true
	return glob.ExecState_True, nil
}

func (exec *Executor) execProofBlockForEachCase(index int, stmt *ast.ProveInEachCaseStmt) (glob.ExecState, error) {
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndRetainMsg()

	caseStmt := stmt.OrFact.Facts[index]

	err := exec.env.NewFact(caseStmt)
	if err != nil {
		return glob.ExecState_Error, err
	}

	execState, err := exec.execStmtsAtCurEnv(stmt.Proofs[index])
	if notOkExec(execState, err) {
		return execState, err
	}

	// verify thenFacts are true
	execState, failedFact, err := verifier.ExecFactsAtCurEnv_retRailedFact(stmt.ThenFacts, exec.env)
	if err != nil {
		return execState, fmt.Errorf("prove in each case statement error: failed to verify then facts:\n%s\n%s", failedFact, err)
	} else if execState != glob.ExecState_True {
		return execState, fmt.Errorf("prove in each case statement error: failed to verify then facts:\n%s", failedFact)
	}

	return glob.ExecState_True, nil
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
func (exec *Executor) knowPropStmt(stmt *ast.KnowPropStmt) error {
	if glob.RequireMsg() {
		defer func() {
			exec.newMsg(fmt.Sprintf("%s\n", stmt))
		}()
	}

	err := exec.defPropStmt(&stmt.Prop, false)
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
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndRetainMsg()

	return exec.execStmtsAtCurEnv(stmt.Proof)
}

func (exec *Executor) defFnStmt(stmt *ast.DefFnStmt) error {
	if glob.RequireMsg() {
		defer func() {
			exec.newMsg(fmt.Sprintf("%s\n", stmt))
		}()
	}

	err := exec.env.IsValidUserDefinedName_NoDuplicate(stmt.Name)
	if err != nil {
		return err
	}

	// 在 objMem 里记录一下
	exec.env.ObjDefMem[stmt.Name] = nil

	err = exec.env.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(ast.FcAtom(stmt.Name), nil, &stmt.FnTemplate)
	if err != nil {
		return err
	}

	derivedFact, err := stmt.FnTemplate.DeriveUniFact_WithGivenFn(ast.FcAtom(stmt.Name))
	if err != nil {
		return err
	}

	err = exec.env.NewFact(derivedFact)
	if err != nil {
		return err
	}

	if glob.RequireMsg() {
		exec.newMsg(fmt.Sprintf("%s\nis true by definition", derivedFact))
	}

	return nil
}

func (exec *Executor) proveOverFiniteSetStmt(stmt *ast.ProveOverFiniteSetStmt) (glob.ExecState, error) {
	exec.newMsg(stmt.String())

	ver := verifier.NewVerifier(exec.env)
	execState, err := ver.ProveOverFiniteSet(stmt)
	if notOkExec(execState, err) {
		return execState, err
	}

	// know uniFact
	err = exec.env.NewFact(&stmt.Fact)
	if err != nil {
		return glob.ExecState_Error, err
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) haveSetFnStmt(stmt *ast.HaveSetFnStmt) (glob.ExecState, error) {
	exec.newMsg(stmt.String())

	// declare related fn
	fnDefStmt := stmt.ToDefFnStmt()
	err := exec.defFnStmt(fnDefStmt)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// have set fn
	exec.env.HaveSetFnDefMem[string(stmt.DefHeader.Name)] = *stmt

	return glob.ExecState_True, nil
}

func (exec *Executor) haveSetDefinedByReplacementStmt(stmt *ast.HaveSetDefinedByReplacementStmt) (glob.ExecState, error) {
	exec.newMsg(stmt.String())

	setDefinedByReplacement := ast.NewFcFn(ast.FcAtom(glob.KeywordSetDefinedByReplacement), []ast.Fc{stmt.DomSet, stmt.RangeSet, stmt.PropName})

	defObjStmt := ast.NewDefObjStmt([]string{stmt.Name}, []ast.Fc{ast.FcAtom(glob.KeywordSet)}, []ast.FactStmt{ast.NewEqualFact(ast.FcAtom(stmt.Name), setDefinedByReplacement)})

	err := exec.defObjStmt(defObjStmt, false)
	if err != nil {
		return glob.ExecState_Error, err
	}

	err = exec.env.SetEqualToSetDefinedByReplacement_PostProcess(ast.FcAtom(stmt.Name), setDefinedByReplacement)
	if err != nil {
		return glob.ExecState_Error, err
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) namedUniFactStmt(stmt *ast.NamedUniFactStmt) (glob.ExecState, error) {
	exec.newMsg(stmt.String())

	uniFact := ast.NewUniFact(stmt.DefPropStmt.DefHeader.Params, stmt.DefPropStmt.DefHeader.ParamSets, stmt.DefPropStmt.IffFacts, stmt.DefPropStmt.ThenFacts)
	execState, err := exec.factStmt(uniFact)
	if notOkExec(execState, err) {
		return execState, err
	}

	err = exec.knowPropStmt(ast.NewKnowPropStmt(stmt.DefPropStmt))
	if notOkExec(execState, err) {
		return execState, err
	}

	return glob.ExecState_True, nil
}

// 只要 dom 成立，那prop成立，进而prop的iff成立
func (exec *Executor) knowExistPropStmt(stmt *ast.KnowExistPropStmt) (glob.ExecState, error) {
	if glob.RequireMsg() {
		defer func() {
			exec.newMsg(fmt.Sprintf("%s\n", stmt))
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

	if glob.RequireMsg() {
		exec.newMsg(fmt.Sprintf("%s\nis true by definition", knownUniFact))
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) fnTemplateStmt(stmt *ast.FnTemplateDefStmt) error {
	if glob.RequireMsg() {
		defer exec.newMsg(fmt.Sprintf("%s\n", stmt))
	}

	err := exec.env.ExecDefFnTemplate(stmt)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) clearStmt() error {
	curEnv := exec.env
	for curEnv.Parent != nil {
		curEnv = curEnv.Parent
	}
	exec.NewEnv(curEnv)
	if glob.RequireMsg() {
		exec.newMsg("clear\n")
	}
	return nil
}

func (exec *Executor) inlineFactsStmt(stmt *ast.InlineFactsStmt) (glob.ExecState, error) {
	for _, fact := range stmt.Facts {
		execState, err := exec.factStmt(fact)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) haveObjEqualStmt(stmt *ast.HaveObjEqualStmt) (glob.ExecState, error) {
	exec.newMsg(stmt.String())

	return glob.ExecState_True, nil
}
