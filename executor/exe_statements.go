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
// Litex Zulip community: https://litex.zulipchat.com

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
	parser "golitex/parser"
	taskManager "golitex/task_manager"
	verifier "golitex/verifier"
	"os"
	"path/filepath"
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
		err = exec.defPropStmt(stmt)
	case *ast.DefObjStmt:
		err = exec.defObjStmt(stmt, true)
	case *ast.HaveStmt:
		execState, err = exec.haveStmt(stmt)
	case *ast.DefExistPropStmt:
		err = exec.defExistPropStmt(stmt)
	case *ast.DefFnStmt:
		err = exec.defFnStmt(stmt)
	case *ast.KnowPropStmt:
		err = exec.knowPropStmt(stmt)
	case *ast.KnowExistPropStmt:
		_, err = exec.knowExistPropStmt(stmt)
	case *ast.ProveInEachCaseStmt:
		execState, err = exec.proveInEachCaseStmt(stmt)
	case *ast.SupposeStmt:
		execState, err = exec.supposePropMatchStmt(stmt)
	case *ast.WithStmt:
		execState, err = exec.withStmt(stmt)
	case *ast.ImportStmt:
		err = exec.importStmt(stmt)
	case *ast.PubStmt:
		execState, err = exec.pubStmt(stmt)
	case *ast.ProveStmt:
		execState, err = exec.proveStmt(stmt)
	case *ast.ClaimProveByContradictionStmt:
		execState, err = exec.execClaimStmtProveByContradiction(stmt)
	default:
		err = fmt.Errorf("unknown statement type: %T", stmt)
	}

	if err != nil {
		return glob.ExecState_Error, glob.NewErrLink(err, "execution error:")
	} else {
		return execState, nil
	}
}

func (exec *Executor) pubStmt(stmt *ast.PubStmt) (glob.ExecState, error) {
	return exec.execProofBlock(stmt.Stmts)
}

func (exec *Executor) factStmt(stmt ast.FactStmt) (glob.ExecState, error) {
	defer exec.appendMsg("\n")

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

	if glob.CheckFalse {
		if asSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
			reversedFact := asSpecFact.ReverseTrue()
			curVerifier := verifier.NewVerifier(exec.env)
			ok, err := curVerifier.VerFactStmt(reversedFact, verifier.Round0Msg)
			if err != nil {
				return glob.ExecState_Error, err
			}
			if ok {
				exec.appendMsg(asSpecFact.String() + "\nis false")
				return glob.ExecState_False, nil
			} else {
				exec.appendMsg(stmt.String() + "\nis unknown")
			}
		} else {
			exec.appendMsg(stmt.String() + "\nis unknown")
		}
	} else {
		exec.appendMsg(stmt.String() + "\nis unknown")
	}

	return glob.ExecState_Unknown, nil
}

// TODO: 再know时就检查，仅仅依赖写在dom里的事实，是否真的能让涉及到的函数和prop能真的满足条件。如果不满足条件，那就warning
func (exec *Executor) knowStmt(stmt *ast.KnowFactStmt) error {
	defer exec.appendMsg("\n")

	for _, fact := range stmt.Facts {
		extraAtoms := map[string]struct{}{}
		if asUniFact, ok := fact.(*ast.UniFactStmt); ok {
			for _, param := range asUniFact.Params {
				extraAtoms[param] = struct{}{}
			}
		} else if asUniFactWithIff, ok := fact.(*ast.UniFactWithIffStmt); ok {
			for _, param := range asUniFactWithIff.UniFact.Params {
				extraAtoms[param] = struct{}{}
			}
		}

		if !exec.env.AreAtomsInFactAreDeclared(fact, extraAtoms) {
			return fmt.Errorf(env.AtomsInFactNotDeclaredMsg(fact))
		}

		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	exec.appendMsg(stmt.String())
	return nil
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
	exec.knowStmt(ast.NewKnowStmt([]ast.FactStmt{stmt.Claim.ToCheckFact}))

	return glob.ExecState_True, nil
}

func (exec *Executor) GetMsgAsStr0ToEnd() string {
	return strings.Join(exec.env.Msgs, "\n")
}

func (exec *Executor) defPropStmt(stmt *ast.DefPropStmt) error {
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	err := exec.env.NewDefProp_InsideAtomsDeclared(stmt)
	if err != nil {
		return err
	}

	// prop leads to iff
	if stmt.IffFacts == nil || len(stmt.IffFacts) == 0 {
		return nil
	}

	propToIff, iffToProp, err := stmt.Make_PropToIff_IffToProp()
	if err != nil {
		return err
	}
	err = exec.env.NewFact(propToIff)
	if err != nil {
		return err
	}
	exec.appendMsg(fmt.Sprintf("%s\nis true by definition", propToIff.String()))

	err = exec.env.NewFact(iffToProp)
	if err != nil {
		return err
	}
	exec.appendMsg(fmt.Sprintf("%s\nis true by definition", iffToProp.String()))

	if len(stmt.IffFacts) == 0 {
		return nil
	}

	return nil
}

func (exec *Executor) defObjStmt(stmt *ast.DefObjStmt, requireMsg bool) error {
	defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))

	if requireMsg {
		defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
	}

	ver := verifier.NewVerifier(exec.env)
	return ver.NewDefObj_InsideAtomsDeclared(stmt)
}

func (exec *Executor) defFnStmt(stmt *ast.DefFnStmt) error {
	defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))

	err := exec.env.NewDefFn_InsideAtomsDeclared(stmt)
	if err != nil {
		return err
	}

	// the function object is in fn
	fnSet := ast.MakeFnSetFc(stmt.DefHeader.SetParams, stmt.RetSet)

	inFact := ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{ast.NewFcAtomWithName(stmt.DefHeader.Name), fnSet})
	err = exec.env.NewFact(inFact)
	if err != nil {
		return err
	}

	thenFacts := []ast.FactStmt{}
	thenFacts = append(thenFacts, stmt.ThenFacts...)

	uniFact := ast.NewUniFact(stmt.DefHeader.Params, stmt.DefHeader.SetParams, stmt.DomFacts, thenFacts)
	err = exec.env.NewFact(uniFact)

	if err != nil {
		return err
	}

	// 现在只处理dom里没额外的东西的情况
	if len(stmt.DomFacts) == 0 {
		fnSet := ast.NewFcFn(ast.NewFcFn(ast.NewFcAtomWithName(glob.KeywordFn), stmt.DefHeader.SetParams), []ast.Fc{stmt.RetSet})

		newFact := ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{ast.NewFcAtomWithName(stmt.DefHeader.Name), fnSet})

		err = exec.env.NewFact(newFact)
		if err != nil {
			return err
		}
	}

	return nil
}

func (exec *Executor) defExistPropStmt(stmt *ast.DefExistPropStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	return exec.env.NewDefExistProp_InsideAtomsDeclared(stmt)
}

func (exec *Executor) haveStmt(stmt *ast.HaveStmt) (glob.ExecState, error) {
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	// 检查 SpecFactStmt 是否满足了
	execState, err := exec.factStmt(&stmt.Fact)
	if notOkExec(execState, err) {
		exec.appendMsg(fmt.Sprintf("%s is unknown", stmt.Fact.String()))
		return execState, err
	}

	// TODO： have 可能会引入3种不同的东西：set,obj,fn都可能；每种情况，处理起来不一样：比如如果你是fn和set，那可能就要把你放到 setMem 和 fnMem 里了
	// 这个 warning 不合时宜了，因为fn的定义其实和obj一样了，就是额外多个满足特定的template
	exec.appendInternalWarningMsg("Litex only support have obj. if you want to introduce set or fn by the have stmt, you need to use the set or fn stmt to introduce them.")

	// TODO 把 exist prop def 里的东西释放出来
	existPropDef, ok := exec.env.GetExistPropDef(stmt.Fact.PropName)
	if !ok {
		return glob.ExecState_Unknown, nil
	}

	if len(existPropDef.ExistParams) != len(stmt.ObjNames) {
		return glob.ExecState_Error, fmt.Errorf("exist prop def params number not equal to have stmt obj names number. expect %d, but got %d", len(existPropDef.ExistParams), len(stmt.ObjNames))
	}

	uniMap := map[string]ast.Fc{}
	ExistParamsAtoms := []ast.Fc{}
	for i, param := range existPropDef.ExistParams {
		paramAsAtom := ast.NewFcAtomWithName(stmt.ObjNames[i])
		uniMap[param] = paramAsAtom
		ExistParamsAtoms = append(ExistParamsAtoms, paramAsAtom)
	}

	for i, param := range existPropDef.DefBody.DefHeader.Params {
		uniMap[param] = stmt.Fact.Params[i]
	}

	instantiatedExistPropDefStmt, err := existPropDef.Instantiate(uniMap)
	if err != nil {
		return glob.ExecState_Error, err
	}

	ver := verifier.NewVerifier(exec.env)

	// 把 obj 放入环境
	for i, objName := range stmt.ObjNames {
		err := ver.NewDefObj_InsideAtomsDeclared(ast.NewDefObjStmt([]string{objName}, []ast.Fc{instantiatedExistPropDefStmt.ExistParamSets[i]}, []ast.FactStmt{}))
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// param in param sets is true
	// for _, paramInParamSet := range instantiatedExistPropDefStmt.ExistParamInSetsFacts() {
	// 	err := exec.env.NewFact(paramInParamSet)
	// 	if err != nil {
	// 		return glob.ExecState_Error, err
	// 	}
	// }

	for i, existParamSet := range instantiatedExistPropDefStmt.ExistParamSets {
		err := exec.env.NewFact(ast.NewInFact(stmt.ObjNames[i], existParamSet))
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// dom of def exist prop is true
	for _, domFact := range instantiatedExistPropDefStmt.DefBody.DomFacts {
		err := exec.env.NewFact(domFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		exec.appendMsg(fmt.Sprintf("%s\nis true by definition", domFact.String()))
	}

	// iff of def exist prop is true
	for _, iffFact := range instantiatedExistPropDefStmt.DefBody.IffFacts {
		err := exec.env.NewFact(iffFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		exec.appendMsg(fmt.Sprintf("%s\nis true by definition", iffFact.String()))
	}

	// 相关的 exist st 事实也成立
	existStFactParams := []ast.Fc{}
	existStFactParams = append(existStFactParams, ExistParamsAtoms...)
	existStFactParams = append(existStFactParams, ast.BuiltinExist_St_FactExistParamPropParmSepAtom)
	existStFactParams = append(existStFactParams, stmt.Fact.Params...)

	newExistStFact := ast.NewSpecFactStmt(ast.TrueExist_St, ast.NewFcAtomWithName(stmt.Fact.PropName.Name), existStFactParams)
	err = exec.env.NewFact(newExistStFact)
	if err != nil {
		return glob.ExecState_Error, err
	}
	exec.appendMsg(fmt.Sprintf("%s\nis true by definition", newExistStFact.String()))

	return glob.ExecState_True, nil
}

func (exec *Executor) execProofBlock(proof []ast.Stmt) (glob.ExecState, error) {
	for _, curStmt := range proof {
		execState, err := exec.Stmt(curStmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			if execState == glob.ExecState_Unknown && glob.ContinueExecutionIfExecUnknown {
				exec.appendWarningMsg("unknown fact:\n%s", curStmt.String())
				return glob.ExecState_Unknown, nil
			} else {
				return execState, nil
			}
		}
	}
	return glob.ExecState_True, nil
}

func (exec *Executor) claimStmtProve(stmt *ast.ClaimProveStmt) (glob.ExecState, error) {
	err := error(nil)
	isSuccess := false

	exec.newEnv(exec.env, exec.env.CurMatchProp)
	defer func() {
		exec.appendMsg("\n")
		if isSuccess {
			exec.appendNewMsgAtBegin("is true\n\n")
		} else {
			exec.appendNewMsgAtBegin("is unknown\n\n")
		}
		exec.appendNewMsgAtBegin(stmt.String())
		exec.deleteEnvAndRetainMsg()
	}()

	// 需要检查stmt.ToCheckFact里的东西都是在外部声明好了的
	if stmt.ToCheckFact != ast.ClaimStmtEmptyToCheck {
		ok := exec.env.AreAtomsInFactAreDeclared(stmt.ToCheckFact, map[string]struct{}{})
		if !ok {
			return glob.ExecState_Error, fmt.Errorf(env.AtomsInFactNotDeclaredMsg(stmt.ToCheckFact))
		}
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
		execState, err := exec.execProofBlock(stmt.Proofs)
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

func (exec *Executor) claimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) (glob.ExecState, error) {
	isSuccess := false

	exec.newEnv(exec.env, exec.env.CurMatchProp)
	defer func() {
		exec.appendMsg("\n")
		if isSuccess {
			exec.appendNewMsgAtBegin("is true\n")
		} else {
			exec.appendNewMsgAtBegin("is unknown\n")
		}
		exec.appendNewMsgAtBegin(stmt.Claim.String())
		exec.deleteEnvAndRetainMsg()
	}()

	if stmt.Claim.ToCheckFact == ast.ClaimStmtEmptyToCheck {
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction does not support empty check")
	}

	// Must be orStmt or specFactStmt
	specFactStmt, ok := stmt.Claim.ToCheckFact.(ast.OrStmt_SpecStmt)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction only support spec fact")
	}

	reversedFact := specFactStmt.ReverseIsTrue()

	for _, curFact := range reversedFact {
		err := exec.env.NewFact(&curFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	execState, err := exec.execProofBlock(stmt.Claim.Proofs)
	if notOkExec(execState, err) {
		return execState, err
	}

	lastStmtAsFact, ok := stmt.Claim.Proofs[len(stmt.Claim.Proofs)-1].(ast.OrStmt_SpecStmt)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction only support fact")
	}

	reversedLastFact := lastStmtAsFact.ReverseIsTrue()

	for _, curFact := range reversedLastFact {
		execState, err = exec.factStmt(&curFact)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) proveInEachCaseStmt(stmt *ast.ProveInEachCaseStmt) (glob.ExecState, error) {
	isSuccess := false
	defer func() {
		exec.appendMsg("\n")
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
		exec.appendMsg(fmt.Sprintf("%s is unknown", stmt.OrFact.String()))
		return execState, err
	}

	for i := range stmt.OrFact.Facts {
		execState, err := exec.execProofBlockForEachCase(i, stmt)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	isSuccess = true
	return glob.ExecState_True, nil
}

func (exec *Executor) execProofBlockForEachCase(index int, stmt *ast.ProveInEachCaseStmt) (glob.ExecState, error) {
	exec.newEnv(exec.env, exec.env.CurMatchProp)
	defer exec.deleteEnvAndRetainMsg()

	caseStmt := stmt.OrFact.Facts[index]

	err := exec.env.NewFact(&caseStmt)
	if err != nil {
		return glob.ExecState_Error, err
	}

	for _, proofStmt := range stmt.Proofs[index] {
		execState, err := exec.Stmt(proofStmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return execState, nil
		}
	}

	// verify thenFacts are true
	for _, thenFact := range stmt.ThenFacts {
		execState, err := exec.factStmt(thenFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return execState, nil
		}
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) knowExistPropStmt(stmt *ast.KnowExistPropStmt) (glob.ExecState, error) {
	defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))

	err := exec.defExistPropStmt(&stmt.ExistProp)
	if err != nil {
		return glob.ExecState_Error, err
	}

	thenFacts := []ast.FactStmt{stmt.ExistProp.ToSpecFact()}
	knownUniFact := ast.NewUniFact(stmt.ExistProp.DefBody.DefHeader.Params, stmt.ExistProp.DefBody.DefHeader.SetParams, stmt.ExistProp.DefBody.DomFacts, thenFacts)

	err = exec.env.NewFact(knownUniFact)
	if err != nil {
		return glob.ExecState_Error, err
	}

	exec.appendMsg(fmt.Sprintf("%s\nis true by definition", knownUniFact.String()))

	return glob.ExecState_True, nil
}

func (exec *Executor) knowPropStmt(stmt *ast.KnowPropStmt) error {
	defer exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))

	err := exec.defPropStmt(&stmt.Prop)
	if err != nil {
		return err
	}

	thenFacts := []ast.FactStmt{stmt.Prop.ToSpecFact()}
	knownUniFact := ast.NewUniFact(stmt.Prop.DefHeader.Params, stmt.Prop.DefHeader.SetParams, stmt.Prop.DomFacts, thenFacts)

	err = exec.env.NewFact(knownUniFact)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) importStmt(stmt *ast.ImportStmt) error {
	execSuccess := false
	originalMsgLen := exec.env.MsgLen()
	defer func() {
		exec.env.ClearMsgFromIndex(originalMsgLen)
		if !execSuccess {
			exec.appendMsg(fmt.Sprintf("Failed to execute import statement:\n%s\n", stmt.String()))
		} else {
			exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
		}
	}()

	// 需要连上现在所在的repo的名字
	codePath := filepath.Join(taskManager.TaskRepoName, stmt.Path)
	code, err := os.ReadFile(codePath)
	if err != nil {
		return err
	}

	if stmt.AsPkgName == "" {
		// read the file
		topStmtSlice, err := parser.ParseSourceCode(string(code))
		if err != nil {
			return err
		}
		for _, topStmt := range topStmtSlice {
			execState, err := exec.Stmt(topStmt)
			if err != nil {
				return err
			}
			if execState != glob.ExecState_True {
				break
			}
		}
		execSuccess = true
	} else {
		panic(glob.InternalWarningMsg("import with as pkg name is not supported"))
	}

	return nil
}

func (exec *Executor) proveStmt(stmt *ast.ProveStmt) (glob.ExecState, error) {
	// new env
	exec.newEnv(exec.env, exec.env.CurMatchProp)
	defer exec.deleteEnvAndRetainMsg()

	return exec.execProofBlock(stmt.Proof)
}

func (exec *Executor) claimStmtProveUniFact(stmt *ast.ClaimProveStmt) (bool, error) {
	asUnivFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt)
	if !ok {
		return false, fmt.Errorf("claim stmt prove uni fact only support uni fact")
	}

	// declare parameters in asUnivFact in the env
	objDefStmt := ast.NewDefObjStmt(asUnivFact.Params, asUnivFact.ParamSets, asUnivFact.DomFacts)
	err := exec.defObjStmt(objDefStmt, false)
	if err != nil {
		exec.appendMsg(fmt.Sprintf("Claim statement error: Failed to declare parameters in universal fact:\n%s\n", objDefStmt.String()))
		return false, err
	}

	// exec proof block
	execState, err := exec.execProofBlock(stmt.Proofs)
	if err != nil {
		exec.appendMsg(fmt.Sprintf("Claim statement error: Failed to execute proof block:\n%s\n", stmt.String()))
		return false, err
	}
	if execState != glob.ExecState_True {
		return false, nil
	}

	// TODO: 让claim能forall if
	// if asUnivFact.IffFacts == nil || len(asUnivFact.IffFacts) == 0 {
	for _, fact := range asUnivFact.ThenFacts {
		execState, err := exec.factStmt(fact)
		if err != nil {
			exec.appendMsg(fmt.Sprintf("Claim statement error: Failed to execute fact statement:\n%s\n", fact.String()))
			return false, err
		}
		if execState != glob.ExecState_True {
			return false, nil
		}
	}
	return true, nil

}
