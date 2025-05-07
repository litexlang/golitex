// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_executor

import (
	"fmt"
	ast "golitex/litex_ast"
	env "golitex/litex_env"
	glob "golitex/litex_global"
	"strings"
)

// 在子函数里管理msg，即比如现在是TypeStmt，那在处理TypeStmt的地方处理它的string，二不是在这里
func (exec *Executor) stmt(stmt ast.Stmt) (glob.ExecState, error) {
	var err error = nil
	var execState glob.ExecState = glob.ExecState_True

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		execState, err = exec.factStmt(stmt)
	case *ast.KnowStmt:
		err = exec.knowStmt(stmt)
	case *ast.ClaimStmt:
		execState, err = exec.claimStmt(stmt)
	case *ast.DefConPropStmt:
		err = exec.defConPropStmt(stmt)
	case *ast.DefObjStmt:
		err = exec.defObjStmt(stmt)
	case *ast.ExistObjDefStmt:
		err = exec.existObjDefStmt(stmt)
	case *ast.DefConExistPropStmt:
		err = exec.defConExistPropStmt(stmt)
	case *ast.DefConFnStmt:
		err = exec.defConFnStmt(stmt)
	case *ast.MatcherEnvStmt:
		err = exec.matcherEnvStmt(stmt)
	case *ast.AxiomStmt:
		err = exec.axiomStmt(stmt)
	case ast.SetDefStmt:
		err = exec.setDefStmt(stmt)
	// case *ast.ThmStmt:
	// 	err = exec.thmStmt(stmt)

	default:
		err = fmt.Errorf("unknown statement type: %T", stmt)
	}

	if err != nil {
		return glob.ExecState_Error, glob.NewErrLink(err, "%s\nexecution error", stmt.String())
	} else {
		return execState, nil
	}
}

func (exec *Executor) TopLevelStmt(stmt *ast.TopStmt) (glob.ExecState, error) {
	exec.clearMsgAndOutput()
	return exec.stmt(stmt.Stmt)
}

func (exec *Executor) knowStmt(stmt *ast.KnowStmt) error {
	defer exec.appendNewMsg("\n")

	for _, fact := range stmt.Facts {
		err := exec.env.NewFactWithOutEmit(fact)
		if err != nil {
			return err
		}
		if stmtAsSpecFact, ok := fact.(*ast.SpecFactStmt); ok {
			err = exec.env.NewEmitWhenSpecFactIsTrue(stmtAsSpecFact)
			if err != nil {
				return err
			}
		}
	}

	exec.appendNewMsg(stmt.String())
	return nil
}

func (exec *Executor) claimStmt(stmt *ast.ClaimStmt) (glob.ExecState, error) {
	// TODO: 这里需要优化，因为claim和prove的逻辑是一样的，所以可以合并
	isSuccess := false
	var err error = nil

	if stmt.IsProve {
		isSuccess, err = exec.claimStmtProve(stmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
	} else {
		isSuccess, err = exec.claimStmtProveByContradiction(stmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// store
	if !isSuccess {
		return glob.ExecState_Unknown, nil
	}

	if asSpecFact, ok := stmt.ToCheckFact.(*ast.SpecFactStmt); ok {
		if stmt.ClaimName != ast.EmptyClaimName {
			return glob.ExecState_Error, fmt.Errorf("specific fact in claim should not have claim name, get %s", stmt.ClaimName)
		}

		err = exec.env.Parent.NewFactWithOutEmit(asSpecFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	} else if asConUniFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt); ok {
		newUniFact, err := ast.AddUniPrefixToUniFact(asConUniFact)
		if err != nil {
			return glob.ExecState_Error, err
		}

		err = exec.env.Parent.NewFactWithOutEmit(newUniFact)
		if err != nil {
			return glob.ExecState_Error, err
		}

		if stmt.ClaimName != ast.EmptyClaimName {
			err = exec.execNamedForall(stmt.ClaimName, asConUniFact, exec.env.Parent)
			if err != nil {
				return glob.ExecState_Error, err
			}
		}
	}
	return glob.ExecState_True, nil
}

func (exec *Executor) execNamedForall(propName string, asConUniFact *ast.UniFactStmt, storeToEnv *env.Env) error {
	// make a uniFact to a propDef. with empty dom, and uniFactThen as iff
	defHeader := ast.ConDefHeader{
		Name:      propName,
		Params:    asConUniFact.Params,
		SetParams: asConUniFact.ParamSets,
	}
	domFacts := []ast.FactStmt{}
	iffFacts := asConUniFact.DomFacts // Notice here is thenFacts, not iffFacts

	propDef := ast.NewDefConPropStmt(defHeader, domFacts, iffFacts)

	err := storeToEnv.NewDefConProp(propDef)
	if err != nil {
		return err
	}

	// make a emitWhenSpecFactIsTrue
	propSpecFact := propDef.ToSpecFact()

	// 本质上只有 thenFact 是被后面用到的
	uniPropImplyClaimThen := ast.NewUniFactStmtWithSetReqInDom(asConUniFact.Params, asConUniFact.ParamSets, []ast.FactStmt{propSpecFact}, asConUniFact.ThenFacts, ast.EmptyIffFacts)

	err = storeToEnv.NewFactWithOutEmit(uniPropImplyClaimThen)
	if err != nil {
		return err
	}

	err = storeToEnv.EmitWhenSpecFactIsTrueMem.Insert(exec.curPkg, propSpecFact.PropName.Name, uniPropImplyClaimThen)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) GetMsgAsStr0ToEnd() string {
	return strings.Join(exec.env.Msgs, "\n")
}

func (exec *Executor) defConPropStmt(stmt *ast.DefConPropStmt) error {
	defer exec.appendNewMsg("\n")

	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendNewMsg(stmt.String())

	// iff leads to prop
	err := exec.env.NewDefConProp(stmt)
	if err != nil {
		return err
	}

	// prop leads to iff
	uniFactParams := stmt.DefHeader.Params
	uniFactParamSets := stmt.DefHeader.SetParams
	domFacts := []ast.FactStmt{}
	domFacts = append(domFacts, stmt.DomFacts...)
	propAsSpec := stmt.ToSpecFact()
	domFacts = append(domFacts, propAsSpec)

	newUniFact := ast.NewUniFactStmtWithSetReqInDom(uniFactParams, uniFactParamSets, domFacts, stmt.IffFacts, ast.EmptyIffFacts)

	err = exec.env.NewFactWithOutEmit(newUniFact)

	exec.appendNewMsg(fmt.Sprintf("know by prop definition:\n%s", newUniFact.String()))

	if err != nil {
		return err
	}

	if len(stmt.IffFacts) == 0 {
		return nil
	}

	return nil
}

func (exec *Executor) defObjStmt(stmt *ast.DefObjStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendNewMsg(fmt.Sprintf("%s\n", stmt.String()))
	err := exec.env.NewDefObj(stmt)
	if err != nil {
		return err
	}

	for i, objName := range stmt.Objs {
		objInSetFact := ast.SpecFactStmt{
			TypeEnum: ast.TrueAtom,
			PropName: ast.FcAtom{
				PkgName: "",
				Name:    glob.KeywordIn,
			},
			Params: []ast.Fc{&ast.FcAtom{PkgName: glob.BuiltinEmptyPkgName, Name: objName}, stmt.ObjSets[i]},
		}
		err := exec.env.NewFactWithOutEmit(&objInSetFact)
		if err != nil {
			return err
		}
	}

	for _, fact := range stmt.Facts {
		err := exec.env.NewFactWithOutEmit(fact)
		if err != nil {
			return err
		}
	}

	return nil
}

func (exec *Executor) defConFnStmt(stmt *ast.DefConFnStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendNewMsg("\n")
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefFn(stmt)
	if err != nil {
		return err
	}

	fcFnParams := []ast.Fc{}
	for _, fc := range stmt.DefHeader.Params {
		fcFnParams = append(fcFnParams, &ast.FcAtom{PkgName: "", Name: fc})
	}

	fcFn := ast.FcFn{FnHead: &ast.FcAtom{PkgName: glob.BuiltinEmptyPkgName, Name: stmt.DefHeader.Name}, ParamSegs: [][]ast.Fc{fcFnParams}}

	retFact := ast.SpecFactStmt{TypeEnum: ast.TrueAtom, PropName: ast.FcAtom{PkgName: "", Name: glob.KeywordIn}, Params: []ast.Fc{&fcFn, stmt.RetSet}}

	uniFactThen := []ast.FactStmt{&retFact}
	uniFactThen = append(uniFactThen, stmt.ThenFacts...)

	thenFacts := []ast.FactStmt{}
	thenFacts = append(thenFacts, uniFactThen...)

	uniFact := ast.UniFactStmt{Params: stmt.DefHeader.Params, ParamSets: stmt.DefHeader.SetParams, DomFacts: stmt.DomFacts, ThenFacts: thenFacts}
	err = exec.env.NewFactWithOutEmit(&uniFact)

	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) defConExistPropStmt(stmt *ast.DefConExistPropStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendNewMsg("\n")
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefConExistProp(stmt)
	if err != nil {
		return err
	}
	return nil
}

func (exec *Executor) existObjDefStmt(stmt *ast.ExistObjDefStmt) error {
	defer exec.appendNewMsg("\n")
	defer exec.appendNewMsg(stmt.String())

	existFact := ast.SpecFactStmt{TypeEnum: ast.TrueExist, PropName: ast.FcAtom{PkgName: "", Name: stmt.Fact.PropName.Name}, Params: stmt.Fact.Params}

	ok, _, err := exec.checkFactStmt(&existFact)
	if err != nil {
		return err
	}

	if !ok {
		exec.appendNewMsg("%v failed: related exist fact check failed\n", existFact.String())
		return nil
	}

	// TODO 需要像defObjStmt那样，把objName和objSet都插入到env里
	propDef, ok := exec.env.GetExistPropDef(stmt.Fact.PropName)
	if !ok {
		return fmt.Errorf("%s has no definition", stmt.String())
	}

	uniConMap := map[string]ast.Fc{}
	for i := 0; i < len(stmt.ObjNames); i++ {
		uniConMap[propDef.ExistParams[i]] = &ast.FcAtom{PkgName: exec.curPkg, Name: stmt.ObjNames[i]}
	}

	for i := 0; i < len(stmt.Fact.Params); i++ {
		uniConMap[propDef.Def.DefHeader.Params[i]] = stmt.Fact.Params[i]
	}

	facts := []ast.FactStmt{}
	for _, fact := range propDef.Def.DomFacts {
		fixed, err := fact.Instantiate(uniConMap)
		if err != nil {
			return err
		}
		facts = append(facts, fixed)
	}

	for _, fact := range propDef.Def.IffFacts {
		fixed, err := fact.Instantiate(uniConMap)
		if err != nil {
			return err
		}
		facts = append(facts, fixed)
	}

	newDefObjStmt := ast.DefObjStmt{Objs: stmt.ObjNames, ObjSets: stmt.Fact.Params, Facts: facts}

	err = exec.defObjStmt(&newDefObjStmt)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) defStmt(stmt ast.DefStmt) error {
	// TODO：这里需要处理任何可能出现的 Def,包括stmt是个DefObj, DefProp, DefConExistProp, DefConFn, DefConProp. 本函数用于 claim forall x Type. 这里的 Type 可以是 obj, fn, prop, existProp.
	// 本函数需要处理所有可能的类型，并根据类型调用不同的函数。

	switch stmt := stmt.(type) {
	case *ast.DefObjStmt:
		return exec.defObjStmt(stmt)
	case *ast.DefConFnStmt:
		return exec.defConFnStmt(stmt)
	case *ast.DefConPropStmt:
		return exec.defConPropStmt(stmt)
	case *ast.DefConExistPropStmt:
		return exec.defConExistPropStmt(stmt)
	default:
		return fmt.Errorf("unknown def stmt type: %T", stmt)
	}
}

func (exec *Executor) matcherEnvStmt(stmt *ast.MatcherEnvStmt) error {
	defer exec.appendNewMsg("\n")
	defer exec.appendNewMsg(stmt.String())

	for _, curStmt := range stmt.Body {
		execState, err := exec.stmt(curStmt)
		if err != nil {
			return err
		}
		if execState != glob.ExecState_True {
			return fmt.Errorf("matcher env stmt is not true")
		}
	}

	return nil
}

func (exec *Executor) GetUniFactSettings(asUnivFact *ast.UniFactStmt) error {
	for i, param := range asUnivFact.Params {
		exec.defStmt(&ast.DefObjStmt{Objs: []string{param}, ObjSets: []ast.Fc{asUnivFact.ParamSets[i]}, Facts: []ast.FactStmt{}})
	}
	for _, fact := range asUnivFact.DomFacts {
		err := exec.env.NewFactWithOutEmit(fact)
		if err != nil {
			return err
		}
	}

	return nil
}

func (exec *Executor) execProofBlock(proof []ast.Stmt) (glob.ExecState, error) {
	for _, curStmt := range proof {
		execState, err := exec.stmt(curStmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return glob.ExecState_Unknown, nil
		}
	}
	return glob.ExecState_True, nil
}

func (exec *Executor) claimStmtProve(stmt *ast.ClaimStmt) (bool, error) {
	exec.newEnv()
	isSuccess := false

	defer func() {
		exec.appendNewMsg("\n")
		if isSuccess {
			exec.appendNewMsgAtBegin("is true\n")
		} else {
			exec.appendNewMsgAtBegin("is unknown\n")
		}
		exec.appendNewMsgAtBegin(stmt.String())
		exec.deleteEnvAndRetainMsg()
	}()

	if asUnivFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt); ok {
		// 把变量引入，把dom事实引入
		err := exec.GetUniFactSettings(asUnivFact)
		if err != nil {
			return false, err
		}
	}

	execState, err := exec.execProofBlock(stmt.Proofs)
	if err != nil {
		return false, err
	}
	if execState != glob.ExecState_True {
		return false, nil
	}

	// 写成 prove: ... 这样的事实，是没有toCheckFact的，默认是nil
	if stmt.ToCheckFact == ast.ClaimStmtEmptyToCheck {
		isSuccess = true
		return true, nil
	}

	if asSpecFact, ok := stmt.ToCheckFact.(*ast.SpecFactStmt); ok {
		ok, _, err := exec.checkFactStmt(asSpecFact)
		if err != nil {
			return false, err
		}
		if ok {
			isSuccess = true
		}
		return ok, nil
	}

	// TODO: 需要处理forall的情况
	if asConUniFact, ok := stmt.ToCheckFact.(*ast.UniFactStmt); ok {
		for _, fact := range asConUniFact.ThenFacts {
			ok, _, err := exec.checkFactStmt(fact)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}
		isSuccess = true
		return true, nil
	}

	return false, fmt.Errorf("unknown claim stmt to check fact type: %T", stmt.ToCheckFact)
}

func (exec *Executor) claimStmtProveByContradiction(stmt *ast.ClaimStmt) (bool, error) {
	exec.newEnv()
	isSuccess := false

	defer func() {
		exec.appendNewMsg("\n")
		if isSuccess {
			exec.appendNewMsgAtBegin("is true\n")
		} else {
			exec.appendNewMsgAtBegin("is unknown\n")
		}
		exec.appendNewMsgAtBegin(stmt.String())
		exec.deleteEnvAndRetainMsg()
	}()

	if stmt.ToCheckFact == ast.ClaimStmtEmptyToCheck {
		return false, fmt.Errorf("prove by contradiction does not support empty check")
	}

	// Must be SpecFactStmt
	specFactStmt, ok := stmt.ToCheckFact.(*ast.SpecFactStmt)
	if !ok {
		return false, fmt.Errorf("prove by contradiction only support spec fact")
	}

	newClaimFact := specFactStmt.ReverseIsTrue()

	err := exec.env.NewFactWithOutEmit(newClaimFact)
	if err != nil {
		return false, err
	}

	for _, curStmt := range stmt.Proofs {
		execState, err := exec.stmt(curStmt)
		if err != nil {
			return false, err
		}
		if execState != glob.ExecState_True {
			return false, nil
		}
	}

	lastStmtAsFact, ok := stmt.Proofs[len(stmt.Proofs)-1].(*ast.SpecFactStmt)
	if !ok {
		return false, fmt.Errorf("prove by contradiction only support fact")
	}

	reverseLastFact := lastStmtAsFact.ReverseIsTrue()

	ok, _, err = exec.checkFactStmt(reverseLastFact)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (exec *Executor) axiomStmt(stmt *ast.AxiomStmt) error {
	defer exec.appendNewMsg("\n")
	defer exec.appendNewMsg(stmt.String())

	err := exec.execNamedForall(stmt.Name, &stmt.Fact, exec.env)
	if err != nil {
		return err
	}

	err = exec.env.NewFactWithOutEmit(&stmt.Fact)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) setDefStmt(stmt ast.SetDefStmt) error {
	defer exec.appendNewMsg("\n")
	defer exec.appendNewMsg(stmt.String())

	err := exec.env.SetMem.Insert(stmt, exec.curPkg)
	if err != nil {
		return err
	}
	return nil
}
