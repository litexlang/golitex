// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_executor

import (
	"fmt"
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
	verifier "golitex/litex_verifier"
	"strings"
)

// 在子函数里管理msg，即比如现在是TypeStmt，那在处理TypeStmt的地方处理它的string，二不是在这里
func (exec *Executor) stmt(stmt ast.Stmt) error {
	var err error = nil
	defer exec.appendNewMsg("\n")

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		err = exec.factStmt(stmt)
	case *ast.KnowStmt:
		err = exec.knowStmt(stmt)
	case *ast.ClaimProveStmt:
		err = exec.claimProveStmt(stmt)
	case *ast.DefConPropStmt:
		err = exec.defConPropStmt(stmt)
	case *ast.DefObjStmt:
		err = exec.defObjStmt(stmt)
	case *ast.ExistObjDefStmt:
		err = exec.haveObjDefStmt(stmt)
	case *ast.DefConExistPropStmt:
		err = exec.defConExistPropStmt(stmt)
	case *ast.DefConFnStmt:
		err = exec.defConFnStmt(stmt)

	default:
		err = fmt.Errorf("unknown statement type: %T", stmt)
	}

	if err != nil {
		return glob.NewErrLink(err, "%s\nexecution error", stmt.String())
	} else {
		return nil
	}
}

func (exec *Executor) TopLevelStmt(stmt *ast.TopStmt) error {
	exec.clearMsgAndOutput()
	return exec.stmt(stmt.Stmt)
}

func (exec *Executor) knowStmt(stmt *ast.KnowStmt) error {
	for _, fact := range stmt.Facts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	exec.appendNewMsg(stmt.String())
	return nil
}

func (exec *Executor) factStmt(stmt ast.FactStmt) error {
	ok, _, err := exec.checkFactStmt(stmt)

	if err != nil {
		return err
	}

	if ok {
		return exec.env.NewFact(stmt)
	}

	if glob.CheckFalse {
		switch stmt := stmt.(type) {
		case *ast.SpecFactStmt:
			newStmt := stmt.ReverseIsTrue()
			ok, _, err := exec.checkFactStmt(newStmt)
			if err != nil {
				return err
			}
			if ok {
				exec.appendNewMsg(stmt.String() + "\nis false")
				return nil
			}
		case *ast.ConUniFactStmt:
			// TODO 这里需要考虑到fact的类型
		default:
			// TODO 这里需要考虑到fact的类型
		}
		exec.appendNewMsg(stmt.String() + "\nis unknown")
	}

	exec.appendNewMsg(stmt.String() + "\nis unknown")

	return nil
}

func (exec *Executor) checkFactStmt(stmt ast.FactStmt) (bool, *verifier.Verifier, error) {
	curVerifier := verifier.NewVerifier(exec.env, exec.env.CurPkg)
	ok, err := curVerifier.FactStmt(stmt, verifier.Round0Msg)
	if err != nil {
		return false, curVerifier, err
	}
	return ok, curVerifier, err
}

func (exec *Executor) claimProveStmt(stmt *ast.ClaimProveStmt) error {
	exec.newEnv(exec.env.CurPkg)
	isSuccess := false

	defer func() {
		exec.appendNewMsg("\n")
		if isSuccess {
			exec.appendNewMsgAtBegin("is true")
		} else {
			exec.appendNewMsgAtBegin("is unknown")
		}
		exec.appendNewMsgAtBegin(stmt.String())
		exec.deleteEnvAndRetainMsg()
	}()

	if stmt.IsProve {
		for _, curStmt := range stmt.Proofs {
			err := exec.stmt(curStmt)
			if err != nil {
				return err
			}
		}

		// TODO 检查claim，并确保claim里的变量都是全局变量。确保了之后，在子环境里检查它后，如果确定对了，那就把这些这些claim释放到大环境里。运行方式是，空转这些命题，如果空转出现错误了，比如某变量没定义，那就报错

		for _, fact := range stmt.ToCheckFacts {
			ok, _, err := exec.checkFactStmt(fact)
			if err != nil {
				return err
			}
			if !ok {
				exec.appendNewMsgAtBegin("%v prove failed", fact.String())
				return nil
			}
		}

		isSuccess = true
		// exec.appendNewMsg("%v success", glob.KeywordProve)
		return nil

	} else {
		if len(stmt.ToCheckFacts) != 1 {
			return fmt.Errorf("prove by contradiction only support one fact")
		}

		// Must be SpecFactStmt
		specFactStmt, ok := stmt.ToCheckFacts[0].(*ast.SpecFactStmt)
		if !ok {
			return fmt.Errorf("prove by contradiction only support spec fact")
		}

		newClaimFact := specFactStmt.ReverseIsTrue()

		err := exec.env.NewFact(newClaimFact)
		if err != nil {
			return err
		}

		for _, curStmt := range stmt.Proofs {
			err := exec.stmt(curStmt)
			if err != nil {
				return err
			}
		}

		lastStmtAsFact, ok := stmt.Proofs[len(stmt.Proofs)-1].(*ast.SpecFactStmt)
		if !ok {
			return fmt.Errorf("prove by contradiction only support fact")
		}

		reverseLastFact := lastStmtAsFact.ReverseIsTrue()

		ok, _, err = exec.checkFactStmt(reverseLastFact)
		if err != nil {
			return err
		}
		if ok {
			isSuccess = true
			// exec.appendNewMsg("%v success", glob.KeywordProveByContradiction)
			return nil
		}
	}

	return nil
}

func (exec *Executor) GetMsgAsStr0ToEnd() string {
	return strings.Join(exec.env.Msgs, "\n")
}

func (exec *Executor) defConPropStmt(stmt *ast.DefConPropStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefConProp(stmt, exec.env.CurPkg)
	if err != nil {
		return err
	}

	// new uni fact
	uniFactParamSets := []ast.Fc{}
	uniFactParamSets = append(uniFactParamSets, stmt.DefHeader.SetParams...)

	iffLeadToPropUniFactDomFacts := []ast.FactStmt{}
	iffLeadToPropUniFactDomFacts = append(iffLeadToPropUniFactDomFacts, stmt.DomFacts...)

	iffFacts := []*ast.SpecFactStmt{}
	for _, fact := range stmt.IffFacts {
		iffLeadToPropUniFactDomFacts = append(iffLeadToPropUniFactDomFacts, fact)
		iffFacts = append(iffFacts, fact)
	}

	specFactParams := []ast.Fc{}
	for _, param := range stmt.DefHeader.Params {
		specFactParams = append(specFactParams, &ast.FcAtom{PkgName: "", Name: param})
	}

	propAsSpecFact := ast.SpecFactStmt{TypeEnum: ast.TrueAtom, PropName: ast.FcAtom{PkgName: "", Name: stmt.DefHeader.Name}, Params: specFactParams}

	IffLeadToProp := ast.ConUniFactStmt{Params: stmt.DefHeader.Params, ParamSets: uniFactParamSets, DomFacts: iffLeadToPropUniFactDomFacts, ThenFacts: []*ast.SpecFactStmt{&propAsSpecFact}}

	err = exec.env.NewFact(&IffLeadToProp)
	if err != nil {
		return err
	}

	domFacts := append(stmt.DomFacts, &propAsSpecFact)

	PropLeadToIff := ast.ConUniFactStmt{Params: stmt.DefHeader.Params, ParamSets: uniFactParamSets, DomFacts: domFacts, ThenFacts: iffFacts}

	err = exec.env.NewFact(&PropLeadToIff)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) defObjStmt(stmt *ast.DefObjStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefObj(stmt, exec.env.CurPkg)
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
			Params: []ast.Fc{&ast.FcAtom{PkgName: exec.env.CurPkg, Name: objName}, stmt.ObjSets[i]},
		}
		err := exec.env.NewFact(&objInSetFact)
		if err != nil {
			return err
		}
	}

	for _, fact := range stmt.Facts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	return nil
}

func (exec *Executor) defConFnStmt(stmt *ast.DefConFnStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefFn(stmt, exec.env.CurPkg)
	if err != nil {
		return err
	}

	fcFnParams := []ast.Fc{}
	for _, fc := range stmt.DefHeader.Params {
		fcFnParams = append(fcFnParams, &ast.FcAtom{PkgName: "", Name: fc})
	}

	fcFn := ast.FcFn{FnHead: ast.FcAtom{PkgName: exec.env.CurPkg, Name: stmt.DefHeader.Name}, ParamSegs: [][]ast.Fc{fcFnParams}}

	retFact := ast.SpecFactStmt{TypeEnum: ast.TrueAtom, PropName: ast.FcAtom{PkgName: "", Name: glob.KeywordIn}, Params: []ast.Fc{&fcFn, stmt.RetSet}}

	uniFactThen := []*ast.SpecFactStmt{&retFact}
	uniFactThen = append(uniFactThen, stmt.ThenFacts...)

	uniFact := ast.ConUniFactStmt{Params: stmt.DefHeader.Params, ParamSets: stmt.DefHeader.SetParams, DomFacts: stmt.DomFacts, ThenFacts: uniFactThen}
	err = exec.env.NewFact(&uniFact)

	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) defConExistPropStmt(stmt *ast.DefConExistPropStmt) error {
	// TODO 像定义这样的经常被调用的 事实，应该和普通的事实分离开来，以便于调用吗?
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefConExistProp(stmt, exec.env.CurPkg)
	if err != nil {
		return err
	}
	return nil
}

func (exec *Executor) haveObjDefStmt(stmt *ast.ExistObjDefStmt) error {
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
		uniConMap[propDef.ExistParams[i]] = &ast.FcAtom{PkgName: exec.env.CurPkg, Name: stmt.ObjNames[i]}
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
