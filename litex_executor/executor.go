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

	if !ok {
		if glob.CheckFalse {
			switch stmt.(type) {
			case *ast.SpecFactStmt:
				newStmt := stmt.(*ast.SpecFactStmt).GetReverseFact()
				ok, _, err := exec.checkFactStmt(newStmt)
				if err != nil {
					return err
				}
				if ok {
					exec.appendNewMsg(stmt.String() + "\nis false")
				}
			case *ast.ConUniFactStmt:
				// TODO 这里需要考虑到fact的类型
			default:
				// TODO 这里需要考虑到fact的类型
			}
		}
		exec.appendNewMsg(stmt.String() + "\nis unknown")
	} else {
		exec.env.NewFact(stmt)
	}

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
	exec.appendNewMsg(stmt.String())

	defer exec.deleteEnvAndRetainMsg()

	for _, curStmt := range stmt.Proofs {
		err := exec.stmt(curStmt)
		if err != nil {
			return err
		}
	}

	// TODO 检查claim，并确保claim里的变量都是全局变量。确保了之后，在子环境里检查它后，如果确定对了，那就把这些这些claim释放到大环境里
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
		specFactParams = append(specFactParams, &ast.FcAtom{PkgName: "", Value: param})
	}

	propAsSpecFact := ast.SpecFactStmt{IsTrue: true, PropName: ast.FcAtom{PkgName: "", Value: stmt.DefHeader.Name}, Params: specFactParams}

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
			IsTrue: true,
			PropName: ast.FcAtom{
				PkgName: "",
				Value:   glob.KeywordIn,
			},
			Params: []ast.Fc{&ast.FcAtom{PkgName: exec.env.CurPkg, Value: objName}, stmt.ObjSets[i]},
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
		fcFnParams = append(fcFnParams, &ast.FcAtom{PkgName: "", Value: fc})
	}

	fcFn := ast.FcFn{FnHead: ast.FcAtom{PkgName: exec.env.CurPkg, Value: stmt.DefHeader.Name}, ParamSegs: []*ast.FcFnSeg{{Params: fcFnParams}}}

	retFact := ast.SpecFactStmt{IsTrue: true, PropName: ast.FcAtom{PkgName: "", Value: glob.KeywordIn}, Params: []ast.Fc{&fcFn, stmt.RetSet}}

	uniFactThen := []*ast.SpecFactStmt{&retFact}
	uniFactThen = append(uniFactThen, stmt.ThenFacts...)

	uniFact := ast.ConUniFactStmt{Params: stmt.DefHeader.Params, ParamSets: stmt.DefHeader.SetParams, DomFacts: stmt.DomFacts, ThenFacts: uniFactThen}
	err = exec.env.NewFact(&uniFact)

	if err != nil {
		return err
	}

	return nil
}
