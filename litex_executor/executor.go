package litexexecutor

import (
	"fmt"
	glob "golitex/litex_global"
	st "golitex/litex_statements"
	verifier "golitex/litex_verifier"
	"strings"
)

func (exec *Executor) TopLevelStmt(stmt *st.TopStmt) error {
	exec.clearMsgAndOutput()
	return exec.stmt(stmt.Stmt)
}

// 在子函数里管理msg，即比如现在是TypeStmt，那在处理TypeStmt的地方处理它的string，二不是在这里
func (exec *Executor) stmt(stmt st.Stmt) error {
	var err error = nil

	switch stmt := (stmt).(type) {
	case st.FactStmt:
		err = exec.factStmt(stmt)
	case *st.KnowStmt:
		err = exec.knowStmt(stmt)
	case *st.ClaimProveStmt:
		err = exec.claimProveStmt(stmt)
	case *st.DefConPropStmt:
		err = exec.defConPropStmt(stmt)
	case *st.DefObjStmt:
		err = exec.defObjStmt(stmt)
	case *st.DefConFnStmt:
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

func (exec *Executor) knowStmt(stmt *st.KnowStmt) error {
	for _, fact := range stmt.Facts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	exec.appendNewMsg(stmt.String())
	return nil
}

func (exec *Executor) factStmt(stmt st.FactStmt) error {
	ok, _, err := exec.checkFactStmt(stmt)

	if err != nil {
		return err
	}

	if !ok {
		exec.appendNewMsg(stmt.String() + "\nis unknown")
	} else {
		exec.env.NewFact(stmt)
	}

	return nil
}

func (exec *Executor) checkFactStmt(stmt st.FactStmt) (bool, *verifier.Verifier, error) {
	curVerifier := verifier.NewVerifier(exec.env, exec.env.CurPkg)
	ok, err := curVerifier.FactStmt(stmt, verifier.AnyMsg)
	if err != nil {
		return false, curVerifier, err
	}
	return ok, curVerifier, err
}

func (exec *Executor) claimProveStmt(stmt *st.ClaimProveStmt) error {
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

func (exec *Executor) defConPropStmt(stmt *st.DefConPropStmt) error {
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefConProp(stmt, exec.env.CurPkg)
	if err != nil {
		return err
	}

	// new uni fact
	// TODO 这里因为我是用 ptr 来实现某个interface的，所以这里非常愚蠢地需要重新变化一下
	uniFactParamTypes := []st.Fc{}
	for _, tp := range stmt.DefHeader.TypeParams {
		uniFactParamTypes = append(uniFactParamTypes, tp)
	}

	iffLeadToPropUniFactDomFacts := []st.FactStmt{}
	iffLeadToPropUniFactDomFacts = append(iffLeadToPropUniFactDomFacts, stmt.DomFacts...)

	iffFacts := []*st.SpecFactStmt{}
	for _, fact := range stmt.IffFacts {
		iffLeadToPropUniFactDomFacts = append(iffLeadToPropUniFactDomFacts, fact)
		iffFacts = append(iffFacts, fact)
	}

	specFactParams := []st.Fc{}
	for _, param := range stmt.DefHeader.Params {
		specFactParams = append(specFactParams, &st.FcAtom{PkgName: "", Value: param})
	}

	propAsSpecFact := st.SpecFactStmt{IsTrue: true, PropName: st.FcAtom{PkgName: "", Value: stmt.DefHeader.Name}, Params: specFactParams}

	IffLeadToProp := st.UniFactStmt{Params: stmt.DefHeader.Params, ParamTypes: uniFactParamTypes, DomFacts: iffLeadToPropUniFactDomFacts, ThenFacts: []*st.SpecFactStmt{&propAsSpecFact}}

	err = exec.env.NewFact(&IffLeadToProp)
	if err != nil {
		return err
	}

	domFacts := append(stmt.DomFacts, &propAsSpecFact)

	PropLeadToIff := st.UniFactStmt{Params: stmt.DefHeader.Params, ParamTypes: uniFactParamTypes, DomFacts: domFacts, ThenFacts: iffFacts}

	err = exec.env.NewFact(&PropLeadToIff)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) defObjStmt(stmt *st.DefObjStmt) error {
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefObj(stmt, exec.env.CurPkg)
	if err != nil {
		return err
	}

	for i, objName := range stmt.Objs {
		objInSetFact := st.SpecFactStmt{
			IsTrue: true,
			PropName: st.FcAtom{
				PkgName: "",
				Value:   glob.KeywordIn,
			},
			Params: []st.Fc{&st.FcAtom{PkgName: exec.env.CurPkg, Value: objName}, stmt.ObjSets[i]},
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

func (exec *Executor) defConFnStmt(stmt *st.DefConFnStmt) error {
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefFn(stmt, exec.env.CurPkg)
	if err != nil {
		return err
	}

	fcFnParams := []st.Fc{}
	for _, fc := range stmt.DefHeader.Params {
		fcFnParams = append(fcFnParams, &st.FcAtom{PkgName: "", Value: fc})
	}

	fcFn := st.FcFnPipe{FnHead: st.FcAtom{PkgName: exec.env.CurPkg, Value: stmt.DefHeader.Name}, CallPipe: []*st.FcFnPipeSeg{{Params: fcFnParams}}}

	retFact := st.SpecFactStmt{IsTrue: true, PropName: st.FcAtom{PkgName: "", Value: glob.KeywordIn}, Params: []st.Fc{&fcFn, stmt.RetType}}

	uniFactThen := []*st.SpecFactStmt{&retFact}
	uniFactThen = append(uniFactThen, stmt.ThenFacts...)

	uniFactDom := []st.SpecFactStmt{}
	for i, paramSet := range stmt.DefHeader.TypeParams {
		objInSetFact := st.SpecFactStmt{
			IsTrue: true,
			PropName: st.FcAtom{
				PkgName: "",
				Value:   glob.KeywordIn,
			},
			Params: []st.Fc{&st.FcAtom{PkgName: exec.env.CurPkg, Value: stmt.DefHeader.Params[i]}, paramSet},
		}
		uniFactDom = append(uniFactDom, objInSetFact)
	}

	uniFact := st.UniFactStmt{Params: stmt.DefHeader.Params, ParamTypes: stmt.DefHeader.TypeParams, DomFacts: stmt.DomFacts, ThenFacts: uniFactThen}
	err = exec.env.NewFact(&uniFact)

	if err != nil {
		return err
	}

	return nil
}
