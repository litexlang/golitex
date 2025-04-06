package litexexecutor

import (
	"fmt"
	glob "golitex/litex_global"
	parser "golitex/litex_parser"
	verifier "golitex/litex_verifier"
	"strings"
)

func (exec *Executor) TopLevelStmt(stmt *parser.TopStmt) error {
	exec.clearMsgAndOutput()
	return exec.stmt(stmt.Stmt)
}

// 在子函数里管理msg，即比如现在是TypeStmt，那在处理TypeStmt的地方处理它的string，二不是在这里
func (exec *Executor) stmt(stmt parser.Stmt) error {
	var err error = nil

	switch stmt := (stmt).(type) {
	case parser.FactStmt:
		err = exec.factStmt(stmt)
	case *parser.KnowStmt:
		err = exec.knowStmt(stmt)
	case *parser.ClaimProveStmt:
		err = exec.claimProveStmt(stmt)
	case *parser.DefConPropStmt:
		err = exec.defConPropStmt(stmt)
	case *parser.DefObjStmt:
		err = exec.defObjStmt(stmt)
	case *parser.DefConFnStmt:
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

func (exec *Executor) knowStmt(stmt *parser.KnowStmt) error {
	for _, fact := range stmt.Facts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	exec.appendNewMsg(stmt.String())
	return nil
}

func (exec *Executor) factStmt(stmt parser.FactStmt) error {
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

func (exec *Executor) checkFactStmt(stmt parser.FactStmt) (bool, *verifier.Verifier, error) {
	curVerifier := verifier.NewVerifier(exec.env, exec.env.CurPkg)
	ok, err := curVerifier.FactStmt(stmt, verifier.AnyMsg)
	if err != nil {
		return false, curVerifier, err
	}
	return ok, curVerifier, err
}

func (exec *Executor) claimProveStmt(stmt *parser.ClaimProveStmt) error {
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

func (exec *Executor) defConPropStmt(stmt *parser.DefConPropStmt) error {
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefConProp(stmt, exec.env.CurPkg)
	if err != nil {
		return err
	}

	// new uni fact
	// TODO 这里因为我是用 ptr 来实现某个interface的，所以这里非常愚蠢地需要重新变化一下
	uniFactParamTypes := []parser.Fc{}
	for _, tp := range stmt.DefHeader.TypeParams {
		uniFactParamTypes = append(uniFactParamTypes, tp)
	}

	iffLeadToPropUniFactDomFacts := []parser.FactStmt{}
	iffLeadToPropUniFactDomFacts = append(iffLeadToPropUniFactDomFacts, stmt.DomFacts...)

	iffFacts := []*parser.SpecFactStmt{}
	for _, fact := range stmt.IffFacts {
		iffLeadToPropUniFactDomFacts = append(iffLeadToPropUniFactDomFacts, fact)
		iffFacts = append(iffFacts, fact)
	}

	specFactParams := []parser.Fc{}
	for _, param := range stmt.DefHeader.Params {
		specFactParams = append(specFactParams, &parser.FcAtom{PkgName: "", Value: param})
	}

	propAsSpecFact := parser.SpecFactStmt{IsTrue: true, PropName: parser.FcAtom{PkgName: "", Value: stmt.DefHeader.Name}, Params: specFactParams}

	IffLeadToProp := parser.UniFactStmt{Params: stmt.DefHeader.Params, ParamTypes: uniFactParamTypes, DomFacts: iffLeadToPropUniFactDomFacts, ThenFacts: []*parser.SpecFactStmt{&propAsSpecFact}}

	err = exec.env.NewFact(&IffLeadToProp)
	if err != nil {
		return err
	}

	domFacts := append(stmt.DomFacts, &propAsSpecFact)

	PropLeadToIff := parser.UniFactStmt{Params: stmt.DefHeader.Params, ParamTypes: uniFactParamTypes, DomFacts: domFacts, ThenFacts: iffFacts}

	err = exec.env.NewFact(&PropLeadToIff)
	if err != nil {
		return err
	}

	return nil
}

func (exec *Executor) defObjStmt(stmt *parser.DefObjStmt) error {
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefObj(stmt, exec.env.CurPkg)
	if err != nil {
		return err
	}

	for i, objName := range stmt.Objs {
		objInSetFact := parser.SpecFactStmt{
			IsTrue: true,
			PropName: parser.FcAtom{
				PkgName: "",
				Value:   glob.KeywordIn,
			},
			Params: []parser.Fc{&parser.FcAtom{PkgName: exec.env.CurPkg, Value: objName}, stmt.ObjSets[i]},
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

func (exec *Executor) defConFnStmt(stmt *parser.DefConFnStmt) error {
	defer exec.appendNewMsg(stmt.String())
	err := exec.env.NewDefFn(stmt, exec.env.CurPkg)
	if err != nil {
		return err
	}

	fcFnParams := []parser.Fc{}
	for _, fc := range stmt.DefHeader.Params {
		fcFnParams = append(fcFnParams, &parser.FcAtom{PkgName: "", Value: fc})
	}

	fcFn := parser.FcFnPipe{FnHead: parser.FcAtom{PkgName: exec.env.CurPkg, Value: stmt.DefHeader.Name}, CallPipe: []*parser.FcFnPipeSeg{{Params: fcFnParams}}}

	retFact := parser.SpecFactStmt{IsTrue: true, PropName: parser.FcAtom{PkgName: "", Value: glob.KeywordIn}, Params: []parser.Fc{&fcFn}}

	uniFactThen := []*parser.SpecFactStmt{&retFact}
	uniFactThen = append(uniFactThen, stmt.ThenFacts...)

	uniFact := parser.UniFactStmt{Params: stmt.DefHeader.Params, ParamTypes: stmt.DefHeader.TypeParams, DomFacts: stmt.DomFacts, ThenFacts: uniFactThen}
	err = exec.env.NewFact(&uniFact)

	if err != nil {
		return err
	}

	return nil
}
