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

	exec.newMsgEnd(stmt.String())
	return nil
}

func (exec *Executor) factStmt(stmt parser.FactStmt) error {
	ok, _, err := exec.checkFactStmt(stmt)

	if err != nil {
		return err
	}

	if !ok {
		exec.newMsgEnd(stmt.String() + "\nis unknown")
	} else {
		exec.env.NewFact(stmt)
	}

	return nil
}

func (exec *Executor) checkFactStmt(stmt parser.FactStmt) (bool, *verifier.Verifier, error) {
	curVerifier := verifier.NewVerifier(exec.env)
	ok, err := curVerifier.FactStmt(stmt, verifier.AnyMsg)
	if err != nil {
		return false, curVerifier, err
	}
	return ok, curVerifier, err
}

func (exec *Executor) claimProveStmt(stmt *parser.ClaimProveStmt) error {
	exec.newEnv()                 // 在子环境中做所有操作，不影响外部世界
	exec.newMsgEnd(stmt.String()) // 在子函数里管理string

	defer exec.deleteEnvAndRetainMsg()

	for _, curStmt := range stmt.Proofs {
		err := exec.stmt(curStmt)
		if err != nil {
			return err
		}
	}

	// TODO 检查claim，并确保claim里的变量都是全局变量。确保了之后，在子环境里检查它后，如果确定对了，那就把这些这些claim释放到大环境里

	// localMsgs := exec.getMsgs()
	// exec.newMsgAtParent(stmt.String() + "\n" + strings.Join(localMsgs, "\n\n"))

	return nil
}

func (exec *Executor) GetMsgAsStr0ToEnd() string {
	return strings.Join(exec.env.Msgs, "\n")
}

func (exec *Executor) newMsgAtParent(s string) error {
	if exec.env.Parent == nil {
		return fmt.Errorf("no parent env")
	} else {
		exec.env.Parent.NewMsg(s)
		return nil
	}
}

func (exec *Executor) defConPropStmt(stmt *parser.DefConPropStmt) error {
	err := exec.env.NewDefConProp(stmt, "")
	if err != nil {
		return err
	}
	exec.newMsgEnd(stmt.String())

	// new uni fact
	// TODO 这里因为我是用 ptr 来实现某个interface的，所以这里非常愚蠢地需要重新变化一下
	uniFactParamTypes := []parser.Fc{}
	for _, tp := range stmt.DefHeader.TypeParams {
		uniFactParamTypes = append(uniFactParamTypes, &tp)
	}

	uniFactDomFacts := []parser.FactStmt{}
	uniFactDomFacts = append(uniFactDomFacts, stmt.DomFacts...)

	iffFacts := []parser.SpecFactStmt{}
	for _, fact := range stmt.IffFacts {
		uniFactDomFacts = append(uniFactDomFacts, &fact)
		iffFacts = append(iffFacts, fact)
	}

	specFactParams := []parser.Fc{}
	for _, param := range stmt.DefHeader.Params {
		specFactParams = append(specFactParams, &parser.FcAtom{PkgName: "", Value: param})
	}

	propAsSpecFact := parser.SpecFactStmt{IsTrue: true, PropName: parser.FcAtom{PkgName: "", Value: stmt.DefHeader.Name}, Params: specFactParams}

	IffLeadToProp := parser.UniFactStmt{Params: stmt.DefHeader.Params, ParamTypes: uniFactParamTypes, DomFacts: uniFactDomFacts, ThenFacts: []parser.SpecFactStmt{propAsSpecFact}}

	err = exec.env.NewFact(&IffLeadToProp)
	if err != nil {
		return err
	}

	// TODO 从 prop 到 dom和iff
	PropLeadToIff := parser.UniFactStmt{Params: stmt.DefHeader.Params, ParamTypes: uniFactParamTypes, DomFacts: append(uniFactDomFacts, &propAsSpecFact), ThenFacts: iffFacts}

	exec.env.NewFact(&PropLeadToIff)
	if err != nil {
		return err
	}

	return nil
}
