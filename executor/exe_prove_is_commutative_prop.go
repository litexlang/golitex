package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	ver "golitex/verifier"
)

func (exe *Executor) proveIsCommutativeProp(stmt *ast.SpecFactStmt) (bool, error) {
	state := ver.Round0NoMsg

	propNameAsAtom, ok := stmt.Params[0].(ast.FcAtom)
	if !ok {
		return false, nil
	}

	if propNameAsAtom == glob.KeySymbolEqual {
		return true, nil
	}

	propDef, ok := exe.env.GetPropDef(propNameAsAtom)
	if !ok {
		return false, nil
	}

	if len(propDef.DefHeader.Params) != 2 {
		return false, nil
	}

	uniFactParams := propDef.DefHeader.Params
	domFacts := propDef.DomFacts
	ThenFact := propDef.ToSpecFact()
	IffFact, err := ThenFact.ReverseParameterOrder()
	if err != nil {
		return false, err
	}

	uniFact := ast.NewUniFactWithIff(ast.NewUniFact(uniFactParams, propDef.DefHeader.ParamSets, domFacts, []ast.FactStmt{ThenFact}, stmt.Line), []ast.FactStmt{IffFact}, stmt.Line)

	verifier := ver.NewVerifier(exe.env)

	ok, err = verifier.VerFactStmt(uniFact, state.GetNoMsg())
	if err != nil {
		return false, err
	}

	if ok {
		exe.newMsg(fmt.Sprintf("%s is a commutative prop.", stmt.String()))
	}

	return ok, nil
}
