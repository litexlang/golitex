package litex_verifier

import (
	ast "golitex/litex_ast"
)

func (ver *Verifier) ExistPropFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if state.isSpec() {
		return false, nil
	}

	if stmt.TypeEnum == ast.TrueExist {
		newFact := ast.NewSpecFactStmt(ast.TrueAtom, stmt.PropName, stmt.Params)

		ok, err := ver.SpecFact(newFact, state)
		if err != nil {
			return false, err
		}
		if ok {
			return ver.factDefer(stmt, state, true, nil, newFact.String())
		}
		return false, nil

	} else if stmt.TypeEnum == ast.FalseExist {
		// get the definition of the prop
		panic("not implemented")
	}

	return false, nil
}
