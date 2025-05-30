package litex_verifier

import ast "golitex/ast"

func (ver *Verifier) verOrStmt(stmt *ast.OrStmt, state VerState) (bool, error) {
	nextState := state.addRound()
	for i := range stmt.Facts {
		ok, err := ver.verFactAtIndex_WhenOthersAreFalse(stmt.Facts, i, nextState)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) verFactAtIndex_WhenOthersAreFalse(facts []ast.SpecFactStmt, i int, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchEnv)
	defer ver.deleteEnvAndRetainMsg()

	for j := range facts {
		if j == i {
			continue
		}
		err := ver.env.NewFact(facts[j].ReverseTrue())
		if err != nil {
			return false, err
		}
	}

	ok, err := ver.FactStmt(&facts[i], state)
	if err != nil {
		return false, err
	}
	return ok, nil
}
