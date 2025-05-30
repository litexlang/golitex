package litex_verifier

import ast "golitex/ast"

func (ver *Verifier) verOrStmt(stmt *ast.OrStmt, state VerState) (bool, error) {
	for i := range stmt.Facts {
		ok, err := ver.verFactWhenOthersAreFalse(stmt.Facts, i, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) verFactWhenOthersAreFalse(facts []ast.SpecFactStmt, i int, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchEnv)
	defer ver.deleteEnvAndRetainMsg()

	nextState := state.addRound()
	for j := range facts {
		if j == int(i) {
			continue
		}
		err := ver.env.NewFact(&facts[j].ReverseIsTrue()[0])
		if err != nil {
			return false, err
		}
	}

	ok, err := ver.FactStmt(&facts[i], nextState)
	if err != nil {
		return false, err
	}
	return ok, nil
}
