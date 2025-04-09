package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	mem "golitex/litex_memory"
)

func (ver *Verifier) useStoredUniFactToVerifySpecFact(knownFact *mem.StoredUniSpecFact, uniConMap map[string]ast.Fc, state VerState) (bool, error) {
	// 这里貌似不需要对整个uniFact实例化，只要实例化then
	insKnownUniFact, err := knownFact.UniFact.Instantiate(uniConMap)
	if err != nil {
		return false, err
	}
	insKnownUniFactAsUniFact, ok := insKnownUniFact.(*ast.ConUniFactStmt)
	if !ok {
		return false, fmt.Errorf("")
	}

	ok, err = ver.insUniFactCond(insKnownUniFactAsUniFact, state)
	if err != nil {
		return false, err
	}

	return ok, nil
}

func (ver *Verifier) insUniFactCond(insUniFact *ast.ConUniFactStmt, state VerState) (bool, error) {
	// TODO 检查是否在对应的集合里

	nextState := state.addRound()
	for _, fact := range insUniFact.DomFacts {
		ok, err := ver.FactStmt(fact, nextState)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
