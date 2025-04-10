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

	ok, err = ver.instUniFactDomFacts(insKnownUniFactAsUniFact, state)
	if err != nil {
		return false, err
	}

	return ok, nil
}

func (ver *Verifier) instUniFactDomFacts(insUniFact *ast.ConUniFactStmt, state VerState) (bool, error) {
	nextState := state.addRound()

	ok, err := ver.instUniFactParamsInParamSets(insUniFact, nextState)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

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

func (ver *Verifier) instUniFactParamsInParamSets(insUniFact *ast.ConUniFactStmt, state VerState) (bool, error) {
	// TODO
	// TODO 检查是否在对应的集合里
	_, _ = insUniFact, state
	return true, nil
}
