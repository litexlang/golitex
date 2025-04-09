package litex_verifier

import (
	ast "golitex/litex_ast"
	mem "golitex/litex_memory"
)

func (ver *Verifier) useStoredUniFactToVerifySpecFact(knownFact *mem.StoredUniSpecFact, uniParamConParamMap map[string]ast.Fc, state VerState) (bool, error) {
	// TODO
	return false, nil
}
