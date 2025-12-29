package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) GivenExistParamsAndSpecFactMatchRightInstExistStFact(freeExistParams []string, freeSpecFact *ast.SpecFactStmt, right *ast.SpecFactStmt) *glob.ShortRet {
	rightExistParams, rightParams := right.ExistStFactToPropNameExistParamsParams()

	if len(freeExistParams) != len(rightExistParams) || len(freeSpecFact.Params) != len(rightParams) {
		return glob.NewShortUnknownRet()
	}

	panic("")
}
