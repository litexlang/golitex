package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) iterateKnownExistFactsAndMatchGivenFact(stmt *ast.SpecFactStmt, knownFacts []ast.SpecFactStmt, state *VerState) *glob.VerRet {
LoopOverFacts:
	for _, knownFact := range knownFacts {
		verRet := ver.MatchExistFact(stmt, &knownFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			continue LoopOverFacts
		}

		if state.WithMsg {
			return successVerString(stmt, &knownFact)
		}
		return glob.NewEmptyVerRetTrue()
	}

	return glob.NewEmptyVerRetUnknown()
}
