package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ie *InferenceEngine) equalSetFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("equal_set fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	derivedFacts := []string{}

	// Create a = b fact
	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := ie.Env.NewFact(equalFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, equalFact.String())

	// Collect any derived facts from the equality fact
	if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
		derivedFacts = append(derivedFacts, ret.GetMsgs()...)
	}

	if len(derivedFacts) > 0 {
		return glob.NewGlobTrueWithMsgs(derivedFacts)
	}
	return glob.NewGlobTrue("")
}
