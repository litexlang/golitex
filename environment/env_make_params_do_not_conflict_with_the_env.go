package litex_env

import (
	ast "golitex/ast"
)

func (env *Env) MakeUniFactParamsInThisDefPropDoNotConflictWithEnv(defPropStmt *ast.DefPropStmt) *ast.DefPropStmt {
	newDomFacts := []ast.FactStmt{}
	for _, domFact := range defPropStmt.DomFacts {
		newDomFacts = append(newDomFacts, env.makeUniFactParamsInThisFactDoNotConflictWithEnv(domFact))
	}

	newIffFacts := []ast.FactStmt{}
	for _, iffFact := range defPropStmt.IffFacts {
		newIffFacts = append(newIffFacts, env.makeUniFactParamsInThisFactDoNotConflictWithEnv(iffFact))
	}

	newThenFacts := []ast.FactStmt{}
	for _, thenFact := range defPropStmt.ThenFacts {
		newThenFacts = append(newThenFacts, env.makeUniFactParamsInThisFactDoNotConflictWithEnv(thenFact))
	}

	return ast.NewDefPropStmt(defPropStmt.DefHeader, newDomFacts, newIffFacts, newThenFacts, defPropStmt.Line)
}

func (env *Env) makeUniFactParamsInThisFactDoNotConflictWithEnv(fact ast.FactStmt) ast.FactStmt {
	switch asFact := fact.(type) {
	case *ast.UniFactStmt:
		return env.makeUniFactParamsInThisUniFactDoNotConflictWithEnv(asFact)
	case *ast.UniFactWithIffStmt:
		return env.makeUniFactParamsInThisUniFactDoNotConflictWithEnv(asFact.UniFact)
	default:
		return fact
	}
}

func (env *Env) makeUniFactParamsInThisUniFactDoNotConflictWithEnv(uniFact *ast.UniFactStmt) ast.FactStmt {
	conflictingParams := map[string]struct{}{}
	for _, param := range uniFact.Params {
		if env.IsAtomDeclared(ast.FcAtom(param), map[string]struct{}{}) {
			conflictingParams[param] = struct{}{}
		}
	}

	if len(conflictingParams) == 0 {
		return uniFact
	}

	// get non conflicting params
	newParams := []string{}
	newParamsMap := map[string]struct{}{}
	for _, param := range uniFact.Params {
		if _, ok := conflictingParams[param]; !ok {
			newParams = append(newParams, param)
			newParamsMap[param] = struct{}{}
		}
		newParam := env.GenerateUndeclaredRandomName_AndNotInMap(newParamsMap)
		newParams = append(newParams, newParam)
		newParamsMap[newParam] = struct{}{}
	}

	// replace params of facts of this uniFact with new params

	return ast.NewUniFact(newParams, uniFact.ParamSets, uniFact.DomFacts, uniFact.ThenFacts, uniFact.Line)
}
