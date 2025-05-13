package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) ParamInParamSets(stmt *ast.DefHeader) ([]ast.SpecFactStmt, error) {
	ret := []ast.SpecFactStmt{}

	for i, param := range stmt.Params {
		paramAsAtom := ast.NewFcAtom(exec.curPkg, param, nil)
		specFact := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{paramAsAtom, stmt.SetParams[i]})
		ret = append(ret, *specFact)
	}

	return ret, nil
}
