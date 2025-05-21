package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) supposePropMatchStmt(stmt *ast.SupposePropMatchStmt) (glob.ExecState, error) {
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	originalEnv := exec.env
	originalEnv.CurMatchEnv = stmt // 之所以这么干，是因为要把stmt下面的事实存到originalEnv里，而且要存到 matchEnv 里
	defer func() {
		originalEnv.CurMatchEnv = nil
	}()

	exec.newEnv(originalEnv, stmt)
	defer exec.deleteEnvAndRetainMsg()

	factSpecDef, ok := exec.env.GetPropDef(stmt.Fact.PropName)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("spec fact parameter must be atom, but got: %s", stmt.Fact.PropName.String())
	}

	if len(factSpecDef.DefHeader.Params) != len(stmt.Fact.Params) {
		return glob.ExecState_Error, fmt.Errorf("spec fact parameter number not equal to prop def params number. expect %d, but got %d", len(factSpecDef.DefHeader.Params), len(stmt.Fact.Params))
	}

	for _, param := range stmt.Fact.Params {
		asAtom, ok := param.(*ast.FcAtom)
		if !ok {
			return glob.ExecState_Error, fmt.Errorf("spec fact parameter must be atom, but got: %s", param.String())
		}
		if asAtom.PkgName != glob.EmptyPkg {
			return glob.ExecState_Error, fmt.Errorf("spec fact parameter must be atom, but got: %s", param.String())
		}
		err := exec.env.ObjDefMem.Insert(ast.NewDefObjStmt([]string{asAtom.Name}, []ast.FactStmt{}, []ast.FactStmt{}), glob.EmptyPkg)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	uniMap := map[string]ast.Fc{}
	for i, param := range factSpecDef.DefHeader.Params {
		uniMap[param] = stmt.Fact.Params[i]
	}

	instantiatedFactSpecDef, err := factSpecDef.Instantiate(uniMap)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// itself is true
	err = exec.env.NewFact(&stmt.Fact)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// in facts are true
	for _, inFact := range instantiatedFactSpecDef.DefHeader.ParamInSetsFacts {
		err = exec.env.NewFact(inFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// dom is true
	for _, domFact := range instantiatedFactSpecDef.DomFacts {
		err = exec.env.NewFact(domFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// iff is true
	for _, iffFact := range instantiatedFactSpecDef.IffFacts {
		err = exec.env.NewFact(iffFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// run stmt body
	for _, bodyFact := range stmt.Body {
		execState, err := exec.factStmt(bodyFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return execState, nil
		} else {
			// store fact in original env
			err = originalEnv.NewFact(bodyFact)
			if err != nil {
				return glob.ExecState_Error, err
			}
		}
	}

	return glob.ExecState_True, nil
}
