package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) verSpecFactPreProcess(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	verRet := ver.verSpecFactPreProcess_ReplaceSymbolsWithValues(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPostProcess(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	verRet := ver.verSpecFactPostProcess_UseCommutativity(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactPostProcess_UseTransitivity(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactPostProcess_WhenPropIsComparison(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactMainLogic(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if verRet := ver.verSpecFactByBuiltinRules(stmt, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verSpecFact_BySpecMem(stmt, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verSpecFact_ByDEF(stmt, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if !state.isFinalRound() {
		if verRet := ver.verSpecFact_ByLogicMem(stmt, state); verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}

		if verRet := ver.verSpecFact_UniMem(stmt, state); verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFact2(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	verRet := ver.verSpecFactPreProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactMainLogic(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactPostProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactByMainLogicAndPostProcess(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	verRet := ver.verSpecFactMainLogic(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactPostProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPreProcess_ReplaceSymbolsWithValues(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	replaced, newStmt := ver.Env.ReplaceObjInSpecFactWithValue(stmt)
	if replaced {
		verRet := ver.verSpecFactByMainLogicAndPostProcess(newStmt, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			msg := fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String())
			if state.WithMsg {
				return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{msg})
			}
			return glob.NewEmptyVerRetTrue()
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPreProcessAndMainLogic(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	verRet := ver.verSpecFactPreProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactMainLogic(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPostProcess_UseCommutativity(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if ver.Env.IsCommutativeProp(stmt) {
		reverseParamsOrderStmt, err := stmt.ReverseParameterOrder()
		if err != nil {
			return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{err.Error()})
		}

		verRet := ver.verSpecFactPreProcessAndMainLogic(reverseParamsOrderStmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}

		return glob.NewEmptyVerRetUnknown()
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPostProcess_UseTransitivity(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if stmt.FactType == ast.TruePure && ver.Env.IsTransitiveProp(string(stmt.PropName)) {
		relatedObjSlice := ver.Env.GetRelatedObjSliceOfTransitiveProp(string(stmt.PropName), stmt.Params[0])
		if len(relatedObjSlice) == 0 {
			return glob.NewEmptyVerRetUnknown()
		}

		for _, relatedObj := range relatedObjSlice {
			relatedObjStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.PropName), []ast.Obj{relatedObj, stmt.Params[1]}, stmt.Line)
			verRet := ver.verSpecFactPreProcessAndMainLogic(relatedObjStmt, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				msg := fmt.Sprintf("%s is true by %s is a transitive prop and %s is true", stmt.String(), string(stmt.PropName), relatedObjStmt.String())
				if state.WithMsg {
					return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{msg})
				}
				return glob.NewEmptyVerRetTrue()
			}
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPostProcess_WhenPropIsComparison(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	return glob.NewEmptyVerRetUnknown()
}
