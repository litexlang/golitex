package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) verTrueEqualFactAndCheckFnReq2(stmt ast.SpecificFactStmt, state *VerState) *glob.VerRet {
	if !state.ReqOk {
		if verRet := ver.checkFnsReq(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		state.UpdateReqOkToTrue()
	}

	if verRet := ver.verByReplaceObjInSpecFactWithValue(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	if verRet := ver.verTrueEqualFactMainLogic(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	// if verRet := ver.verByReplaceObjInSpecFactWithValueAndCompute(stmt, state); verRet.IsTrue() || verRet.IsErr() {
	// 	return verRet
	// }

	return glob.NewEmptyVerRetUnknown()
}
