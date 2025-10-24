package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
)

func (ver *Verifier) verByReplaceFcInSpecFactWithValue(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	var ok bool
	var err error
	replaced, newStmt := ver.env.ReplaceFcInSpecFactWithValue(stmt)
	if replaced {
		ok, err = ver.verTrueEqualFactMainLogic(newStmt, state, true)
		if err != nil {
			return false, err
		}

		if ok {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
			}
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) verByReplaceFcInSpecFactWithValueAndCompute(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	var ok bool
	var err error
	replaced, newStmt, err := ver.env.ReplaceFcInSpecFactWithValueAndCompute(stmt)
	if err != nil {
		return false, err
	}
	if replaced {
		ok, err = ver.verTrueEqualFactMainLogic(newStmt, state, true)
		if err != nil {
			return false, err
		}
		if ok {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values and computing", stmt.String(), newStmt.String()))
			}
			return true, nil
		}
	}

	return false, nil
}
