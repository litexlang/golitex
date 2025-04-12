package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
)

func (ver *Verifier) builtinLogicOptRule(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.PropName.PkgName != "" {
		return false, nil
	}

	if !glob.IsKeySymbolRelaProp(stmt.PropName.Value) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	leftNumLitExpr, ok, err := ast.IsFcBuiltinNumLitExpr(stmt.Params[0])
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightNumLitExpr, ok, err := ast.IsFcBuiltinNumLitExpr(stmt.Params[1])
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	ok, err = glob.NumLitExprLogicOpt(leftNumLitExpr, rightNumLitExpr, stmt.PropName.Value)

	if err != nil {
		return false, err
	}
	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "builtin rules")
		} else {
			ver.successNoMsg()
		}
		return true, nil
	}
	return false, nil
}
