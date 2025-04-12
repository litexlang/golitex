package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	env "golitex/litex_env"
	glob "golitex/litex_global"
)

func (ver *Verifier) builtinLogicOptRule(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.PropName.PkgName != "" {
		return false, nil
	}

	if !glob.IsKeySymbolRelaProp(stmt.PropName.Value) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	// switch stmt.PropName.Value {
	// 	case
	// }

	return false, nil

}
