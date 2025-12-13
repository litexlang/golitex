package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (env *Env) SatisfyNewFactReq(stmt ast.FactStmt) glob.GlobRet {
	// 检查所有的参数是否都定义了
	panic("not implemented")
}

func (env *Env) AtomsInSpecFactDefined(stmt *ast.SpecFactStmt) glob.GlobRet {
	if ret := env.IsPropDefinedOrBuiltinProp(stmt.PropName); ret.IsNotTrue() {
		return ret
	}

	panic("not implemented")
}

func (env *Env) IsPropDefinedOrBuiltinProp(prop ast.Atom) glob.GlobRet {
	if glob.IsBuiltinPropName(string(prop)) {
		return glob.TrueRet("")
	}

	return glob.ErrRet(fmt.Errorf("undefined prop: %s", prop))
}
