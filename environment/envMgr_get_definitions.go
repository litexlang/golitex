package litex_env

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (envMgr *EnvMgr) GetPropDef(propName ast.Atom) *ast.DefPropStmt {
	var pkgName string
	var envMgrContainsDef = envMgr

	withPkgName, pkgName, _ := glob.GetPkgNameAndName(string(propName))

	if withPkgName {
		envMgrContainsDef = envMgr.GetEnvMgrOfName(pkgName)
	} else {
		envMgrContainsDef = envMgr
	}

	// depth
	propDef, ok := envMgrContainsDef.AllDefinedPropNames[string(propName)]
	if ok {
		return propDef
	}
	return nil
}

func (envMgr *EnvMgr) GetExistPropDef(propName ast.Atom) *ast.DefExistPropStmt {
	var pkgName string
	var envMgrContainsDef = envMgr

	withPkgName, pkgName, _ := glob.GetPkgNameAndName(string(propName))

	if withPkgName {
		envMgrContainsDef = envMgr.GetEnvMgrOfName(pkgName)
	} else {
		envMgrContainsDef = envMgr
	}

	existPropDef, ok := envMgrContainsDef.AllDefinedExistPropNames[string(propName)]
	if ok {
		return existPropDef
	}
	return nil
}
