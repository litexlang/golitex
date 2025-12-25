// Copyright Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

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
