// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_verifier

import (
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
)

func (ver *Verifier) FcSatisfySpecFactParaReq(stmt *ast.SpecFactStmt) (bool, error) {
	if !glob.VerifyFcSatisfySpecFactParaReq {
		return true, nil
	}

	return true, nil
}

func (ver *Verifier) FcSatisfyFnParaReq(fc ast.Fc) (bool, error) {
	if asAtom, ok := fc.(*ast.FcAtom); ok {
		_, ok = ver.env.GetFcAtomDef(asAtom)
		if !ok {
			return false, nil
		}
	} else 

}

func (ver *Verifier) FcAtomDefined(fc *ast.FcAtom) (ast.DefStmt, bool, error) {
	if 
	
	defStmt, ok := ver.env.GetFcAtomDef(fc)
	if !ok {
		return nil, false, nil
	}

	return defStmt, true, nil
}
