// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) FcSatisfySpecFactParaReq(stmt *ast.SpecFactStmt) (bool, error) {
	if !glob.VerifyFcSatisfySpecFactParaReq {
		return true, nil
	}

	// prop Name
	if ast.IsFcAtomAndHasBuiltinPropName(stmt.PropName) {
		return true, nil
	} else if stmt.IsPureFact() {
		_, ok := ver.env.GetPropDef(stmt.PropName)
		if !ok {
			return false, nil
		}
	} else if stmt.IsExist_St_Fact() {
		_, ok := ver.env.GetExistPropDef(stmt.PropName)
		if !ok {
			return false, nil
		}
	}

	for _, param := range stmt.Params {
		ok, err := ver.FcSatisfyFnParaReq(param)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}
	return true, nil
}

func (ver *Verifier) FcSatisfyFnParaReq(fc ast.Fc) (bool, error) {
	if asAtom, ok := fc.(ast.FcAtom); ok {
		return ver.fcAtomSatisfyParaReq(asAtom)
	} else if asFcFn, ok := fc.(*ast.FcFn); ok {
		return ver.fcFnSatisfyFnParaReq(asFcFn)
	}

	return false, nil
}

func (ver *Verifier) fcAtomSatisfyParaReq(fc ast.FcAtom) (bool, error) {
	return ver.fcAtomDefined(fc)
}

func (ver *Verifier) fcAtomDefined(fc ast.FcAtom) (bool, error) {
	if _, ok, _ := ast.MakeFcIntoNumLitExpr(fc); ok {
		return true, nil
	}

	if _, ok := glob.BuiltinKeywordsSet[string(fc)]; ok {
		return true, nil
	}

	ok := ver.env.IsFcAtomDeclaredByUser(fc)
	if !ok {
		return false, nil
	}

	return true, nil
}

func (ver *Verifier) FcDefined(fc ast.Fc) (bool, error) {
	if asAtom, ok := fc.(ast.FcAtom); ok {
		return ver.fcAtomDefined(asAtom)
	} else if asFcFn, ok := fc.(*ast.FcFn); ok {
		return ver.fcFnDefined(asFcFn)
	}

	return false, nil
}

func (ver *Verifier) fcFnSatisfyFnParaReq(fc *ast.FcFn) (bool, error) {
	// TODO: 还要检查是否符合dom
	return ver.fcFnDefined(fc)

}

func (ver *Verifier) fcFnDefined(fc *ast.FcFn) (bool, error) {
	if _, ok, _ := ast.MakeFcIntoNumLitExpr(fc.FnHead); ok {
		return true, nil
	}

	var ok bool = true
	var err = error(nil)

	// head
	ok, err = ver.FcDefined(fc.FnHead)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	// params
	for _, seg := range fc.Params {
		ok, err = ver.FcDefined(seg)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return ok, err
}
