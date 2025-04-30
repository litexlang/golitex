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

package litex_executor

import (
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
)

func (exe *Executor) FcSatisfySpecFactParaReq(stmt *ast.SpecFactStmt) (bool, error) {
	if !glob.VerifyFcSatisfySpecFactParaReq {
		return true, nil
	}

	return true, nil
}

func (exe *Executor) FcSatisfyFnParaReq(fc ast.Fc) (bool, error) {
	if asAtom, ok := fc.(*ast.FcAtom); ok {
		return exe.fcAtomSatisfyParaReq(asAtom)
	} else if asFcFn, ok := fc.(*ast.FcFn); ok {
		return exe.fcFnSatisfyFnParaReq(asFcFn)
	}

	return false, nil
}

func (exe *Executor) fcAtomSatisfyParaReq(fc *ast.FcAtom) (bool, error) {
	return exe.fcAtomDefined(fc)
}

func (exe *Executor) FcDefined(fc ast.Fc) (bool, error) {
	if asAtom, ok := fc.(*ast.FcAtom); ok {
		return exe.fcAtomDefined(asAtom)
	} else if asFcFn, ok := fc.(*ast.FcFn); ok {
		return exe.fcFnDefined(asFcFn)
	}

	return false, nil
}

func (exe *Executor) fcAtomDefined(fc *ast.FcAtom) (bool, error) {
	if ast.IsBuiltinKwFcAtom(fc) {
		return true, nil
	}

	_, ok := exe.env.GetFcAtomDef(fc)
	if !ok {
		return false, nil
	}

	return true, nil
}

func (exe *Executor) fcFnSatisfyFnParaReq(fc *ast.FcFn) (bool, error) {
	// TODO: 还要检查是否符合dom
	return exe.fcFnDefined(fc)

}

func (exe *Executor) fcFnDefined(fc *ast.FcFn) (bool, error) {
	var ok bool = true
	var err = error(nil)

	// head
	ok, err = exe.FcDefined(fc.FnHead)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	// params
	for _, seg := range fc.ParamSegs {
		for _, param := range seg {
			ok, err = exe.FcDefined(param)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}
	}

	return ok, err
}
