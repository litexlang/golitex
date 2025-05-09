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
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (ver *Verifier) btEqualRule_useSpecMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.fcEqualSpec(stmt, state)
	if err != nil {
		return false, err
	}
	if state.requireMsg() && ok {
		ver.successMsgEnd(fmt.Sprintf("%s = %s", stmt.Params[0].String(), stmt.Params[1].String()), "")
	}
	return ok, err
}

func (ver *Verifier) fcEqualSpec(stmt *ast.SpecFactStmt, state VerState) (bool, error) {

	left := stmt.Params[0]
	right := stmt.Params[1]

	// Case: 用内置方法直接比较，比如计算字面量都是整数，那可以通过运算来比较
	ok, err := cmp.CmpFcRule(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// state = state.addRound()

	// Case: equalSpecMem里找
	ok, err = ver.fcEqualSpecInSpecMem(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// Case: 如果left, right都是 FcFn，那一位位比较一下
	cmpRet, fcEnum, err := cmp.CmpFcType(left, right)
	if err != nil {
		return false, err
	}

	if cmpRet != 0 {
		return false, nil
	}

	if fcEnum == cmp.FcFnEnum {
		// WARNING:  这里根本不是SpecMsg，而是RoundMsg，所以fcEqualSpec里不能是可能用到非SpecFact的
		// state = state.addRound()
		return ver.fcFnEq(left.(*ast.FcFn), right.(*ast.FcFn), state.toSpec())
		// return ver.fcFnEq(left.(*ast.FcFn), right.(*ast.FcFn), SpecMsg)
	} else if fcEnum == cmp.FcAtomEnum {
		return false, nil
	}

	return false, fmt.Errorf("unexpected")
}

func (ver *Verifier) fcEqualSpecInSpecMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	left := stmt.Params[0]
	right := stmt.Params[1]
	fact := stmt
	fact2 := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtom(glob.BtEmptyPkgName, glob.KeySymbolEqual), []ast.Fc{right, left})

	upMostEnv := theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		verified, err := ver.specFactUsingMemSpecifically(fact, state)
		if err != nil {
			return false, err
		}
		if verified {
			return true, nil
		}

		verified, err = ver.specFactUsingMemSpecifically(fact2, state)
		if err != nil {
			return false, err
		}
		if verified {
			return true, nil
		}
	}
	return false, nil
}

// func (ver *Verifier) makeFcEqualFactAndVerify(left, right ast.Fc, state VerState) (bool, error) {
// 	newSpecFactToCheck := ast.NewSpecFactStmt(ast.TrueAtom, *ast.NewFcAtom(glob.BuiltinEmptyPkgName, glob.KeySymbolEqual), []ast.Fc{left, right})
// 	return ver.SpecFact(newSpecFactToCheck, state)
// }
