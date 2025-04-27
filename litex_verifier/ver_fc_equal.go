// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	cmp "golitex/litex_comparator"
	env "golitex/litex_env"
	glob "golitex/litex_global"
	memory "golitex/litex_memory"
)

func (ver *Verifier) makeFcEqualFactAndVerify(left, right ast.Fc, state VerState) (bool, error) {
	newSpecFactToCheck := ast.NewSpecFactStmt(ast.TrueAtom, *ast.NewFcAtom(glob.BuiltinEmptyPkgName, glob.KeySymbolEqual), []ast.Fc{left, right})
	return ver.SpecFact(newSpecFactToCheck, state)
}

func (ver *Verifier) fcEqualSpec(left, right ast.Fc, state VerState) (bool, error) {
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
	ok, err = ver.fcEqualSpecInSpecMem(left, right, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if state.isSpec() {
		return false, nil
	}

	// Case: 如果left, right都是 FcFn，那一位位比较一下
	cmpRet, fcEnum, err := ast.CmpFcType(left, right)
	if err != nil {
		return false, err
	}

	if cmpRet != 0 {
		return false, nil
	}

	if fcEnum == ast.FcFnEnum {
		// WARNING:  这里根本不是SpecMsg，而是RoundMsg，所以fcEqualSpec里不能是可能用到非SpecFact的
		// state = state.addRound()
		return ver.fcFnEq(left.(*ast.FcFn), right.(*ast.FcFn), state)
		// return ver.fcFnEq(left.(*ast.FcFn), right.(*ast.FcFn), SpecMsg)
	} else if fcEnum == ast.FcAtomEnum {
		return false, nil
	}

	return false, fmt.Errorf("unexpected")
}

func (ver *Verifier) fcEqualSpecInSpecMem(left, right ast.Fc, state VerState) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		verified, err := ver.FcEqualSpecEnvSpecMem(curEnv, left, right, state)
		if err != nil {
			return false, err
		}
		if verified {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) FcEqualSpecEnvSpecMem(curEnv *env.Env, left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	ok, err := ver.FcEqualSpecEnvSpecMemRule(curEnv, left, right, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	ok, err = ver.FcEqualSpecEnvSpecMemRule(curEnv, right, left, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return false, nil
}

func (ver *Verifier) FcEqualSpecEnvSpecMemRule(curEnv *env.Env, keyFc ast.Fc, fcToComp ast.Fc, state VerState) (bool, error) {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: keyFc, Values: &[]ast.Fc{}}

	searchedNode, err := curEnv.EqualFactMem.Mem.TreeSearch(&key)

	if err != nil {
		return false, err
	}

	if searchedNode == nil {
		return false, nil
	}

	key2 := memory.EqualFactMemoryTreeNode{FcAsKey: fcToComp, Values: &[]ast.Fc{}}
	searchedNode2, err := curEnv.EqualFactMem.Mem.TreeSearch(&key2)

	if err != nil {
		return false, err
	}

	if searchedNode2 != nil && searchedNode.Key != nil && searchedNode2.Key != nil {
		if searchedNode.Key.Values != nil && searchedNode.Key.Values == searchedNode2.Key.Values {
			return true, nil
		}
	}

	ok, err := cmp.SliceFcAllEqualToGivenFcBuiltinRule(searchedNode.Key.Values, fcToComp)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return ok, nil
}

// func (ver *Verifier) fcEqual(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	// Case: 用内置方法直接比较，比如计算字面量都是整数，那可以通过运算来比较
// 	left := stmt.Params[0]
// 	right := stmt.Params[1]

// 	ok, err := cmp.CmpFcRule(left, right)
// 	if err != nil {
// 		return false, err
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	// state = state.addRound()

// 	// Case: equalSpecMem里找
// 	ok, err = ver.fcEqualSpecInSpecMem(left, right, state)
// 	if err != nil {
// 		return false, err
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	ok, err = ver.SpecFactCond(stmt, state)
// 	if err != nil {
// 		return false, err
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	if state.isSpec() {
// 		return false, nil
// 	}

// 	ok, err = ver.SpecFactUni(stmt, state)
// 	if err != nil {
// 		return false, err
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	// Case: 如果left, right都是 FcFn，那一位位比较一下
// 	cmpRet, fcEnum, err := ast.CmpFcType(left, right)
// 	if err != nil {
// 		return false, err
// 	}

// 	if cmpRet != 0 {
// 		return false, nil
// 	}

// 	if fcEnum == ast.FcFnEnum {
// 		return ver.fcFnEq(left.(*ast.FcFn), right.(*ast.FcFn), state)
// 		// return ver.fcFnEq(left.(*ast.FcFn), right.(*ast.FcFn), SpecMsg)
// 	} else if fcEnum == ast.FcAtomEnum {
// 		return false, nil
// 	}

// 	if state.requireMsg() {
// 		ver.unknownMsgEnd(fmt.Sprintf("%s = %s", left.String(), right.String()), "")
// 	}

// 	return false, nil
// }
