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
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
)

func (ver *Verifier) btLogicOptSpec(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// 存储相等型事实，不需要有一个额外的数据结构来存；但是验证相等性事实的时候，需要用不一样的方式去验证
	if stmt.IsPropNameEqual() {
		// 所有的验证方法都集成在btEqualRule里了，包括用已知的uni，cond来证明。= 和其他事很不一样的
		return ver.btEqualRule(stmt, state)
	}

	if stmt.IsPropNameAssociative() {
		// 如果用内置的验证方法不成立，还是能用后面的方法验证的。
		if ok, err := ver.btAssociativeRule(stmt, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		}
	}

	if stmt.IsPropNameCommutative() {
		if ok, err := ver.btCommutativeRule(stmt, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		}
	}

	// TODO 处理其他的builtin logic infix opt
	ok, err := ver.btLogicInfixOptBtRule(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.specFactUsingMemSpecifically(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) btLogicInfixOptBtRule(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.PropName.PkgName != "" {
		return false, nil
	}

	if ok, err := ver.btNumberInfixCompareProp(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.btInProp(stmt); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.btCommutativeRule(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.btAssociativeRule(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) btNumberInfixCompareProp(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !glob.IsBuiltinNumberInfixRelaProp(stmt.PropName.Name) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	leftNumLitExpr, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightNumLitExpr, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[1])
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	ok, err = glob.NumLitExprCompareOpt(leftNumLitExpr, rightNumLitExpr, stmt.PropName.Name)

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

func (ver *Verifier) btCommutativeRule(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// TODO: 处理commutative rule
	_, _ = stmt, state
	return false, nil
}

func (ver *Verifier) btAssociativeRule(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// TODO: 处理associative rule
	_, _ = stmt, state
	return false, nil
}

func (ver *Verifier) btNumLitInProp(stmt *ast.SpecFactStmt) (bool, error) {
	if !ast.IsInProp(&stmt.PropName) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params))
	}

	leftFc, ok, err := ast.MakeFcIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if ast.IsNatFcAtom(stmt.Params[1]) {
		return glob.IsNatNumLitExpr(leftFc), nil
	}

	if ast.IsIntegerFcAtom(stmt.Params[1]) {
		return glob.IsIntegerNumLitExpr(leftFc), nil
	}

	if ast.IsRationalFcAtom(stmt.Params[1]) {
		return glob.IsRationalNumLitExpr(leftFc), nil
	}

	if ast.IsRealFcAtom(stmt.Params[1]) {
		return glob.IsRealNumLitExpr(leftFc), nil
	}

	return false, nil
}

func (ver *Verifier) btInProp(stmt *ast.SpecFactStmt) (bool, error) {
	ok, err := ver.btNumLitInProp(stmt)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}
