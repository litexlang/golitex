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

package litex_ast

import (
	"fmt"
	"sort"
)

func (stmt *FcFn) isAdd() (bool, error) {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false, nil
	}
	if asAtom.Name == "+" {
		if len(stmt.ParamSegs) != 2 {
			return false, fmt.Errorf("add must have 2 params, but got %d", len(stmt.ParamSegs))
		}
		return true, nil
	}
	return false, nil
}

func (stmt *FcFn) isMul() (bool, error) {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false, nil
	}
	if asAtom.Name == "*" {
		if len(stmt.ParamSegs) != 2 {
			return false, fmt.Errorf("mul must have 2 params, but got %d", len(stmt.ParamSegs))
		}
		return true, nil
	}
	return false, nil
}

func (stmt *FcFn) isMinusAsInfix() (bool, error) {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false, nil
	}
	if asAtom.Name == "-" {
		if len(stmt.ParamSegs) != 2 {
			return false, fmt.Errorf("sub must have 2 params, but got %d", len(stmt.ParamSegs))
		}
		return true, nil
	}
	return false, nil
}

func (stmt *FcFn) isMinusAsPrefix() (bool, error) {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false, nil
	}
	if asAtom.Name == "-" {
		if len(stmt.ParamSegs) != 1 {
			return false, fmt.Errorf("minus must have 1 param, but got %d", len(stmt.ParamSegs))
		}
		return true, nil
	}
	return false, nil
}

func (stmt *FcFn) isDiv() (bool, error) {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false, nil
	}
	if asAtom.Name == "/" {
		if len(stmt.ParamSegs) != 2 {
			return false, fmt.Errorf("div must have 2 params, but got %d", len(stmt.ParamSegs))
		}
		return true, nil
	}
	return false, nil
}

func (stmt *FcAtom) orderNumberExpr() ([]Fc, error) {
	return []Fc{stmt}, nil
}

func (stmt *FcFn) orderNumberExpr() ([]Fc, error) {
	isAdd, err := stmt.isAdd()
	if err != nil {
		return nil, err
	}
	if isAdd {
		return stmt.orderAddFcFn()
	}

	isMul, err := stmt.isMul()
	if err != nil {
		return nil, err
	}
	if isMul {
		return stmt.orderMulFcFn()
	}

	isMinusAsInfix, err := stmt.isMinusAsInfix()
	if err != nil {
		return nil, err
	}
	if isMinusAsInfix {
		return stmt.orderMinusAsInfixFcFn()
	}

	isMinusAsPrefix, err := stmt.isMinusAsPrefix()
	if err != nil {
		return nil, err
	}
	if isMinusAsPrefix {
		return stmt.orderMinusAsPrefixFcFn()
	}

	isDiv, err := stmt.isDiv()
	if err != nil {
		return nil, err
	}
	if isDiv {
		return stmt.orderDivFcFn()
	}

	return nil, nil
}

func (stmt *FcFn) orderAddFcFn() ([]Fc, error) {
	orderedLeft, err := stmt.ParamSegs[0].orderNumberExpr()
	if err != nil {
		return nil, err
	}
	orderedRight, err := stmt.ParamSegs[1].orderNumberExpr()
	if err != nil {
		return nil, err
	}

	// order merged left, right
	merged := append(orderedLeft, orderedRight...)
	orderedFc, err := orderFc(merged)
	if err != nil {
		return nil, err
	}

	return orderedFc, nil
}

func (stmt *FcFn) orderMulFcFn() ([]Fc, error) {
	return []Fc{}, nil
}

func (stmt *FcFn) orderMinusAsInfixFcFn() ([]Fc, error) {
	return []Fc{}, nil
}

func (stmt *FcFn) orderDivFcFn() ([]Fc, error) {
	return []Fc{}, nil
}

func (stmt *FcFn) orderMinusAsPrefixFcFn() ([]Fc, error) {
	return []Fc{}, nil
}

func IsNumberExpr_OrderIt(fc Fc) (Fc, bool, error) {
	return nil, false, nil
}

func orderFc(fcSlice []Fc) ([]Fc, error) {
	// Create a slice of structs that pair the Fc with its string representation
	type fcWithStr struct {
		fc    Fc
		fcStr string
	}

	// Create a temporary slice to hold the paired values
	temp := make([]fcWithStr, len(fcSlice))
	for i, fc := range fcSlice {
		temp[i] = fcWithStr{
			fc:    fc,
			fcStr: fc.String(),
		}
	}

	// Sort the temporary slice based on the string representation
	sort.Slice(temp, func(i, j int) bool {
		return temp[i].fcStr < temp[j].fcStr
	})

	// Extract the sorted Fc values
	orderedFc := make([]Fc, len(fcSlice))
	for i, item := range temp {
		orderedFc[i] = item.fc
	}

	return orderedFc, nil
}
