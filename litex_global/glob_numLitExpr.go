// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_global

import (
	"errors"
	"fmt"
)

type NumLitExpr struct {
	IsPositive  bool
	Left        *NumLitExpr
	OptOrNumber string
	Right       *NumLitExpr
}

// evalNumLitExpr 计算表达式树，返回字符串形式的结果。如果发现不符合规定，返回错误
// bool 表示基于现有的litex-rule，虽然说我不能说你对不对，但你至少没犯错，error表示你犯错了，比如1/0
func (node *NumLitExpr) evalNumLitExpr() (string, bool, error) {
	// Leaf node
	if node.Left == nil && node.Right == nil {
		value := node.OptOrNumber
		if !node.IsPositive {
			if value == "0" {
				value = "0"
			} else {
				value = "-" + value

			}

		}
		return value, true, nil
	}

	leftVal, ok, err := (node.Left).evalNumLitExpr()
	if err != nil {
		return "", false, err
	}
	if !ok {
		return "", false, nil
	}

	rightVal, ok, err := (node.Right).evalNumLitExpr()
	if err != nil {
		return "", false, err
	}
	if !ok {
		return "", false, nil
	}

	var result string
	switch node.OptOrNumber {
	case "+":
		result, ok, err = addBigFloat(leftVal, rightVal)
	case "-":
		result, ok, err = subBigFloat(leftVal, rightVal)
	case "*":
		result, ok, err = mulBigFloat(leftVal, rightVal)
	case "/":
		result, ok, err = divBigFloat(leftVal, rightVal)
	case "^":
		if !isNaturalNumber(rightVal) {
			return "", false, errors.New("exponent must be a natural number")
		}
		result, ok, err = powBigFloat(leftVal, rightVal)
	default:
		return "", false, fmt.Errorf("unknown operator: %s", node.OptOrNumber)
	}

	if err != nil {
		return "", false, err
	}
	if !ok {
		return "", false, nil
	}

	// Apply IsPositive to the result
	if !node.IsPositive {
		result = "-" + result
	}

	return result, true, nil
}

func NumLitExprEqual(leftAsNumLitExpr *NumLitExpr, rightAsNumLitExpr *NumLitExpr) (bool, error) {
	leftAsStr, ok, err := (leftAsNumLitExpr).evalNumLitExpr()
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightAsStr, ok, err := (rightAsNumLitExpr).evalNumLitExpr()
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if leftAsStr == "" || rightAsStr == "" {
		return false, nil
	}

	return cmpBigFloat(leftAsStr, rightAsStr) == 0, nil
}

func NumLitExprLogicOpt(left *NumLitExpr, right *NumLitExpr, builtinLogicOpt string) (bool, error) {
	leftEvaluated, ok, err := (left).evalNumLitExpr()
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightEvaluated, ok, err := (right).evalNumLitExpr()
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	// Apply signs based on IsPositive flags
	if !left.IsPositive {
		leftEvaluated = "-" + leftEvaluated
	}
	if !right.IsPositive {
		rightEvaluated = "-" + rightEvaluated
	}

	switch builtinLogicOpt {
	case ">=":
		return cmpDecimalStrings(leftEvaluated, rightEvaluated) >= 0, nil
	case ">":
		return cmpDecimalStrings(leftEvaluated, rightEvaluated) > 0, nil
	case "<":
		return cmpDecimalStrings(leftEvaluated, rightEvaluated) < 0, nil
	case "<=":
		return cmpDecimalStrings(leftEvaluated, rightEvaluated) <= 0, nil
	case "==":
		return cmpDecimalStrings(leftEvaluated, rightEvaluated) == 0, nil
	case "!=":
		return cmpDecimalStrings(leftEvaluated, rightEvaluated) != 0, nil
	default:
		return false, fmt.Errorf("unsupported builtin logic opt %s", builtinLogicOpt)
	}
}
