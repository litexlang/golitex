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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_global

import (
	"fmt"
	"strings"
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

	// 如果 leftVal 和 rightVal 有超过一个-，那把多余的去掉
	leftVal = simplifyMinusSigns(leftVal)
	rightVal = simplifyMinusSigns(rightVal)

	var result string
	switch node.OptOrNumber {
	case KeySymbolPlus:
		result, ok, err = addBigFloat(leftVal, rightVal)
	case KeySymbolMinus:
		result, ok, err = subBigFloat(leftVal, rightVal)
	case KeySymbolStar:
		result, ok, err = mulBigFloat(leftVal, rightVal)
	case KeySymbolSlash:
		result, ok, err = divBigFloat(leftVal, rightVal)
	case KeySymbolCaret:
		if !isNaturalNumber(rightVal) {
			return "", false, nil
		}
		result, ok, err = powBigFloat(leftVal, rightVal)
	case KeySymbolPercent:
		result, ok, err = modBigFloat(leftVal, rightVal)
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

	// Remove decimal point and trailing zeros if decimal part is all zeros
	if strings.Contains(result, ".") {
		parts := strings.Split(result, ".")
		if len(parts) == 2 {
			// Check if decimal part is all zeros
			allZeros := true
			for _, c := range parts[1] {
				if c != '0' {
					allZeros = false
					break
				}
			}
			if allZeros {
				result = parts[0]
			}
		}
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

func NumLitExprCompareOpt(left *NumLitExpr, right *NumLitExpr, builtinLogicOpt string) (bool, error) {
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
	case "=":
		return cmpDecimalStrings(leftEvaluated, rightEvaluated) == 0, nil
	case "!=":
		return cmpDecimalStrings(leftEvaluated, rightEvaluated) != 0, nil
	default:
		return false, fmt.Errorf("unsupported builtin logic opt %s", builtinLogicOpt)
	}
}

// 不能是小数，不能有负号
func IsNatNumLitExpr(numLitExpr *NumLitExpr) bool {
	str, ok, err := numLitExpr.evalNumLitExpr()
	if err != nil {
		return false
	}
	if !ok {
		return false
	}

	if strings.Contains(str, ".") {
		return false
	}

	if strings.HasPrefix(str, "-") {
		return false
	}

	return true
}

func IsIntegerNumLitExpr(numLitExpr *NumLitExpr) bool {
	str, ok, err := numLitExpr.evalNumLitExpr()
	if err != nil {
		return false
	}
	if !ok {
		return false
	}

	if strings.Contains(str, ".") {
		return false
	}

	return true
}

func IsRationalNumLitExpr(numLitExpr *NumLitExpr) bool {
	return true
}

func IsRealNumLitExpr(numLitExpr *NumLitExpr) bool {
	return true
}

func IsComplexNumLitExpr(numLitExpr *NumLitExpr) bool {
	return true
}

// simplifyMinusSigns 处理字符串中可能存在的多个负号，返回化简后的结果
func simplifyMinusSigns(val string) string {
	if !strings.HasPrefix(val, "-") {
		return val
	}

	// 计算负号的个数
	minusCount := 0
	for _, c := range val {
		if c == '-' {
			minusCount++
		}
	}

	// 如果负号个数是偶数，结果为正；如果是奇数，结果为负
	if minusCount%2 == 0 {
		return strings.TrimLeft(val, "-")
	} else {
		return "-" + strings.TrimLeft(val, "-")
	}
}
