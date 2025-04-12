package litex_global

import (
	"fmt"
	"strings"
)

func BuiltinLogicOptOnNumLitExpr(left *NumLitExpr, right *NumLitExpr, builtinLogicOpt string) (bool, error) {
	leftEvaluated, ok, err := EvalNumLitExprFc(left)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightEvaluated, ok, err := EvalNumLitExprFc(right)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	switch builtinLogicOpt {
	case ">=":
		return CompareDecimalStrings(leftEvaluated, rightEvaluated) >= 0, nil
	case ">":
		return CompareDecimalStrings(leftEvaluated, rightEvaluated) > 0, nil
	case "<":
		return CompareDecimalStrings(leftEvaluated, rightEvaluated) < 0, nil
	case "<=":
		return CompareDecimalStrings(leftEvaluated, rightEvaluated) <= 0, nil
	case "==":
		return CompareDecimalStrings(leftEvaluated, rightEvaluated) == 0, nil
	case "!=":
		return CompareDecimalStrings(leftEvaluated, rightEvaluated) != 0, nil
	}

	return false, fmt.Errorf("unsupported builtin logic opt %s", builtinLogicOpt)
}

// CompareDecimalStrings 比较两个带小数点的数字符串
// 返回:
//
//	-1 如果 a < b
//	 0 如果 a == b
//	 1 如果 a > b
func CompareDecimalStrings(a, b string) int {
	// 处理符号（假设都是正数，如果有负号需要额外处理）
	// 这里假设输入是有效的数字字符串（无前导0，除非是 "0.xxx"）

	// 拆分整数和小数部分
	aInt, aFrac := splitNumber(a)
	bInt, bFrac := splitNumber(b)

	// 先比较整数部分
	cmpInt := compareIntegerParts(aInt, bInt)
	if cmpInt != 0 {
		return cmpInt
	}

	// 整数部分相同，比较小数部分
	return compareFractionalParts(aFrac, bFrac)
}

// splitNumber 拆分数字的整数和小数部分
// 例如 "123.456" -> ("123", "456")
// "123" -> ("123", "")
// ".456" -> ("", "456")
func splitNumber(s string) (intPart, fracPart string) {
	parts := strings.Split(s, ".")
	switch len(parts) {
	case 1:
		return parts[0], "" // 无小数点
	case 2:
		return parts[0], parts[1]
	default:
		return "", "" // 无效格式（比如多个小数点）
	}
}

// compareIntegerParts 比较整数部分
func compareIntegerParts(a, b string) int {
	// 先比较位数
	if len(a) > len(b) {
		return 1
	}
	if len(a) < len(b) {
		return -1
	}

	// 位数相同，逐位比较
	for i := 0; i < len(a); i++ {
		if a[i] > b[i] {
			return 1
		}
		if a[i] < b[i] {
			return -1
		}
	}

	return 0 // 完全相等
}

// compareFractionalParts 比较小数部分
func compareFractionalParts(a, b string) int {
	maxLen := max(len(a), len(b))
	for i := 0; i < maxLen; i++ {
		// 如果某一位超出范围，视为 '0'
		aDigit := byte('0')
		if i < len(a) {
			aDigit = a[i]
		}

		bDigit := byte('0')
		if i < len(b) {
			bDigit = b[i]
		}

		if aDigit > bDigit {
			return 1
		}
		if aDigit < bDigit {
			return -1
		}
	}

	return 0 // 完全相等（包括末尾的 0）
}

func IsNumLitStr(s string) bool {
	if s == "" {
		return false
	}

	hasDigit := false
	hasDot := false

	for _, c := range s {
		if c >= '0' && c <= '9' {
			hasDigit = true
		} else if c == '.' {
			if hasDot {
				return false
			}
			hasDot = true
		} else {
			return false
		}
	}

	return hasDigit
}
