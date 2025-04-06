package litexcomparator

import (
	"fmt"
	parser "golitex/litex_parser"
	"strings"
)

// EvaluateNumberFc 计算表达式树，返回字符串形式的结果
func EvaluateNumberFc(node *parser.NumberFc) string {
	// 叶子节点
	if node.Left == nil && node.Right == nil {
		return node.OptOrNumber
	}

	leftVal := EvaluateNumberFc(node.Left)
	rightVal := EvaluateNumberFc(node.Right)

	switch node.OptOrNumber {
	case "+":
		return addBigFloat(leftVal, rightVal)
	case "-":
		return subBigFloat(leftVal, rightVal)
	case "*":
		return mulBigFloat(leftVal, rightVal)
		// TODO
		// case "/":
		// 	return divBigFloat(leftVal, rightVal)
		// case "^":
		// return orderBigFloat(leftVal, rightVal)
	default:
		panic(fmt.Sprintf("未知运算符: %s", node.OptOrNumber))
	}
}

func addBigFloat(a, b string) string {
	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// 对齐小数部分长度
	maxFracLen := max(len(aFrac), len(bFrac))
	aFrac = padRight(aFrac, maxFracLen, '0')
	bFrac = padRight(bFrac, maxFracLen, '0')

	// 小数部分相加
	fracSum, carry := addStrings(aFrac, bFrac, false)

	// 去除末尾的0（小数部分）
	fracSum = strings.TrimRight(fracSum, "0")

	// 整数部分对齐
	maxIntLen := max(len(aInt), len(bInt))
	aInt = padLeft(aInt, maxIntLen, '0')
	bInt = padLeft(bInt, maxIntLen, '0')

	// 整数部分相加
	intSum, carry := addStrings(aInt, bInt, carry)
	if carry {
		intSum = "1" + intSum
	}

	result := intSum
	if len(fracSum) > 0 {
		result += "." + fracSum
	}

	return result
}

func splitNumberToIntPartFracPart(s string) (string, string) {
	parts := strings.Split(s, ".")
	if len(parts) == 1 {
		return parts[0], ""
	}
	return parts[0], parts[1]
}

func addStrings(a, b string, carry bool) (string, bool) {
	if len(a) != len(b) {
		panic("addStrings length mismatch")
	}

	n := len(a)
	result := make([]byte, n)
	c := 0
	if carry {
		c = 1
	}

	for i := n - 1; i >= 0; i-- {
		sum := int(a[i]-'0') + int(b[i]-'0') + c
		c = sum / 10
		result[i] = byte(sum%10) + '0'
	}

	return string(result), c > 0
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func padLeft(s string, length int, pad byte) string {
	for len(s) < length {
		s = string(pad) + s
	}
	return s
}

func padRight(s string, length int, pad byte) string {
	for len(s) < length {
		s += string(pad)
	}
	return s
}

// 去除前导0
func trimLeftZero(s string) string {
	for len(s) > 1 && s[0] == '0' {
		s = s[1:]
	}
	return s
}

// 判断大小：返回 1 if a > b, -1 if a < b, 0 if a==b
func CompareBigFloat(a, b string) int {
	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	aInt = trimLeftZero(aInt)
	bInt = trimLeftZero(bInt)

	if len(aInt) > len(bInt) {
		return 1
	}
	if len(aInt) < len(bInt) {
		return -1
	}
	if aInt > bInt {
		return 1
	}
	if aInt < bInt {
		return -1
	}

	// 补齐小数部分长度
	maxLen := max(len(aFrac), len(bFrac))
	aFrac = padRight(aFrac, maxLen, '0')
	bFrac = padRight(bFrac, maxLen, '0')

	if aFrac > bFrac {
		return 1
	}
	if aFrac < bFrac {
		return -1
	}
	return 0
}

// 字符串大数减法
func subBigFloat(a, b string) string {
	if CompareBigFloat(a, b) == -1 {
		panic("暂不支持负数")
	}

	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// 补齐小数部分长度
	maxFracLen := max(len(aFrac), len(bFrac))
	aFrac = padRight(aFrac, maxFracLen, '0')
	bFrac = padRight(bFrac, maxFracLen, '0')

	// 小数部分先减
	fracRes, borrow := subStrings(aFrac, bFrac, false)

	// 整数部分减（带借位）
	intRes, _ := subStrings(aInt, bInt, borrow)

	intRes = trimLeftZero(intRes)
	if intRes == "" {
		intRes = "0"
	}

	if fracRes != "" {
		fracRes = strings.TrimRight(fracRes, "0")
		if fracRes != "" {
			return intRes + "." + fracRes
		}
	}
	return intRes
}

// 字符串减法，a >= b
func subStrings(a, b string, borrow bool) (string, bool) {
	maxLen := max(len(a), len(b))
	a = padLeft(a, maxLen, '0')
	b = padLeft(b, maxLen, '0')

	res := make([]byte, maxLen)
	curBorrow := 0
	if borrow {
		curBorrow = 1
	}

	for i := maxLen - 1; i >= 0; i-- {
		x := int(a[i]-'0') - curBorrow
		y := int(b[i] - '0')
		if x < y {
			x += 10
			curBorrow = 1
		} else {
			curBorrow = 0
		}
		res[i] = byte(x-y) + '0'
	}

	return string(res), curBorrow > 0
}

// 大数乘法
func mulBigFloat(a, b string) string {
	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// 先拼接成整数
	aTotal := aInt + aFrac
	bTotal := bInt + bFrac

	fracLen := len(aFrac) + len(bFrac)

	// 乘法
	product := mulStrings(aTotal, bTotal)

	if fracLen > 0 {
		if len(product) <= fracLen {
			product = padLeft(product, fracLen+1, '0')
		}
		intPart := product[:len(product)-fracLen]
		fracPart := product[len(product)-fracLen:]
		fracPart = strings.TrimRight(fracPart, "0")
		if fracPart == "" {
			return trimLeftZero(intPart)
		}
		return trimLeftZero(intPart) + "." + fracPart
	}
	return trimLeftZero(product)
}

// 字符串乘法
func mulStrings(a, b string) string {
	n, m := len(a), len(b)
	res := make([]int, n+m)

	for i := n - 1; i >= 0; i-- {
		for j := m - 1; j >= 0; j-- {
			res[i+j+1] += int(a[i]-'0') * int(b[j]-'0')
		}
	}

	// 处理进位
	for i := len(res) - 1; i > 0; i-- {
		res[i-1] += res[i] / 10
		res[i] %= 10
	}

	var sb strings.Builder
	leadingZero := true
	for _, v := range res {
		if v == 0 && leadingZero {
			continue
		}
		leadingZero = false
		sb.WriteByte(byte(v) + '0')
	}
	if sb.Len() == 0 {
		return "0"
	}
	return sb.String()
}
