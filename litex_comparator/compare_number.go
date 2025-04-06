package litexcomparator

import (
	"strings"
)

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

// CompareBigFloat 比较两个字符串形式的浮点数
// 返回 -1 if a < b, 0 if a == b, 1 if a > b
func CompareBigFloat(a, b string) int {
	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// 去除整数部分前导0
	aInt = strings.TrimLeft(aInt, "0")
	bInt = strings.TrimLeft(bInt, "0")

	// 先比较整数部分长度
	if len(aInt) < len(bInt) {
		return -1
	}
	if len(aInt) > len(bInt) {
		return 1
	}

	// 长度相同，比较具体内容
	if aInt < bInt {
		return -1
	}
	if aInt > bInt {
		return 1
	}

	// 整数部分相等，比较小数部分
	maxFracLen := max(len(aFrac), len(bFrac))
	aFrac = padRight(aFrac, maxFracLen, '0')
	bFrac = padRight(bFrac, maxFracLen, '0')

	if aFrac < bFrac {
		return -1
	}
	if aFrac > bFrac {
		return 1
	}

	// 完全相等
	return 0
}
