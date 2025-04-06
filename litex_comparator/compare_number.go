package litexcomparator

import (
	"fmt"
	parser "golitex/litex_parser"
	"strings"
)

func CmpNumberBuiltin(numberAsStr string, right parser.Fc) (bool, error) {

	return false, nil
}

func addBigFloat(a, b string) string {
	// 分离整数部分和小数部分
	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// 小数部分相加
	fracSum, carry := addStrings(aFrac, bFrac, false)

	// 整数部分相加（加上小数部分的进位）
	intSum, _ := addStrings(aInt, bInt, carry)

	// 组合结果
	result := intSum
	if len(fracSum) > 0 {
		result += "." + fracSum
	}

	return result
}

// 分离整数和小数部分
func splitNumberToIntPartFracPart(s string) (string, string) {
	parts := strings.Split(s, ".")
	if len(parts) == 1 {
		return parts[0], ""
	}
	return parts[0], parts[1]
}

// 对两个数字字符串进行相加，可以是整数或小数部分
// isIntPart表示是否是整数部分的加法（处理前导零不同）
func addStrings(a, b string, carry bool) (string, bool) {
	// 对齐长度
	maxLen := max(len(a), len(b))
	a = padRight(a, maxLen, '0')
	b = padRight(b, maxLen, '0')

	result := make([]byte, maxLen)
	currentCarry := 0
	if carry {
		currentCarry = 1
	}

	for i := maxLen - 1; i >= 0; i-- {
		sum := int(a[i]-'0') + int(b[i]-'0') + currentCarry
		currentCarry = sum / 10
		result[i] = byte(sum%10) + '0'
	}

	resStr := string(result)
	// 去除小数部分末尾的零（如果是小数部分）
	if !strings.Contains(a, ".") && !strings.Contains(b, ".") {
		resStr = strings.TrimRight(resStr, "0")
		if resStr == "" {
			resStr = "0"
		}
	}

	return resStr, currentCarry > 0
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func padRight(s string, length int, pad byte) string {
	for len(s) < length {
		s += string(pad)
	}
	return s
}

func main() {
	// 测试用例
	testCases := []struct {
		a, b, expected string
	}{
		{"123.45", "67.89", "191.34"},
		{"0.1", "0.2", "0.3"},
		{"99999999999999999999.99999999999999999999", "0.00000000000000000001", "100000000000000000000.00000000000000000000"},
		{"123456789012345678901234567890.987654321", "98765432109876543210987654321.012345679", "222222221122222222112222222211.999999999"},
		{"1.0000000000000000000000000000000000000001", "2.0000000000000000000000000000000000000002", "3.0000000000000000000000000000000000000003"},
	}

	for _, tc := range testCases {
		result := addBigFloat(tc.a, tc.b)
		fmt.Printf("%s + %s = %s (期望: %s) ", tc.a, tc.b, result, tc.expected)
		if result == tc.expected {
			fmt.Println("✓")
		} else {
			fmt.Println("✗")
		}
	}
}
