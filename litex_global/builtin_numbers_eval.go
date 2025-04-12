package litex_global

import (
	"errors"
	"fmt"
	"strings"
)

type NumLitExpr struct {
	IsPositive  bool
	Left        *NumLitExpr
	OptOrNumber string
	Right       *NumLitExpr
}

// EvalNumLitExprFc 计算表达式树，返回字符串形式的结果。如果发现不符合规定，返回错误
// bool 表示基于现有的litex-rule，虽然说我不能说你对不对，但你至少没犯错，error表示你犯错了，比如1/0
func EvalNumLitExprFc(node *NumLitExpr) (string, bool, error) {
	// Leaf node
	if node.Left == nil && node.Right == nil {
		value := node.OptOrNumber
		if !node.IsPositive {
			value = "-" + value
		}
		return value, true, nil
	}

	leftVal, ok, err := EvalNumLitExprFc(node.Left)
	if err != nil {
		return "", false, err
	}
	if !ok {
		return "", false, nil
	}

	rightVal, ok, err := EvalNumLitExprFc(node.Right)
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

func addBigFloat(a, b string) (string, bool, error) {
	// Handle sign combinations
	aNegative := strings.HasPrefix(a, "-")
	bNegative := strings.HasPrefix(b, "-")

	// Case 1: Both positive - normal addition
	if !aNegative && !bNegative {
		return addPositiveNumbers(a, b)
	}

	// Case 2: Both negative - add absolute values and make negative
	if aNegative && bNegative {
		result, ok, err := addPositiveNumbers(a[1:], b[1:])
		if err != nil {
			return "", false, err
		}
		if !ok {
			return "", false, nil
		}
		return "-" + result, true, nil
	}

	// Case 3: One negative, one positive - convert to subtraction
	if aNegative {
		return subBigFloat(b, a[1:])
	}
	// bNegative
	return subBigFloat(a, b[1:])
}

// Helper function for adding two positive numbers
func addPositiveNumbers(a, b string) (string, bool, error) {
	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// Align fractional parts
	maxFracLen := max(len(aFrac), len(bFrac))
	aFrac = padRight(aFrac, maxFracLen, '0')
	bFrac = padRight(bFrac, maxFracLen, '0')

	// Add fractional parts
	fracSum, carry, err := addStrings(aFrac, bFrac, false)
	if err != nil {
		return "", false, err
	}

	// Trim trailing zeros from fractional part
	fracSum = strings.TrimRight(fracSum, "0")

	// Align integer parts
	maxIntLen := max(len(aInt), len(bInt))
	aInt = padLeft(aInt, maxIntLen, '0')
	bInt = padLeft(bInt, maxIntLen, '0')

	// Add integer parts
	intSum, carry, err := addStrings(aInt, bInt, carry)
	if err != nil {
		return "", false, err
	}
	if carry {
		intSum = "1" + intSum
	}

	// Construct result
	result := intSum
	if len(fracSum) > 0 {
		result += "." + fracSum
	}

	return result, true, nil
}

func splitNumberToIntPartFracPart(s string) (string, string) {
	parts := strings.Split(s, ".")
	if len(parts) == 1 {
		return parts[0], ""
	}
	return parts[0], parts[1]
}

func addStrings(a, b string, carry bool) (string, bool, error) {
	if len(a) != len(b) {
		return "", false, errors.New("addStrings length mismatch")
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

	return string(result), c > 0, nil
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

// 字符串大数减法
func subBigFloat(a, b string) (string, bool, error) {
	cmp := CmpBigFloat(a, b)
	if cmp == -1 {
		// TODO "暂不支持负数"
		return "", false, nil
	}

	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// 补齐小数部分长度
	maxFracLen := max(len(aFrac), len(bFrac))
	aFrac = padRight(aFrac, maxFracLen, '0')
	bFrac = padRight(bFrac, maxFracLen, '0')

	// 小数部分先减
	fracRes, borrow, err := subStrings(aFrac, bFrac, false)
	if err != nil {
		return "", false, err
	}

	// 整数部分减（带借位）
	intRes, _, err := subStrings(aInt, bInt, borrow)
	if err != nil {
		return "", false, err
	}

	intRes = trimLeftZero(intRes)
	if intRes == "" {
		intRes = "0"
	}

	if fracRes != "" {
		fracRes = strings.TrimRight(fracRes, "0")
		if fracRes != "" {
			return intRes + "." + fracRes, true, nil
		}
	}
	return intRes, true, nil
}

// 字符串减法，a >= b
func subStrings(a, b string, borrow bool) (string, bool, error) {
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

	return string(res), curBorrow > 0, nil
}

// 大数乘法
func mulBigFloat(a, b string) (string, bool, error) {
	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// 先拼接成整数
	aTotal := aInt + aFrac
	bTotal := bInt + bFrac

	fracLen := len(aFrac) + len(bFrac)

	// 乘法
	product, err := mulStrings(aTotal, bTotal)
	if err != nil {
		return "", false, err
	}

	if fracLen > 0 {
		if len(product) <= fracLen {
			product = padLeft(product, fracLen+1, '0')
		}
		intPart := product[:len(product)-fracLen]
		fracPart := product[len(product)-fracLen:]
		fracPart = strings.TrimRight(fracPart, "0")
		if fracPart == "" {
			return trimLeftZero(intPart), true, nil
		}
		return trimLeftZero(intPart) + "." + fracPart, true, nil
	}
	return trimLeftZero(product), true, nil
}

// 字符串乘法
func mulStrings(a, b string) (string, error) {
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
		return "0", nil
	}
	return sb.String(), nil
}

// 判断大小：返回 1 if a > b, -1 if a < b, 0 if a==b
func CmpBigFloat(a, b string) int {
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

// 判断是不是自然数（包含0）
func isNaturalNumber(s string) bool {
	// 去掉前导0
	s = trimLeftZero(s)
	// 允许 "0"
	if s == "0" {
		return true
	}
	// 必须是纯数字且没有小数点
	for _, ch := range s {
		if ch < '0' || ch > '9' {
			return false
		}
	}
	return true
}

// a^b, 其中 b 必须是自然数（已经在外层判断过）
// 结果长度不超过 200 位（超过返回错误）
func powBigFloat(a, b string) (string, bool, error) {
	res := "1"
	cnt, err := parseNaturalNumber(b)
	if err != nil {
		return "", false, err
	}

	for i := 0; i < cnt; i++ {
		var ok bool
		res, ok, err = mulBigFloat(res, a)
		if err != nil {
			return "", false, err
		}
		if !ok {
			return "", false, nil
		}
		if len(res) > 200 {
			return "", false, errors.New("powBigFloat: result too long")
		}
	}
	return res, true, nil
}

// parseNaturalNumber 手动解析自然数（不含前导零，不含小数点）
func parseNaturalNumber(s string) (int, error) {
	s = strings.TrimSpace(s)
	s = trimLeftZero(s)

	if s == "" {
		return 0, errors.New("parseNaturalNumber: empty string")
	}

	if strings.Contains(s, ".") {
		return 0, errors.New("parseNaturalNumber: float value not allowed")
	}

	// 检查是否全是数字字符
	for _, c := range s {
		if c < '0' || c > '9' {
			return 0, errors.New("parseNaturalNumber: invalid number")
		}
	}

	// 手动计算数值
	var num int
	for _, c := range s {
		num = num*10 + int(c-'0')
		// 避免溢出（假设 int 是 32/64 位）
		if num < 0 {
			return 0, errors.New("parseNaturalNumber: number too large")
		}
	}

	return num, nil
}

// divBigFloat 大数除法，a除以b，如果能整除则返回精确结果，否则返回错误
func divBigFloat(a, b string) (string, bool, error) {
	// 检查除数是否为0
	if b == "0" || b == "0.0" {
		return "", false, errors.New("division by zero")
	}

	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// 将被除数和除数转为整数形式（去掉小数点）
	aTotal := aInt + aFrac
	bTotal := bInt + bFrac

	// 计算小数部分的长度差
	fracLenDiff := len(aFrac) - len(bFrac)

	// 补齐两个数的长度，使它们成为整数
	maxLen := max(len(aTotal), len(bTotal))
	aTotal = padLeft(aTotal, maxLen, '0')
	bTotal = padLeft(bTotal, maxLen, '0')

	// 执行长除法
	result, remainder, err := longDivision(aTotal, bTotal)
	if err != nil {
		return "", false, err
	}

	// 检查是否能整除（余数为0）
	if !isZero(remainder) {
		return "", false, nil
	}

	// 处理小数点的位置
	if fracLenDiff > 0 {
		// 需要在结果中插入小数点
		if len(result) <= fracLenDiff {
			result = padLeft(result, fracLenDiff+1, '0')
		}
		intPart := result[:len(result)-fracLenDiff]
		fracPart := result[len(result)-fracLenDiff:]
		fracPart = strings.TrimRight(fracPart, "0")
		if len(fracPart) > 0 {
			return intPart + "." + fracPart, true, nil
		}
		return intPart, true, nil
	} else if fracLenDiff < 0 {
		// 需要在结果末尾补0
		return result + strings.Repeat("0", -fracLenDiff), true, nil
	}
	return result, true, nil
}

// longDivision 执行长除法，返回商和余数
func longDivision(dividend, divisor string) (string, string, error) {
	if len(dividend) < len(divisor) {
		return "0", dividend, nil
	}

	var quotient strings.Builder
	remainder := dividend[:len(divisor)]
	dividend = dividend[len(divisor):]

	for {
		// 计算当前位的商
		digit := 0
		currentRem := remainder
		for ; digit < 9; digit++ {
			// 尝试减去divisor
			subRes, borrow, err := subStrings(currentRem, divisor, false)
			if err != nil {
				return "", "", err
			}
			if borrow {
				break
			}
			currentRem = subRes
		}
		quotient.WriteByte(byte(digit) + '0')

		// 更新余数
		remainder = currentRem

		// 如果被除数已经用完
		if len(dividend) == 0 {
			break
		}

		// 取下一位
		remainder += string(dividend[0])
		dividend = dividend[1:]
	}

	// 去除前导零
	q := strings.TrimLeft(quotient.String(), "0")
	if q == "" {
		q = "0"
	}

	// 去除余数的前导零
	r := strings.TrimLeft(remainder, "0")
	if r == "" {
		r = "0"
	}

	return q, r, nil
}

// isZero 检查字符串表示的数值是否为0
func isZero(s string) bool {
	for _, c := range s {
		if c != '0' {
			return false
		}
	}
	return true
}

// func BuiltinLogicOptRule() (bool, error) {

// 	switch expression {
// 	case condition:

// 	}
// }
