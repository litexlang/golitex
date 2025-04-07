package litexcomparator

import (
	"errors"
	"fmt"
	glob "golitex/litex_global"
	st "golitex/litex_statements"
	"strconv"
	"strings"
)

type NumberFc struct {
	Left        *NumberFc
	OptOrNumber string
	Right       *NumberFc
}

func IsNumberFcWithBuiltinInfixOpt(fc st.Fc) (*NumberFc, bool, error) {
	asStr, ok := st.IsNumberAtom(fc)
	if ok {
		return &NumberFc{nil, asStr, nil}, true, nil
	}

	asFcFn, ok := fc.(*st.FcFnPipe)
	if !ok {
		return nil, false, fmt.Errorf("")
	}

	opt := asFcFn.FnHead.Value
	if !glob.IsBuiltinRelaFn(opt) {
		return nil, false, nil
	}

	if len(asFcFn.CallPipe) != 1 {
		return nil, false, nil
	}

	if len(asFcFn.CallPipe[0].Params) != 2 {
		return nil, false, nil
	}

	left, ok, err := IsNumberFcWithBuiltinInfixOpt(asFcFn.CallPipe[0].Params[0])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	right, ok, err := IsNumberFcWithBuiltinInfixOpt(asFcFn.CallPipe[0].Params[1])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	return &NumberFc{left, opt, right}, true, nil
}

// EvaluateNumberFc 计算表达式树，返回字符串形式的结果。如果发现不符合规定，返回错误
func EvaluateNumberFc(node *NumberFc) (string, error) {
	// 叶子节点
	if node.Left == nil && node.Right == nil {
		return node.OptOrNumber, nil
	}

	leftVal, err := EvaluateNumberFc(node.Left)
	if err != nil {
		return "", err
	}

	rightVal, err := EvaluateNumberFc(node.Right)
	if err != nil {
		return "", err
	}

	switch node.OptOrNumber {
	case "+":
		return addBigFloat(leftVal, rightVal)
	case "-":
		return subBigFloat(leftVal, rightVal)
	case "*":
		return mulBigFloat(leftVal, rightVal)
	case "/":
		return divBigFloat(leftVal, rightVal)
	case "^":
		if !isNaturalNumber(rightVal) {
			return "", errors.New("exponent must be a natural number")
		}
		return powBigFloat(leftVal, rightVal)
	default:
		return "", fmt.Errorf("未知运算符: %s", node.OptOrNumber)
	}
}

func addBigFloat(a, b string) (string, error) {
	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// 对齐小数部分长度
	maxFracLen := max(len(aFrac), len(bFrac))
	aFrac = padRight(aFrac, maxFracLen, '0')
	bFrac = padRight(bFrac, maxFracLen, '0')

	// 小数部分相加
	fracSum, carry, err := addStrings(aFrac, bFrac, false)
	if err != nil {
		return "", err
	}

	// 去除末尾的0（小数部分）
	fracSum = strings.TrimRight(fracSum, "0")

	// 整数部分对齐
	maxIntLen := max(len(aInt), len(bInt))
	aInt = padLeft(aInt, maxIntLen, '0')
	bInt = padLeft(bInt, maxIntLen, '0')

	// 整数部分相加
	intSum, carry, err := addStrings(aInt, bInt, carry)
	if err != nil {
		return "", err
	}
	if carry {
		intSum = "1" + intSum
	}

	result := intSum
	if len(fracSum) > 0 {
		result += "." + fracSum
	}

	return result, nil
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
func subBigFloat(a, b string) (string, error) {
	cmp := CompareBigFloat(a, b)
	if cmp == -1 {
		return "", errors.New("暂不支持负数")
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
		return "", err
	}

	// 整数部分减（带借位）
	intRes, _, err := subStrings(aInt, bInt, borrow)
	if err != nil {
		return "", err
	}

	intRes = trimLeftZero(intRes)
	if intRes == "" {
		intRes = "0"
	}

	if fracRes != "" {
		fracRes = strings.TrimRight(fracRes, "0")
		if fracRes != "" {
			return intRes + "." + fracRes, nil
		}
	}
	return intRes, nil
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
func mulBigFloat(a, b string) (string, error) {
	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// 先拼接成整数
	aTotal := aInt + aFrac
	bTotal := bInt + bFrac

	fracLen := len(aFrac) + len(bFrac)

	// 乘法
	product, err := mulStrings(aTotal, bTotal)
	if err != nil {
		return "", err
	}

	if fracLen > 0 {
		if len(product) <= fracLen {
			product = padLeft(product, fracLen+1, '0')
		}
		intPart := product[:len(product)-fracLen]
		fracPart := product[len(product)-fracLen:]
		fracPart = strings.TrimRight(fracPart, "0")
		if fracPart == "" {
			return trimLeftZero(intPart), nil
		}
		return trimLeftZero(intPart) + "." + fracPart, nil
	}
	return trimLeftZero(product), nil
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
func powBigFloat(a, b string) (string, error) {
	res := "1"
	cnt, err := toInt(b)
	if err != nil {
		return "", err
	}

	for i := 0; i < cnt; i++ {
		res, err = mulBigFloat(res, a)
		if err != nil {
			return "", err
		}
		if len(res) > 200 {
			return "", errors.New("powBigFloat: result too long")
		}
	}
	return res, nil
}

func toInt(s string) (int, error) {
	s = strings.TrimSpace(s)
	s = trimLeftZero(s)

	if s == "" {
		return 0, errors.New("toInt: empty string")
	}

	if strings.Contains(s, ".") {
		return 0, errors.New("toInt: float value not allowed")
	}

	val, err := strconv.Atoi(s)
	if err != nil {
		return 0, errors.New("toInt: invalid number")
	}

	return val, nil
}

// divBigFloat 大数除法，a除以b，如果能整除则返回精确结果，否则返回错误
func divBigFloat(a, b string) (string, error) {
	// 检查除数是否为0
	if b == "0" || b == "0.0" {
		return "", errors.New("division by zero")
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
		return "", err
	}

	// 检查是否能整除（余数为0）
	if !isZero(remainder) {
		return "", nil
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
			return intPart + "." + fracPart, nil
		}
		return intPart, nil
	} else if fracLenDiff < 0 {
		// 需要在结果末尾补0
		return result + strings.Repeat("0", -fracLenDiff), nil
	}
	return result, nil
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
