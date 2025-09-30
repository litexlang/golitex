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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

// This file reads in two decimals represented as strings and returns a decimal as a string (in simplified format). The computation here is completely accurate.

package litex_num

import (
	"strings"
)

// 移除前导零
func stripZero(s string) string {
	if s == "" {
		return "0"
	}
	i := 0
	for i < len(s)-1 && s[i] == '0' {
		i++
	}
	result := s[i:]
	if result == "" {
		return "0"
	}
	return result
}

// 字符串大整数加法
func addIntStrings(a, b string) string {
	i, j := len(a)-1, len(b)-1
	carry := 0
	var res []byte

	for i >= 0 || j >= 0 || carry > 0 {
		sum := carry
		if i >= 0 {
			sum += int(a[i] - '0')
			i--
		}
		if j >= 0 {
			sum += int(b[j] - '0')
			j--
		}
		res = append(res, byte(sum%10)+'0')
		carry = sum / 10
	}
	// 翻转
	for i, n := 0, len(res); i < n/2; i++ {
		res[i], res[n-1-i] = res[n-1-i], res[i]
	}
	return string(res)
}

// 字符串大整数减法 (假设 a>=b)
func subIntStrings(a, b string) string {
	i, j := len(a)-1, len(b)-1
	borrow := 0
	var res []byte

	for i >= 0 {
		diff := int(a[i]-'0') - borrow
		if j >= 0 {
			diff -= int(b[j] - '0')
			j--
		}
		if diff < 0 {
			diff += 10
			borrow = 1
		} else {
			borrow = 0
		}
		res = append(res, byte(diff)+'0')
		i--
	}
	// 翻转并去掉前导零
	for i, n := 0, len(res); i < n/2; i++ {
		res[i], res[n-1-i] = res[n-1-i], res[i]
	}
	return stripZero(string(res))
}

// 字符串大整数乘法
func mulIntStrings(a, b string) string {
	m, n := len(a), len(b)
	prod := make([]int, m+n)

	for i := m - 1; i >= 0; i-- {
		for j := n - 1; j >= 0; j-- {
			prod[i+j+1] += int((a[i] - '0') * (b[j] - '0'))
		}
	}

	// 处理进位
	for i := m + n - 1; i > 0; i-- {
		if prod[i] >= 10 {
			prod[i-1] += prod[i] / 10
			prod[i] %= 10
		}
	}

	// 转成字符串
	var sb strings.Builder
	for i, v := range prod {
		if i == 0 && v == 0 {
			continue
		}
		sb.WriteByte(byte(v) + '0')
	}
	return stripZero(sb.String())
}

// 去掉小数点右侧多余零
func stripDecimal(s string) string {
	if !strings.Contains(s, ".") {
		return s
	}
	s = strings.TrimRight(s, "0")  // 去掉右边零
	s = strings.TrimSuffix(s, ".") // 去掉末尾的小数点
	if s == "" {
		return "0"
	}
	return s
}

// 统一小数点表示: 返回 (纯整数, scale)
func normalizeDecimal(s string) (string, int) {
	if !strings.Contains(s, ".") {
		return stripZero(s), 0
	}
	parts := strings.Split(s, ".")
	intPart := stripZero(parts[0])
	fracPart := parts[1]
	fracPart = strings.TrimRight(fracPart, "0")
	scale := len(fracPart)
	if scale == 0 {
		return intPart, 0
	}
	// 确保整数部分不为空
	if intPart == "" {
		intPart = "0"
	}
	// 如果整数部分是"0"，直接返回小数部分
	if intPart == "0" {
		return fracPart, scale
	}
	return intPart + fracPart, scale
}

// 加法 (支持小数)
func AddDecimalStr(a, b string) string {
	// 处理负号
	aNegative := strings.HasPrefix(a, "-")
	bNegative := strings.HasPrefix(b, "-")

	// 去掉负号
	if aNegative {
		a = a[1:]
	}
	if bNegative {
		b = b[1:]
	}

	ai, as := normalizeDecimal(a)
	bi, bs := normalizeDecimal(b)

	// 对齐小数位
	if as > bs {
		bi += strings.Repeat("0", as-bs)
		bs = as
	} else if bs > as {
		ai += strings.Repeat("0", bs-as)
		as = bs
	}

	var result string
	var isNegative bool

	// 根据符号决定是加法还是减法
	if aNegative == bNegative {
		// 同号相加
		sum := addIntStrings(ai, bi)
		if as > 0 {
			pointPos := len(sum) - as
			if pointPos <= 0 {
				sum = strings.Repeat("0", -pointPos+1) + sum
				pointPos = 1
			}
			sum = sum[:pointPos] + "." + sum[pointPos:]
		}
		result = sum
		isNegative = aNegative
	} else {
		// 异号相减
		if compareStrings(ai, bi) {
			result = subIntStrings(ai, bi)
			isNegative = aNegative
		} else {
			result = subIntStrings(bi, ai)
			isNegative = bNegative
		}

		// 添加小数点
		if as > 0 {
			pointPos := len(result) - as
			if pointPos <= 0 {
				result = strings.Repeat("0", -pointPos+1) + result
				pointPos = 1
			}
			result = result[:pointPos] + "." + result[pointPos:]
		}
	}

	// 添加负号
	if isNegative {
		result = "-" + result
	}

	return stripDecimal(result)
}

// 比较两个字符串数字的大小，返回 true 如果 a >= b
func compareStrings(a, b string) bool {
	// 先去掉前导零
	a = stripZero(a)
	b = stripZero(b)

	// 比较长度
	if len(a) > len(b) {
		return true
	}
	if len(a) < len(b) {
		return false
	}

	// 长度相等，逐位比较
	return a >= b
}

// 减法 (支持小数)
func SubDecimalStr(a, b string) string {
	ai, as := normalizeDecimal(a)
	bi, bs := normalizeDecimal(b)

	// 对齐小数位
	if as > bs {
		bi += strings.Repeat("0", as-bs)
		bs = as
	} else if bs > as {
		ai += strings.Repeat("0", bs-as)
		as = bs
	}

	var result string
	var isNegative bool

	// 比较大小决定符号
	if compareStrings(ai, bi) {
		result = subIntStrings(ai, bi)
		isNegative = false
	} else {
		result = subIntStrings(bi, ai)
		isNegative = true
	}

	// 如果结果是0，直接返回"0"
	if result == "0" {
		return "0"
	}

	// 添加小数点
	if as > 0 {
		pointPos := len(result) - as
		if pointPos <= 0 {
			result = strings.Repeat("0", -pointPos+1) + result
			pointPos = 1
		}
		result = result[:pointPos] + "." + result[pointPos:]
	}

	// 添加负号
	if isNegative {
		result = "-" + result
	}

	return stripDecimal(result)
}

// 乘法 (支持小数)
func MulDecimalStr(a, b string) string {
	// 处理负号
	aNegative := strings.HasPrefix(a, "-")
	bNegative := strings.HasPrefix(b, "-")

	// 去掉负号
	if aNegative {
		a = a[1:]
	}
	if bNegative {
		b = b[1:]
	}

	ai, as := normalizeDecimal(a)
	bi, bs := normalizeDecimal(b)

	prod := mulIntStrings(ai, bi)
	scale := as + bs
	if scale > 0 {
		pointPos := len(prod) - scale
		if pointPos <= 0 {
			prod = strings.Repeat("0", -pointPos+1) + prod
			pointPos = 1
		}
		prod = prod[:pointPos] + "." + prod[pointPos:]
	}

	// 添加负号（如果只有一个数是负数）
	if aNegative != bNegative {
		prod = "-" + prod
	}

	return stripDecimal(prod)
}
