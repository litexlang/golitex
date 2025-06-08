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
// Litex zulip chat: https://litex.zulipchat.com/

package litex_global

import (
	"errors"
	"fmt"
	"strings"
)

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

// func max(a, b int) int {
// 	if a > b {
// 		return a
// 	}
// 	return b
// }

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

// subBigFloat handles subtraction with proper sign consideration
func subBigFloat(a, b string) (string, bool, error) {
	// Handle sign combinations
	aNegative := strings.HasPrefix(a, "-")
	bNegative := strings.HasPrefix(b, "-")

	// Case 1: Both positive - normal subtraction
	if !aNegative && !bNegative {
		return subtractPositiveNumbers(a, b)
	}

	// Case 2: Both negative - (-a) - (-b) = -a + b = b - a
	if aNegative && bNegative {
		return subtractPositiveNumbers(b[1:], a[1:])
	}

	// Case 3: First negative, second positive - (-a) - b = -(a + b)
	if aNegative {
		sum, ok, err := addBigFloat(a[1:], b)
		if err != nil || !ok {
			return "", ok, err
		}
		return "-" + sum, true, nil
	}

	// Case 4: First positive, second negative - a - (-b) = a + b
	return addBigFloat(a, b[1:])
}

// Helper function for subtracting two positive numbers (a >= b)
func subtractPositiveNumbers(a, b string) (string, bool, error) {
	cmp := cmpBigFloat(a, b)

	// Handle a < b case by swapping and making result negative
	if cmp == -1 {
		result, ok, err := subtractPositiveNumbers(b, a)
		if err != nil || !ok {
			return "", ok, err
		}
		return "-" + result, true, nil
	}

	aInt, aFrac := splitNumberToIntPartFracPart(a)
	bInt, bFrac := splitNumberToIntPartFracPart(b)

	// Align fractional parts
	maxFracLen := max(len(aFrac), len(bFrac))
	aFrac = padRight(aFrac, maxFracLen, '0')
	bFrac = padRight(bFrac, maxFracLen, '0')

	// Subtract fractional parts
	fracRes, borrow, err := subStrings(aFrac, bFrac, false)
	if err != nil {
		return "", false, err
	}

	// Subtract integer parts (with borrow)
	intRes, _, err := subStrings(aInt, bInt, borrow)
	if err != nil {
		return "", false, err
	}

	// Clean up result
	intRes = trimLeftZero(intRes)
	if intRes == "" {
		intRes = "0"
	}

	fracRes = strings.TrimRight(fracRes, "0")
	if fracRes != "" {
		return intRes + "." + fracRes, true, nil
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

// mulBigFloat handles multiplication with proper sign consideration
func mulBigFloat(a, b string) (string, bool, error) {
	// Handle sign combinations
	aNegative := strings.HasPrefix(a, "-")
	bNegative := strings.HasPrefix(b, "-")

	// Work with absolute values
	aAbs := a
	if aNegative {
		aAbs = a[1:]
	}
	bAbs := b
	if bNegative {
		bAbs = b[1:]
	}

	// Split into integer and fractional parts
	aInt, aFrac := splitNumberToIntPartFracPart(aAbs)
	bInt, bFrac := splitNumberToIntPartFracPart(bAbs)

	// Combine into single numbers (removing decimal points)
	aTotal := aInt + aFrac
	bTotal := bInt + bFrac

	// Calculate total fractional digits
	fracLen := len(aFrac) + len(bFrac)

	// Perform multiplication
	product, err := mulStrings(aTotal, bTotal)
	if err != nil {
		return "", false, err
	}

	// Handle decimal point placement
	if fracLen > 0 {
		if len(product) <= fracLen {
			product = padLeft(product, fracLen+1, '0')
		}
		intPart := product[:len(product)-fracLen]
		fracPart := product[len(product)-fracLen:]
		fracPart = strings.TrimRight(fracPart, "0")
		product = trimLeftZero(intPart)
		if fracPart != "" {
			product += "." + fracPart
		}
	} else {
		product = trimLeftZero(product)
	}

	// Determine result sign (negative if exactly one operand was negative)
	if (aNegative && !bNegative) || (!aNegative && bNegative) {
		// Only make negative if result isn't zero
		if product != "0" {
			product = "-" + product
		}
	}

	return product, true, nil
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

// cmpBigFloat compares two big float numbers considering their signs
// Returns: 1 if a > b, -1 if a < b, 0 if a == b
func cmpBigFloat(a, b string) int {
	// Handle sign comparison first
	aNegative := strings.HasPrefix(a, "-")
	bNegative := strings.HasPrefix(b, "-")

	// Different signs cases
	if aNegative && !bNegative {
		return -1
	}
	if !aNegative && bNegative {
		return 1
	}

	// Both negative or both positive
	aAbs := a
	if aNegative {
		aAbs = a[1:]
	}
	bAbs := b
	if bNegative {
		bAbs = b[1:]
	}

	// Compare absolute values
	cmp := compareAbsoluteValues(aAbs, bAbs)

	// If both were negative, reverse the comparison result
	if aNegative && bNegative {
		return -cmp
	}
	return cmp
}

// // compareAbsoluteValues compares the absolute values of two numbers
// func compareAbsoluteValues(a, b string) int {
// 	aInt, aFrac := splitNumberToIntPartFracPart(a)
// 	bInt, bFrac := splitNumberToIntPartFracPart(b)

// 	aInt = trimLeftZero(aInt)
// 	bInt = trimLeftZero(bInt)

// 	// Compare integer part lengths
// 	if len(aInt) > len(bInt) {
// 		return 1
// 	}
// 	if len(aInt) < len(bInt) {
// 		return -1
// 	}

// 	// Compare integer parts digit by digit
// 	if aInt > bInt {
// 		return 1
// 	}
// 	if aInt < bInt {
// 		return -1
// 	}

// 	// Compare fractional parts
// 	maxLen := max(len(aFrac), len(bFrac))
// 	aFrac = padRight(aFrac, maxLen, '0')
// 	bFrac = padRight(bFrac, maxLen, '0')

// 	if aFrac > bFrac {
// 		return 1
// 	}
// 	if aFrac < bFrac {
// 		return -1
// 	}
// 	return 0
// }

// isNaturalNumber checks if a string represents a natural number (including 0)
func isNaturalNumber(s string) bool {
	// Handle negative numbers
	if strings.HasPrefix(s, "-") {
		return false
	}

	// Remove leading zeros and check for empty string
	s = trimLeftZero(s)
	if s == "" {
		return false
	}

	// Check for decimal point
	if strings.Contains(s, ".") {
		return false
	}

	// Check all characters are digits
	for _, ch := range s {
		if ch < '0' || ch > '9' {
			return false
		}
	}

	return true
}

// powBigFloat calculates a^b where b must be a natural number (handles signs)
func powBigFloat(a, b string) (string, bool, error) {
	// Handle sign of base
	aNegative := strings.HasPrefix(a, "-")
	aAbs := a
	if aNegative {
		aAbs = a[1:]
	}

	// Parse exponent (already validated as natural number)
	exponent, err := parseNaturalNumber(b)
	if err != nil {
		return "", false, fmt.Errorf("invalid exponent: %v", err)
	}

	// Handle special cases
	if exponent == 0 {
		return "1", true, nil // x^0 = 1 for any x
	}
	if aAbs == "0" || aAbs == "0.0" {
		return "0", true, nil // 0^n = 0
	}

	result := "1"
	for i := 0; i < exponent; i++ {
		var ok bool
		result, ok, err = mulBigFloat(result, aAbs)
		if err != nil {
			return "", false, fmt.Errorf("multiplication error: %v", err)
		}
		if !ok {
			return "", false, nil
		}
		if len(result) > 200 {
			return "", false, errors.New("result exceeds 200 digits")
		}
	}

	// Apply sign (negative if base was negative and exponent is odd)
	if aNegative && exponent%2 == 1 {
		result = "-" + result
	}

	return result, true, nil
}

// parseNaturalNumber validates and parses a natural number string
func parseNaturalNumber(s string) (int, error) {
	s = strings.TrimSpace(s)
	s = trimLeftZero(s)

	if s == "" {
		return 0, errors.New("empty string")
	}

	// Check for non-digit characters
	for _, c := range s {
		if c < '0' || c > '9' {
			return 0, fmt.Errorf("invalid character '%c'", c)
		}
	}

	// Parse with overflow check
	var num int
	for _, c := range s {
		digit := int(c - '0')
		if num > (1<<31-1-digit)/10 { // Check for 32-bit overflow
			return 0, errors.New("number too large")
		}
		num = num*10 + digit
	}

	return num, nil
}

// divBigFloat performs exact division (returns error if not divisible)
func divBigFloat(a, b string) (string, bool, error) {
	// Handle signs
	aNegative := strings.HasPrefix(a, "-")
	bNegative := strings.HasPrefix(b, "-")
	aAbs := a
	if aNegative {
		aAbs = a[1:]
	}
	bAbs := b
	if bNegative {
		bAbs = b[1:]
	}

	// Check for division by zero
	if isZero(bAbs) {
		return "", false, errors.New("division by zero")
	}

	// Convert to integer representation
	aInt, aFrac := splitNumberToIntPartFracPart(aAbs)
	bInt, bFrac := splitNumberToIntPartFracPart(bAbs)
	aTotal := aInt + aFrac
	bTotal := bInt + bFrac
	fracLenDiff := len(aFrac) - len(bFrac)

	// Normalize lengths
	maxLen := max(len(aTotal), len(bTotal))
	aTotal = padLeft(aTotal, maxLen, '0')
	bTotal = padLeft(bTotal, maxLen, '0')

	// Perform division
	quotient, remainder, err := longDivision(aTotal, bTotal)
	if err != nil {
		return "", false, fmt.Errorf("division error: %v", err)
	}

	// Check for exact division
	if !isZero(remainder) {
		return "", false, nil
	}

	// Handle decimal point placement
	if fracLenDiff > 0 {
		if len(quotient) <= fracLenDiff {
			quotient = padLeft(quotient, fracLenDiff+1, '0')
		}
		intPart := quotient[:len(quotient)-fracLenDiff]
		fracPart := strings.TrimRight(quotient[len(quotient)-fracLenDiff:], "0")
		if len(fracPart) > 0 {
			quotient = intPart + "." + fracPart
		} else {
			quotient = intPart
		}
	} else if fracLenDiff < 0 {
		quotient += strings.Repeat("0", -fracLenDiff)
	}

	// Apply sign (negative if signs differ)
	if (aNegative && !bNegative) || (!aNegative && bNegative) {
		quotient = "-" + quotient
	}

	return quotient, true, nil
}

// longDivision performs the actual division algorithm
func longDivision(dividend, divisor string) (string, string, error) {
	if len(dividend) < len(divisor) {
		return "0", dividend, nil
	}

	var quotient strings.Builder
	remainder := dividend[:len(divisor)]
	dividend = dividend[len(divisor):]

	for {
		// Find current digit (0-9)
		digit := 0
		currentRem := remainder
		for digit < 9 {
			subRes, borrow, err := subStrings(currentRem, divisor, false)
			if err != nil {
				return "", "", err
			}
			if borrow {
				break
			}
			currentRem = subRes
			digit++
		}

		quotient.WriteByte(byte(digit) + '0')
		remainder = currentRem

		if len(dividend) == 0 {
			break
		}

		remainder += string(dividend[0])
		dividend = dividend[1:]
	}

	// Clean up results
	q := strings.TrimLeft(quotient.String(), "0")
	if q == "" {
		q = "0"
	}
	r := strings.TrimLeft(remainder, "0")
	if r == "" {
		r = "0"
	}

	return q, r, nil
}

// isZero checks if a number string represents zero
func isZero(s string) bool {
	// Handle negative numbers
	s = strings.TrimLeft(s, "-")

	// Check if all remaining characters are zeros or decimal points
	for _, c := range s {
		if c != '0' && c != '.' {
			return false
		}
	}
	return true
}

// modBigFloat performs modulo operation (a % b) for integers only
func modBigFloat(a, b string) (string, bool, error) {
	// Handle signs
	aNegative := strings.HasPrefix(a, "-")
	bNegative := strings.HasPrefix(b, "-")
	aAbs := a
	if aNegative {
		aAbs = a[1:]
	}
	bAbs := b
	if bNegative {
		bAbs = b[1:]
	}

	// Check for division by zero
	if isZero(bAbs) {
		return "", false, errors.New("modulo by zero")
	}

	// Check if numbers are integers
	aInt, aFrac := splitNumberToIntPartFracPart(aAbs)
	bInt, bFrac := splitNumberToIntPartFracPart(bAbs)

	if aFrac != "" || bFrac != "" {
		return "", false, errors.New("modulo operation only supports integers")
	}

	// Normalize lengths for long division
	maxLen := max(len(aInt), len(bInt))
	aTotal := padLeft(aInt, maxLen, '0')
	bTotal := padLeft(bInt, maxLen, '0')

	// Perform long division to get remainder
	_, remainder, err := longDivision(aTotal, bTotal)
	if err != nil {
		return "", false, fmt.Errorf("modulo error: %v", err)
	}

	// Clean up remainder (remove leading zeros)
	remainder = trimLeftZero(remainder)
	if remainder == "" {
		remainder = "0"
	}

	// Handle sign of the result:
	// 1. If remainder is 0, sign doesn't matter (return "0")
	// 2. If remainder is non-zero:
	//    - If b is positive, result has same sign as a.
	//    - If b is negative, result has opposite sign of a.
	if remainder != "0" {
		if bNegative {
			// b is negative → result sign is opposite of a
			if aNegative {
				// a is negative → result is positive
				remainder = "-" + remainder
			} else {
				// a is positive → result is negative
				remainder = "-" + remainder
				var ok bool = false
				remainder, ok, err = addBigFloat(remainder, bAbs)
				if err != nil {
					return "", false, fmt.Errorf("modulo adjustment error: %v", err)
				}
				if !ok {
					return "", false, nil
				}
				remainder = "-" + remainder
			}
		} else {
			// b is positive → result sign matches a
			if aNegative {
				// a is negative → result is negative
				remainder = "-" + remainder
				var ok bool = false
				remainder, ok, err = addBigFloat(remainder, bAbs)
				if err != nil {
					return "", false, fmt.Errorf("modulo adjustment error: %v", err)
				}
				if !ok {
					return "", false, nil
				}
			}
		}
	}

	return remainder, true, nil
}
