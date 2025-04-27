// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_global

import (
	"strings"
)

// cmpDecimalStrings compares two decimal number strings with sign support
func cmpDecimalStrings(a, b string) int {
	aNegative := strings.HasPrefix(a, "-")
	bNegative := strings.HasPrefix(b, "-")

	// Different signs cases
	if aNegative && !bNegative {
		return -1
	}
	if !aNegative && bNegative {
		return 1
	}

	// Both negative or both positive - compare absolute values
	aAbs := a
	if aNegative {
		aAbs = a[1:]
	}
	bAbs := b
	if bNegative {
		bAbs = b[1:]
	}

	cmp := compareAbsoluteValues(aAbs, bAbs)

	// If both were negative, reverse the comparison result
	if aNegative && bNegative {
		return -cmp
	}
	return cmp
}

// compareAbsoluteValues compares absolute values of two decimal strings
func compareAbsoluteValues(a, b string) int {
	aInt, aFrac := splitNumber(a)
	bInt, bFrac := splitNumber(b)

	// Compare integer parts
	cmpInt := compareIntegerParts(aInt, bInt)
	if cmpInt != 0 {
		return cmpInt
	}

	// Compare fractional parts if integer parts are equal
	return compareFractionalParts(aFrac, bFrac)
}

func splitNumber(s string) (intPart, fracPart string) {
	parts := strings.Split(s, ".")
	switch len(parts) {
	case 1:
		return parts[0], ""
	case 2:
		return parts[0], parts[1]
	default:
		return "", ""
	}
}

func compareIntegerParts(a, b string) int {
	// Remove leading zeros except for single zero
	a = strings.TrimLeft(a, "0")
	if a == "" {
		a = "0"
	}
	b = strings.TrimLeft(b, "0")
	if b == "" {
		b = "0"
	}

	// Compare lengths
	if len(a) > len(b) {
		return 1
	}
	if len(a) < len(b) {
		return -1
	}

	// Compare digit by digit
	for i := 0; i < len(a); i++ {
		if a[i] > b[i] {
			return 1
		}
		if a[i] < b[i] {
			return -1
		}
	}
	return 0
}

func compareFractionalParts(a, b string) int {
	maxLen := max(len(a), len(b))
	for i := 0; i < maxLen; i++ {
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
	return 0
}

func IsNumLitStr(s string) bool {
	if s == "" {
		return false
	}

	// Check for optional sign
	if strings.HasPrefix(s, "-") || strings.HasPrefix(s, "+") {
		s = s[1:]
	}

	hasDigit := false
	hasDot := false

	for _, c := range s {
		switch {
		case c >= '0' && c <= '9':
			hasDigit = true
		case c == '.':
			if hasDot {
				return false // Multiple dots
			}
			hasDot = true
		default:
			return false // Invalid character
		}
	}

	return hasDigit
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}
