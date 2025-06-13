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

package litex_num

import (
	"fmt"
	"strings"
	"unicode"
)

type term struct {
	operator    string // + or -
	numerator   []string
	denominator string
}

func combineFractions(expr string) (string, string, error) {
	terms := splitTerms(expr)
	if len(terms) == 0 {
		return "", "", fmt.Errorf("invalid expression")
	}

	var parsed []term
	for _, t := range terms {
		pt, err := parseTerm(t)
		if err != nil {
			return "", "", err
		}
		parsed = append(parsed, pt)
	}

	// construct common denominator
	commonDenominator := "1"
	for _, t := range parsed {
		if t.denominator != "1" {
			commonDenominator = fmt.Sprintf("(%s*%s)", commonDenominator, t.denominator)
		}
	}

	// construct numerator
	numerator := ""
	for i, t := range parsed {
		termNumerator := strings.Join(t.numerator, "*")

		// 乘上其他分母
		for j, ot := range parsed {
			if i != j && ot.denominator != "1" {
				termNumerator = fmt.Sprintf("(%s*%s)", termNumerator, ot.denominator)
			}
		}

		if i == 0 {
			numerator = termNumerator
		} else {
			if t.operator == "+" {
				numerator = fmt.Sprintf("(%s + %s)", numerator, termNumerator)
			} else {
				numerator = fmt.Sprintf("(%s - %s)", numerator, termNumerator)
			}
		}
	}

	return numerator, commonDenominator, nil
}

func parseTerm(raw string) (term, error) {
	raw = strings.TrimSpace(raw)
	if raw == "" {
		return term{}, fmt.Errorf("empty term")
	}

	op := "+"
	if raw[0] == '+' || raw[0] == '-' {
		op = string(raw[0])
		raw = strings.TrimSpace(raw[1:])
	}

	// split multiplication terms
	muls := strings.Split(raw, "*")
	if len(muls) == 0 {
		return term{}, fmt.Errorf("invalid term: %s", raw)
	}

	num := []string{}
	den := "1"

	for _, m := range muls {
		m = strings.TrimSpace(m)
		if strings.Contains(m, "/") {
			parts := strings.Split(m, "/")
			if len(parts) != 2 {
				return term{}, fmt.Errorf("invalid fraction format: %s", m)
			}
			num = append(num, parts[0])
			den = fmt.Sprintf("%s*%s", den, parts[1])
		} else {
			num = append(num, m)
		}
	}

	// clean up denominator多余的 1
	if den == "1*1" || den == "1" {
		den = "1"
	}

	return term{
		operator:    op,
		numerator:   num,
		denominator: den,
	}, nil
}

func splitTerms(expr string) []string {
	var terms []string
	var currentTerm strings.Builder
	expr = strings.ReplaceAll(expr, " ", "")

	for i, ch := range expr {
		if (ch == '+' || ch == '-') && i != 0 && !isExponentialNotation(expr, i) {
			terms = append(terms, currentTerm.String())
			currentTerm.Reset()
			currentTerm.WriteRune(ch)
		} else {
			currentTerm.WriteRune(ch)
		}
	}

	if currentTerm.Len() > 0 {
		terms = append(terms, currentTerm.String())
	}

	return terms
}

func isExponentialNotation(expr string, pos int) bool {
	if pos < 1 || pos >= len(expr)-1 {
		return false
	}
	return (expr[pos] == '+' || expr[pos] == '-') &&
		unicode.ToLower(rune(expr[pos-1])) == 'e' &&
		unicode.IsDigit(rune(expr[pos+1]))
}
