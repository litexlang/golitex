package litex_num

import (
	"fmt"
	"strings"
	"unicode"
)

type term struct {
	operator    string   // + or -
	numerator   []string // 乘数组成的分子项
	denominator string   // 分母整体表达式
}

func CombineFractions(expr string) (string, string, error) {
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

	// 构造公共分母
	commonDenominator := "1"
	for _, t := range parsed {
		if t.denominator != "1" {
			commonDenominator = fmt.Sprintf("(%s*%s)", commonDenominator, t.denominator)
		}
	}

	// 构造分子
	numerator := ""
	for i, t := range parsed {
		termNumerator := strings.Join(t.numerator, "*")

		// 乘上其他项的分母
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

// 拆分表达式为各个项（支持 + 和 -，但忽略科学计数法中的 e-5）
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

// 解析每个 term，识别主层级的除法和乘法
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

	muls := splitMultiplicationPreservingNested(raw)
	if len(muls) == 0 {
		return term{}, fmt.Errorf("invalid term: %s", raw)
	}

	num := []string{}
	den := "1"

	for _, m := range muls {
		m = strings.TrimSpace(m)

		if slashIdx := findTopLevelSlash(m); slashIdx != -1 {
			left := strings.TrimSpace(m[:slashIdx])
			right := strings.TrimSpace(m[slashIdx+1:])
			num = append(num, left)
			den = fmt.Sprintf("%s*%s", den, right)
		} else {
			num = append(num, m)
		}
	}

	return term{
		operator:    op,
		numerator:   num,
		denominator: den,
	}, nil
}

// 在主层级拆分 *，忽略括号或函数中的 *
func splitMultiplicationPreservingNested(expr string) []string {
	var parts []string
	var current strings.Builder
	nesting := 0

	for _, r := range expr {
		switch r {
		case '(':
			nesting++
		case ')':
			if nesting > 0 {
				nesting--
			}
		case '*':
			if nesting == 0 {
				parts = append(parts, current.String())
				current.Reset()
				continue
			}
		}
		current.WriteRune(r)
	}

	if current.Len() > 0 {
		parts = append(parts, current.String())
	}

	return parts
}

// 查找主层级的 /，忽略括号中
func findTopLevelSlash(s string) int {
	nesting := 0
	for i, r := range s {
		switch r {
		case '(':
			nesting++
		case ')':
			nesting--
		case '/':
			if nesting == 0 {
				return i
			}
		}
	}
	return -1
}
