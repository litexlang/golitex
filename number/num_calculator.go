// Copyright Jiachen Shen.
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

// This file is for and only for as a simple calculator for literal number calculation.

package litex_num

import (
	"errors"
	"fmt"
	"strconv"
	"unicode"
)

type tokenType int

const (
	tokNumber tokenType = iota
	tokPlus
	tokMinus
	tokMultiply
	tokDivide
	tokLParen
	tokRParen
)

type calculatorToken struct {
	typ tokenType
	val string
}

// 词法分析
func calculatorTokenize(expr string) ([]calculatorToken, error) {
	var tokens []calculatorToken
	i := 0
	for i < len(expr) {
		ch := expr[i]

		if unicode.IsSpace(rune(ch)) {
			i++
			continue
		}

		switch ch {
		case '+':
			tokens = append(tokens, calculatorToken{tokPlus, "+"})
			i++
		case '-':
			tokens = append(tokens, calculatorToken{tokMinus, "-"})
			i++
		case '*':
			tokens = append(tokens, calculatorToken{tokMultiply, "*"})
			i++
		case '/':
			tokens = append(tokens, calculatorToken{tokDivide, "/"})
			i++
		case '(':
			tokens = append(tokens, calculatorToken{tokLParen, "("})
			i++
		case ')':
			tokens = append(tokens, calculatorToken{tokRParen, ")"})
			i++
		default:
			if unicode.IsDigit(rune(ch)) || ch == '.' {
				start := i
				for i < len(expr) && (unicode.IsDigit(rune(expr[i])) || expr[i] == '.') {
					i++
				}
				tokens = append(tokens, calculatorToken{tokNumber, expr[start:i]})
			} else {
				return nil, fmt.Errorf("unexpected character: %c", ch)
			}
		}
	}
	return tokens, nil
}

// 解析与计算表达式：使用递归下降解析器
type calculatorParser struct {
	tokens []calculatorToken
	pos    int
}

func (p *calculatorParser) current() calculatorToken {
	if p.pos >= len(p.tokens) {
		return calculatorToken{typ: -1}
	}
	return p.tokens[p.pos]
}

func (p *calculatorParser) eat(t tokenType) error {
	if p.current().typ == t {
		p.pos++
		return nil
	}
	return fmt.Errorf("unexpected calculatorToken: %v", p.current())
}

// expr = term { (+|-) term }
func (p *calculatorParser) parseExpr() (float64, error) {
	result, err := p.parseTerm()
	if err != nil {
		return 0, err
	}

	for {
		switch p.current().typ {
		case tokPlus:
			p.eat(tokPlus)
			right, err := p.parseTerm()
			if err != nil {
				return 0, err
			}
			result += right
		case tokMinus:
			p.eat(tokMinus)
			right, err := p.parseTerm()
			if err != nil {
				return 0, err
			}
			result -= right
		default:
			return result, nil
		}
	}
}

// term = factor { (*|/) factor }
func (p *calculatorParser) parseTerm() (float64, error) {
	result, err := p.parseFactor()
	if err != nil {
		return 0, err
	}

	for {
		switch p.current().typ {
		case tokMultiply:
			p.eat(tokMultiply)
			right, err := p.parseFactor()
			if err != nil {
				return 0, err
			}
			result *= right
		case tokDivide:
			p.eat(tokDivide)
			right, err := p.parseFactor()
			if err != nil {
				return 0, err
			}
			if right == 0 {
				return 0, errors.New("division by zero")
			}
			result /= right
		default:
			return result, nil
		}
	}
}

// factor = number | ( expr )
func (p *calculatorParser) parseFactor() (float64, error) {
	switch p.current().typ {
	case tokNumber:
		val := p.current().val
		p.eat(tokNumber)
		return strconv.ParseFloat(val, 64)
	case tokLParen:
		p.eat(tokLParen)
		val, err := p.parseExpr()
		if err != nil {
			return 0, err
		}
		if err := p.eat(tokRParen); err != nil {
			return 0, err
		}
		return val, nil
	default:
		return 0, fmt.Errorf("unexpected calculatorToken: %v", p.current())
	}
}

func CalculatorEval(expr string) (float64, error) {
	tokens, err := calculatorTokenize(expr)
	if err != nil {
		return 0, err
	}
	p := calculatorParser{tokens: tokens}
	return p.parseExpr()
}
