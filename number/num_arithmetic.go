// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_num

import (
	"fmt"
	"sort"
	"strconv"
	"strings"
	"unicode"
)

type arithmeticTerm struct {
	Coeff float64
	Vars  []string // sorted variables, e.g. [x][x][y] => ["x", "x", "y"]
}

func (t arithmeticTerm) Key() string {
	return strings.Join(t.Vars, "*")
}

func (t arithmeticTerm) String() string {
	if len(t.Vars) == 0 {
		return fmt.Sprintf("%g", t.Coeff)
	}
	var varParts []string
	for _, v := range t.Vars {
		varParts = append(varParts, fmt.Sprintf("[%s]", v))
	}
	key := strings.Join(varParts, "*")
	if t.Coeff == 1 {
		return key
	}
	return fmt.Sprintf("%g*%s", t.Coeff, key)
}

type polynomial []arithmeticTerm

// --- Tokenization ---

type arithematicTokenType int

const (
	NUM arithematicTokenType = iota
	VAR
	PLUS
	MINUS
	MULT
	LPAREN
	RPAREN
)

type arithematicToken struct {
	Type  arithematicTokenType
	Value string
}

func tokenize(s string) []arithematicToken {
	var tokens []arithematicToken
	i := 0
	for i < len(s) {
		switch {
		case s[i] == ' ':
			i++
		case s[i] == '+':
			tokens = append(tokens, arithematicToken{PLUS, "+"})
			i++
		case s[i] == '-':
			tokens = append(tokens, arithematicToken{MINUS, "-"})
			i++
		case s[i] == '*':
			tokens = append(tokens, arithematicToken{MULT, "*"})
			i++
		case s[i] == '(':
			tokens = append(tokens, arithematicToken{LPAREN, "("})
			i++
		case s[i] == ')':
			tokens = append(tokens, arithematicToken{RPAREN, ")"})
			i++
		case s[i] == '[':
			j := i + 1
			for j < len(s) && s[j] != ']' {
				j++
			}
			if j >= len(s) {
				panic("missing closing ']' for variable")
			}
			varName := s[i+1 : j]
			tokens = append(tokens, arithematicToken{VAR, varName})
			i = j + 1
		case unicode.IsDigit(rune(s[i])):
			j := i
			for j < len(s) && (unicode.IsDigit(rune(s[j])) || s[j] == '.') {
				j++
			}
			tokens = append(tokens, arithematicToken{NUM, s[i:j]})
			i = j
		default:
			panic("invalid character: " + string(s[i]))
		}
	}
	return tokens
}

// --- AST definitions ---

type arithemticNodeType int

const (
	N_ADD arithemticNodeType = iota
	N_MUL
	N_NUM
	N_VAR
)

type arithematicAST struct {
	Type     arithemticNodeType
	Value    string
	Children []*arithematicAST
}

// --- Recursive descent parser ---

type arithmeicParser struct {
	tokens []arithematicToken
	pos    int
}

func parseExpr(tokens []arithematicToken) *arithematicAST {
	p := &arithmeicParser{tokens, 0}
	return p.parseExpr()
}

func (p *arithmeicParser) parseExpr() *arithematicAST {
	node := p.parseTerm()
	for {
		if p.match(PLUS) {
			right := p.parseTerm()
			node = &arithematicAST{Type: N_ADD, Children: []*arithematicAST{node, right}}
		} else if p.match(MINUS) {
			right := p.parseTerm()
			neg := &arithematicAST{
				Type:     N_MUL,
				Children: []*arithematicAST{{Type: N_NUM, Value: "-1"}, right},
			}
			node = &arithematicAST{Type: N_ADD, Children: []*arithematicAST{node, neg}}
		} else {
			break
		}
	}
	return node
}

func (p *arithmeicParser) parseTerm() *arithematicAST {
	node := p.parseFactor()
	for p.match(MULT) {
		right := p.parseFactor()
		node = &arithematicAST{Type: N_MUL, Children: []*arithematicAST{node, right}}
	}
	return node
}

func (p *arithmeicParser) parseFactor() *arithematicAST {
	if p.match(NUM) {
		return &arithematicAST{Type: N_NUM, Value: p.prev().Value}
	}
	if p.match(VAR) {
		return &arithematicAST{Type: N_VAR, Value: p.prev().Value}
	}
	if p.match(LPAREN) {
		node := p.parseExpr()
		if !p.match(RPAREN) {
			panic("missing closing parenthesis")
		}
		return node
	}
	panic("unexpected token")
}

func (p *arithmeicParser) match(t arithematicTokenType) bool {
	if p.pos < len(p.tokens) && p.tokens[p.pos].Type == t {
		p.pos++
		return true
	}
	return false
}

func (p *arithmeicParser) prev() arithematicToken {
	return p.tokens[p.pos-1]
}

// --- Evaluation ---

func eval(ast *arithematicAST) polynomial {
	switch ast.Type {
	case N_NUM:
		n, _ := strconv.ParseFloat(ast.Value, 64)
		return polynomial{{Coeff: n}}
	case N_VAR:
		return polynomial{{Coeff: 1.0, Vars: []string{ast.Value}}}
	case N_ADD:
		left := eval(ast.Children[0])
		right := eval(ast.Children[1])
		return append(left, right...)
	case N_MUL:
		left := eval(ast.Children[0])
		right := eval(ast.Children[1])
		var result polynomial
		for _, l := range left {
			for _, r := range right {
				combined := arithmeticTerm{
					Coeff: l.Coeff * r.Coeff,
					Vars:  append([]string{}, l.Vars...),
				}
				combined.Vars = append(combined.Vars, r.Vars...)
				sort.Strings(combined.Vars)
				result = append(result, combined)
			}
		}
		return result
	default:
		panic("invalid AST node")
	}
}

// --- Combine like terms ---

func simplify(poly polynomial) polynomial {
	group := map[string]float64{}
	for _, term := range poly {
		key := term.Key()
		group[key] += term.Coeff
	}
	var result polynomial
	for key, coeff := range group {
		if coeff == 0 {
			continue
		}
		vars := []string{}
		if key != "" {
			vars = strings.Split(key, "*")
		}
		result = append(result, arithmeticTerm{Coeff: coeff, Vars: vars})
	}
	sort.Slice(result, func(i, j int) bool {
		return result[i].Key() < result[j].Key()
	})
	return result
}

// --- High-level entry point ---

func ParseAndExpandPolynomial(expr string) polynomial {
	tokens := tokenize(expr)
	ast := parseExpr(tokens)
	poly := eval(ast)
	return simplify(poly)
}

func ExpandPolynomial_ReturnStr(expr string) string {
	poly := ParseAndExpandPolynomial(expr)
	var parts []string
	for _, t := range poly {
		parts = append(parts, t.String())
	}
	return strings.Join(parts, " + ")
}
