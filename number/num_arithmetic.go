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

type Term struct {
	Coeff float64
	Vars  []string // sorted variables, e.g. [x][x][y] => ["x", "x", "y"]
}

func (t Term) Key() string {
	return strings.Join(t.Vars, "*")
}

func (t Term) String() string {
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

type polynomial []Term

// --- Tokenization ---

type TokenType int

const (
	NUM TokenType = iota
	VAR
	PLUS
	MINUS
	MULT
	LPAREN
	RPAREN
)

type Token struct {
	Type  TokenType
	Value string
}

func tokenize(s string) []Token {
	var tokens []Token
	i := 0
	for i < len(s) {
		switch {
		case s[i] == ' ':
			i++
		case s[i] == '+':
			tokens = append(tokens, Token{PLUS, "+"})
			i++
		case s[i] == '-':
			tokens = append(tokens, Token{MINUS, "-"})
			i++
		case s[i] == '*':
			tokens = append(tokens, Token{MULT, "*"})
			i++
		case s[i] == '(':
			tokens = append(tokens, Token{LPAREN, "("})
			i++
		case s[i] == ')':
			tokens = append(tokens, Token{RPAREN, ")"})
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
			tokens = append(tokens, Token{VAR, varName})
			i = j + 1
		case unicode.IsDigit(rune(s[i])):
			j := i
			for j < len(s) && (unicode.IsDigit(rune(s[j])) || s[j] == '.') {
				j++
			}
			tokens = append(tokens, Token{NUM, s[i:j]})
			i = j
		default:
			panic("invalid character: " + string(s[i]))
		}
	}
	return tokens
}

// --- AST definitions ---

type NodeType int

const (
	N_ADD NodeType = iota
	N_MUL
	N_NUM
	N_VAR
)

type AST struct {
	Type     NodeType
	Value    string
	Children []*AST
}

// --- Recursive descent parser ---

type Parser struct {
	tokens []Token
	pos    int
}

func parseExpr(tokens []Token) *AST {
	p := &Parser{tokens, 0}
	return p.parseExpr()
}

func (p *Parser) parseExpr() *AST {
	node := p.parseTerm()
	for {
		if p.match(PLUS) {
			right := p.parseTerm()
			node = &AST{Type: N_ADD, Children: []*AST{node, right}}
		} else if p.match(MINUS) {
			right := p.parseTerm()
			neg := &AST{
				Type:     N_MUL,
				Children: []*AST{{Type: N_NUM, Value: "-1"}, right},
			}
			node = &AST{Type: N_ADD, Children: []*AST{node, neg}}
		} else {
			break
		}
	}
	return node
}

func (p *Parser) parseTerm() *AST {
	node := p.parseFactor()
	for p.match(MULT) {
		right := p.parseFactor()
		node = &AST{Type: N_MUL, Children: []*AST{node, right}}
	}
	return node
}

func (p *Parser) parseFactor() *AST {
	if p.match(NUM) {
		return &AST{Type: N_NUM, Value: p.prev().Value}
	}
	if p.match(VAR) {
		return &AST{Type: N_VAR, Value: p.prev().Value}
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

func (p *Parser) match(t TokenType) bool {
	if p.pos < len(p.tokens) && p.tokens[p.pos].Type == t {
		p.pos++
		return true
	}
	return false
}

func (p *Parser) prev() Token {
	return p.tokens[p.pos-1]
}

// --- Evaluation ---

func eval(ast *AST) polynomial {
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
				combined := Term{
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
		result = append(result, Term{Coeff: coeff, Vars: vars})
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
