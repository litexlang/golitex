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

package litex_num

import (
	"fmt"
	"sort"
	"strings"
	"unicode"
)

type arithmeticTerm struct {
	// CoEff float64
	CoEff string
	Vars  []string // sorted variables, e.g. [x][x][y] => ["x", "x", "y"]
}

func (t arithmeticTerm) Key() string {
	return strings.Join(t.Vars, "*")
}

func (t arithmeticTerm) String() string {
	if len(t.Vars) == 0 {
		return t.CoEff
	}
	var varParts []string
	for _, v := range t.Vars {
		varParts = append(varParts, fmt.Sprintf("{%s}", v))
	}
	key := strings.Join(varParts, "*")
	if t.CoEff == "1" {
		return key
	}
	return fmt.Sprintf("%s*%s", t.CoEff, key)
}

type polynomial []arithmeticTerm

// --- Tokenization ---

type arithTokenType int

const (
	NUM arithTokenType = iota
	VAR
	PLUS
	MINUS
	MULTI
	LPAREN
	RPAREN
)

type arithToken struct {
	Type  arithTokenType
	Value string
}

func tokenize(s string) []arithToken {
	var tokens []arithToken
	i := 0
	for i < len(s) {
		switch {
		case s[i] == ' ':
			i++
		case s[i] == '+':
			tokens = append(tokens, arithToken{PLUS, "+"})
			i++
		case s[i] == '-':
			tokens = append(tokens, arithToken{MINUS, "-"})
			i++
		case s[i] == '*':
			tokens = append(tokens, arithToken{MULTI, "*"})
			i++
		case s[i] == '(':
			tokens = append(tokens, arithToken{LPAREN, "("})
			i++
		case s[i] == ')':
			tokens = append(tokens, arithToken{RPAREN, ")"})
			i++
		case s[i] == '{':
			j := i + 1
			for j < len(s) && s[j] != '}' {
				j++
			}
			if j >= len(s) {
				panic("missing closing '}' for variable")
			}
			varName := s[i+1 : j]
			tokens = append(tokens, arithToken{VAR, varName})
			i = j + 1
		case unicode.IsDigit(rune(s[i])):
			j := i
			for j < len(s) && (unicode.IsDigit(rune(s[j])) || s[j] == '.') {
				j++
			}
			tokens = append(tokens, arithToken{NUM, s[i:j]})
			i = j
		default:
			panic("invalid character: " + string(s[i]))
		}
	}
	return tokens
}

// --- AST definitions ---

type arithNodeType int

const (
	N_ADD arithNodeType = iota
	N_MUL
	N_NUM
	N_VAR
)

type arithAST struct {
	Type     arithNodeType
	Value    string
	Children []*arithAST
}

// --- Recursive descent parser ---

type arithParser struct {
	tokens []arithToken
	pos    int
}

func parseExpr(tokens []arithToken) *arithAST {
	p := &arithParser{tokens, 0}
	return p.parseExpr()
}

func (p *arithParser) parseExpr() *arithAST {
	node := p.parseTerm()
	for {
		if p.match(PLUS) {
			right := p.parseTerm()
			node = &arithAST{Type: N_ADD, Children: []*arithAST{node, right}}
		} else if p.match(MINUS) {
			right := p.parseTerm()
			neg := &arithAST{
				Type:     N_MUL,
				Children: []*arithAST{{Type: N_NUM, Value: "-1"}, right},
			}
			node = &arithAST{Type: N_ADD, Children: []*arithAST{node, neg}}
		} else {
			break
		}
	}
	return node
}

func (p *arithParser) parseTerm() *arithAST {
	node := p.parseFactor()
	for p.match(MULTI) {
		right := p.parseFactor()
		node = &arithAST{Type: N_MUL, Children: []*arithAST{node, right}}
	}
	return node
}

func (p *arithParser) parseFactor() *arithAST {
	if p.match(NUM) {
		return &arithAST{Type: N_NUM, Value: p.prev().Value}
	}
	if p.match(VAR) {
		return &arithAST{Type: N_VAR, Value: p.prev().Value}
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

func (p *arithParser) match(t arithTokenType) bool {
	if p.pos < len(p.tokens) && p.tokens[p.pos].Type == t {
		p.pos++
		return true
	}
	return false
}

func (p *arithParser) prev() arithToken {
	return p.tokens[p.pos-1]
}

// --- Evaluation ---

func eval(ast *arithAST) polynomial {
	switch ast.Type {
	case N_NUM:
		// 处理数字，包括负数
		value := ast.Value
		if value == "-1" {
			value = "-1"
		}
		return polynomial{{CoEff: value}}
	case N_VAR:
		// return polynomial{{CoEff: 1.0, Vars: []string{ast.Value}}}
		return polynomial{{CoEff: "1", Vars: []string{ast.Value}}}
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
				coEff := MulDecimal(l.CoEff, r.CoEff)
				combined := arithmeticTerm{
					// CoEff: l.CoEff * r.CoEff,
					CoEff: coEff,
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

// // This version of simplify does not make x * x into x^2
// func simplify(poly polynomial) polynomial {
// 	group := map[string]float64{}
// 	for _, term := range poly {
// 		key := term.Key()
// 		group[key] += term.CoEff
// 	}
// 	var result polynomial
// 	for key, coEff := range group {
// 		if coEff == 0 {
// 			continue
// 		}
// 		vars := []string{}
// 		if key != "" {
// 			vars = strings.Split(key, "*")
// 		}
// 		result = append(result, arithmeticTerm{CoEff: coEff, Vars: vars})
// 	}
// 	sort.Slice(result, func(i, j int) bool {
// 		return result[i].Key() < result[j].Key()
// 	})
// 	return result
// }

// This version of simplify makes x * x into x^2
func simplify(poly polynomial) polynomial {
	// group := map[string]float64{}
	group := map[string]string{}
	for _, term := range poly {
		key := term.Key()
		// group[key] += term.CoEff
		coEff := AddDecimal(group[key], term.CoEff)
		group[key] = coEff
	}
	var result polynomial
	for key, coEff := range group {
		// if coEff == 0 {
		// 	continue
		// }
		if coEff == "0" {
			continue
		}
		vars := []string{}
		if key != "" {
			// vars = strings.Split(key, "*")

			// Count occurrences of each variable
			varCount := make(map[string]int)
			for _, v := range strings.Split(key, "*") {
				varCount[v]++
			}
			// Convert to exponential form
			for v, count := range varCount {
				if count == 1 {
					vars = append(vars, v)
				} else {
					vars = append(vars, fmt.Sprintf("(%s ^ %d)", v, count))
				}
			}
			// Sort variables for consistent output
			sort.Strings(vars)
		}
		result = append(result, arithmeticTerm{CoEff: coEff, Vars: vars})
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
	simplified := simplify(poly)
	return simplified
}

func ExpandPolynomial_ReturnStr(expr string) string {
	poly := ParseAndExpandPolynomial(expr)
	var parts []string
	for _, t := range poly {
		parts = append(parts, t.String())
	}
	return strings.Join(parts, " + ")
}

// SortStringsByLength sorts a slice of strings by their length
func SortStringsByLength(strs []string) {
	sort.Slice(strs, func(i, j int) bool {
		return len(strs[i]) < len(strs[j])
	})
}
