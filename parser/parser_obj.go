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

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// ============================================================================
// Main entry point for parsing objects
// ============================================================================

// Obj parses an object expression. It uses precedence-based parsing to handle
// infix operators correctly (e.g., a + b * c should be parsed as a + (b * c)).
// Obj()
// → objInfixExpr() [按优先级解析中缀表达式]
//
//	  → unaryOptObj() [处理一元运算符]
//		→ primaryExpr() [处理基本表达式]
//		  → atomObj() [解析原子，支持 pkgname.atomname]
//		  → numberStr() [解析数字]
//		  → fnSet() [解析函数集合]
//		  → bracedExpr_orTuple() [解析括号表达式]
func (tb *tokenBlock) Obj() (ast.Obj, error) {
	return tb.objInfixExpr(glob.PrecLowest)
}

// ============================================================================
// Precedence-based infix expression parsing
// ============================================================================

// objInfixExpr parses infix expressions using operator precedence.
// Higher precedence operators are parsed first (e.g., * before +).
// This ensures expressions like "a + b * c" are parsed as "a + (b * c)".
func (tb *tokenBlock) objInfixExpr(currentPrec glob.BuiltinOptPrecedence) (ast.Obj, error) {
	// Parse left operand (starting with unary operators or primary expressions)
	left, err := tb.unaryOptObj()
	if err != nil {
		return nil, err
	}

	// Parse infix operators with higher precedence than currentPrec
	for !tb.header.ExceedEnd() {
		curToken, err := tb.header.currentToken()
		if err != nil {
			return nil, fmt.Errorf("unexpected end of input while parsing infix expression")
		}

		// Handle backslash operator (e.g., x \mul y)
		if curToken == glob.KeySymbolBackSlash {
			fn, err := tb.backSlashExpr()
			if err != nil {
				return nil, err
			}
			right, err := tb.objInfixExpr(glob.PrecLowest)
			if err != nil {
				return nil, err
			}
			left = ast.NewFnObj(fn, []ast.Obj{left, right})
			break
		}

		// Check if current token is a binary operator
		curPrec, isBinary := glob.BuiltinOptPrecedenceMap[curToken]
		if !isBinary {
			break
		}

		// Stop if current operator has lower or equal precedence
		if curPrec <= currentPrec {
			break
		}

		// Parse right operand with current operator's precedence
		tb.header.skip("") // consume operator
		right, err := tb.objInfixExpr(curPrec)
		if err != nil {
			return nil, err
		}

		// Build function object: operator(left, right)
		leftHead := ast.Atom(curToken)
		left = ast.NewFnObj(leftHead, []ast.Obj{left, right})
	}

	return left, nil
}

// unaryOptObj parses unary operators (currently only "-").
// If no unary operator is present, it parses a primary expression.
func (tb *tokenBlock) unaryOptObj() (ast.Obj, error) {
	unaryOp, err := tb.header.currentToken()
	if err != nil {
		return nil, err
	}

	if unaryOp != glob.KeySymbolMinus {
		return tb.fnSetObjAndParenthesizedExprAndAtomObjAndFnObj()
	}

	// Handle unary minus
	tb.header.skip(unaryOp)

	// Special case: if followed by comma, return "-" as an atom
	if tb.header.is(glob.KeySymbolComma) {
		return ast.Atom(unaryOp), nil
	}

	// Parse right operand and convert to -1 * right
	right, err := tb.unaryOptObj()
	if err != nil {
		return nil, err
	}
	return ast.NewFnObj(ast.Atom(glob.KeySymbolStar), []ast.Obj{ast.Atom("-1"), right}), nil
}

// fnSetObjAndParenthesizedExprAndAtomObjAndFnObj parses primary expressions: atoms, numbers, function sets, or parenthesized expressions.
// Higher precedence means more "primitive" - parentheses and atoms are at the bottom of the precedence hierarchy.
func (tb *tokenBlock) fnSetObjAndParenthesizedExprAndAtomObjAndFnObj() (ast.Obj, error) {
	if tb.header.is(glob.KeywordFn) {
		return tb.fnSet()
	}

	if tb.header.is(glob.KeySymbolLeftBrace) {
		expr, err := tb.parenthesizedObj()
		if err != nil {
			return nil, err
		}
		return tb.fnObjWithRepeatedParentheses(expr)
	}

	if tb.header.curTokenBeginWithNumber() {
		expr, err := tb.numberAtom()
		if err != nil {
			return nil, err
		}
		if tb.header.is(glob.KeySymbolLeftBrace) {
			return nil, fmt.Errorf("unexpected left brace after number")
		}
		return expr, nil
	}

	// Parse atom (identifier, possibly with package name)
	atom, err := tb.notNumberAtom()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Check if atom is followed by function arguments
	return tb.fnObjWithRepeatedParentheses(atom)
}

// ============================================================================
// Atom parsing
// ============================================================================

// notNumberAtom parses an atom (identifier). Supports package name notation: pkgname.atomname
// For example, "a.b" means atom "b" in package "a".
func (tb *tokenBlock) notNumberAtom() (ast.Atom, error) {
	value, err := tb.header.next()
	if err != nil {
		return ast.Atom(""), err
	}

	// Check for package name separator (e.g., "a.b")
	if tb.header.is(glob.PkgNameAtomSeparator) {
		tb.header.skip(glob.PkgNameAtomSeparator)
		rightValue, err := tb.header.next()
		if err != nil {
			return "", parserErrAtTb(err, tb)
		}
		return ast.Atom(fmt.Sprintf("%s%s%s", value, glob.PkgNameAtomSeparator, rightValue)), nil
	}

	return ast.Atom(value), nil
}

// numberAtom parses a numeric literal (integer or decimal).
func (tb *tokenBlock) numberAtom() (ast.Atom, error) {
	left, err := tb.header.next()
	if err != nil {
		return ast.Atom(""), err
	}

	// Validate all characters are digits
	for _, c := range left {
		if c < '0' || c > '9' {
			return ast.Atom(""), fmt.Errorf("invalid number: %s", left)
		}
	}

	// Check for decimal point
	if tb.header.is(glob.KeySymbolDot) {
		// Peek ahead to check if next token is all digits (decimal part)
		nextChar := tb.header.strAtCurIndexPlus(1)
		if len(nextChar) == 0 {
			return ast.Atom(left), nil
		}

		allDigits := true
		for _, c := range nextChar {
			if c < '0' || c > '9' {
				allDigits = false
				break
			}
		}

		if allDigits {
			tb.header.skip("")
			right, err := tb.header.next()
			if err != nil {
				return ast.Atom(""), fmt.Errorf("invalid number: %s", right)
			}
			return ast.Atom(fmt.Sprintf("%s.%s", left, right)), nil
		} else {
			return ast.Atom(""), fmt.Errorf("invalid number: %s", left)
		}
	}

	// Integer: cannot start with 0 unless it's exactly "0"
	if left[0] == '0' && len(left) > 1 {
		return ast.Atom(""), fmt.Errorf("invalid number: %s", left)
	}

	return ast.Atom(left), nil
}

func (tb *tokenBlock) bracedObjSlice() ([]ast.Obj, error) {
	params := []ast.Obj{}
	tb.header.skip(glob.KeySymbolLeftBrace)

	if !tb.header.is(glob.KeySymbolRightBrace) {
		for {
			obj, err := tb.Obj()
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			params = append(params, obj)

			done, err := tb.expectAndSkipCommaOr(glob.KeySymbolRightBrace)
			if err != nil {
				return nil, err
			}
			if done {
				break
			}
		}
	}

	tb.header.skip(glob.KeySymbolRightBrace)

	return params, nil
}

func (tb *tokenBlock) parenthesizedObj() (ast.Obj, error) {
	if err := tb.header.skip(glob.KeySymbolLeftBrace); err != nil {
		return nil, fmt.Errorf("expected '(': %s", err)
	}

	// Peek after first expression to check for comma
	firstExpr, err := tb.Obj()
	if err != nil {
		return nil, err
	}

	// If no comma, expect a single expression followed by ')'
	if err := tb.header.skip(glob.KeySymbolRightBrace); err != nil {
		return nil, fmt.Errorf("expected ')': %s", err)
	}

	return firstExpr, nil
}

// fnObjWithRepeatedParentheses parses function calls with multiple consecutive parentheses pairs.
// For example, a()()()() will be parsed as (((a()())())()).
// Each () pair is parsed as a separate argument list, and the function continues
// until there are no more left braces.
func (tb *tokenBlock) fnObjWithRepeatedParentheses(head ast.Obj) (ast.Obj, error) {
	for !tb.header.ExceedEnd() && (tb.header.is(glob.KeySymbolLeftBrace)) {
		objParamsPtr, err := tb.bracedObjSlice()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		head = ast.NewFnObj(head, objParamsPtr)
	}

	return head, nil
}

func (tb *tokenBlock) fnSet() (ast.Obj, error) {
	tb.header.skip(glob.KeywordFn)
	tb.header.skip(glob.KeySymbolLeftBrace)

	fnSets := []ast.Obj{}
	var retSet ast.Obj
	for !(tb.header.is(glob.KeySymbolRightBrace)) {
		fnSet, err := tb.Obj()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		fnSets = append(fnSets, fnSet)

		done, err := tb.expectAndSkipCommaOr(glob.KeySymbolRightBrace)
		if err != nil {
			return nil, err
		}
		if done {
			break
		}
	}

	err := tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	retSet, err = tb.Obj()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	ret := ast.NewFnObj(ast.NewFnObj(ast.Atom(glob.KeywordFn), fnSets), []ast.Obj{retSet})

	return ret, nil
}

func ParseSourceCodeGetObj(s string) (ast.Obj, error) {
	blocks, err := makeTokenBlocks([]string{s})
	if err != nil {
		return nil, err
	}

	obj, err := blocks[0].Obj()
	if err != nil {
		return nil, err
	}

	return obj, nil
}

func (tb *tokenBlock) backSlashExpr() (ast.Obj, error) {
	err := tb.header.skip(glob.KeySymbolBackSlash)
	if err != nil {
		return nil, err
	}

	obj, err := tb.header.next()
	if err != nil {
		return nil, err
	}

	return ast.Atom(obj), nil
}
