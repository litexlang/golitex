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

package litex_ast

import (
	"fmt"
	glob "golitex/glob"
	"strings"
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
//		  → atomObj() [解析原子，支持 pkgName.atomName]
//		  → numberStr() [解析数字]
//		  → fnSet() [解析函数集合]
//		  → bracedExpr_orTuple() [解析括号表达式]
func (p *TbParser) Obj(tb *tokenBlock) (Obj, error) {
	if tb.header.is(glob.KeySymbolLeftCurly) {
		return p.EnumSetObjOrSetBuilderObj(tb)
	}

	return p.objInfixExpr(tb, glob.PrecLowest)
}

// ============================================================================
// Precedence-based infix expression parsing
// ============================================================================

// objInfixExpr parses infix expressions using operator precedence.
// Higher precedence operators are parsed first (e.g., * before +).
// This ensures expressions like "a + b * c" are parsed as "a + (b * c)".
func (p *TbParser) objInfixExpr(tb *tokenBlock, currentPrec glob.BuiltinOptPrecedence) (Obj, error) {
	// Parse left operand (starting with unary operators or primary expressions)
	left, err := p.unaryOptObj(tb)
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
			fn, err := p.backSlashExpr(tb)
			if err != nil {
				return nil, err
			}
			right, err := p.objInfixExpr(tb, glob.PrecLowest)
			if err != nil {
				return nil, err
			}
			left = NewFnObj(fn, []Obj{left, right})
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
		right, err := p.objInfixExpr(tb, curPrec)
		if err != nil {
			return nil, err
		}

		// Build function object: operator(left, right)
		leftHead := Atom(curToken)
		left = NewFnObj(leftHead, []Obj{left, right})
	}

	return left, nil
}

// unaryOptObj parses unary operators (currently only "-").
// If no unary operator is present, it parses a primary expression.
func (p *TbParser) unaryOptObj(tb *tokenBlock) (Obj, error) {
	unaryOp, err := tb.header.currentToken()
	if err != nil {
		return nil, err
	}

	if unaryOp != glob.KeySymbolMinus {
		return p.fnSetObjAndBracedExprAndAtomObjAndFnObj(tb)
	}

	// Handle unary minus
	tb.header.skip(unaryOp)

	// Special case: if followed by comma, return "-" as an atom
	if tb.header.is(glob.KeySymbolComma) {
		return Atom(unaryOp), nil
	}

	// Parse right operand and convert to -1 * right
	right, err := p.unaryOptObj(tb)
	if err != nil {
		return nil, err
	}
	return NewFnObj(Atom(glob.KeySymbolStar), []Obj{Atom("-1"), right}), nil
}

// fnSetObjAndBracedExprAndAtomObjAndFnObj parses primary expressions: atoms, numbers, function sets, or parenthesized expressions.
// Higher precedence means more "primitive" - parentheses and atoms are at the bottom of the precedence hierarchy.
func (p *TbParser) fnSetObjAndBracedExprAndAtomObjAndFnObj(tb *tokenBlock) (Obj, error) {
	if tb.header.is(glob.KeywordFn) {
		return p.fnSet(tb)
	}

	if tb.header.is(glob.KeySymbolLeftBrace) {
		expr, err := p.bracedObj(tb)
		if err != nil {
			return nil, err
		}
		return p.fnObjWithRepeatedBraceAndBracket(tb, expr)
	}

	if tb.header.curTokenBeginWithNumber() {
		expr, err := p.numberAtom(tb)
		if err != nil {
			return nil, err
		}
		if tb.header.is(glob.KeySymbolLeftBrace) {
			return nil, fmt.Errorf("unexpected left brace after number")
		}
		return expr, nil
	}

	// Parse atom (identifier, possibly with package name)
	atom, err := p.notNumberAtom(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Check if atom is followed by function arguments
	return p.fnObjWithRepeatedBraceAndBracket(tb, atom)
}

// ============================================================================
// Atom parsing
// ============================================================================

// notNumberAtom parses an atom (identifier). Supports package name notation: pkgName.atomName
// For example, "a.b" means atom "b" in package "a".
func (p *TbParser) notNumberAtom(tb *tokenBlock) (Atom, error) {
	value, err := tb.header.next()
	if err != nil {
		return Atom(""), err
	}

	// Check for package name separator (e.g., "a.b")
	if tb.header.is(glob.PkgNameAtomSeparator) {
		tb.header.skip(glob.PkgNameAtomSeparator)
		rightValue, err := tb.header.next()
		if err != nil {
			return "", parserErrAtTb(err, tb)
		}
		return Atom(fmt.Sprintf("%s%s%s", value, glob.PkgNameAtomSeparator, rightValue)), nil
	}

	return Atom(value), nil
}

// numberAtom parses a numeric literal (integer or decimal).
func (p *TbParser) numberAtom(tb *tokenBlock) (Atom, error) {
	left, err := tb.header.next()
	if err != nil {
		return Atom(""), err
	}

	// Validate all characters are digits
	for _, c := range left {
		if c < '0' || c > '9' {
			return Atom(""), fmt.Errorf("invalid number: %s", left)
		}
	}

	// Check for decimal point
	if tb.header.is(glob.KeySymbolDot) {
		// Peek ahead to check if next token is all digits (decimal part)
		nextChar := tb.header.strAtCurIndexPlus(1)
		if len(nextChar) == 0 {
			return Atom(left), nil
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
				return Atom(""), fmt.Errorf("invalid number: %s", right)
			}
			return Atom(fmt.Sprintf("%s.%s", left, right)), nil
		} else {
			return Atom(""), fmt.Errorf("invalid number: %s", left)
		}
	}

	// Integer: cannot start with 0 unless it's exactly "0"
	if left[0] == '0' && len(left) > 1 {
		return Atom(""), fmt.Errorf("invalid number: %s", left)
	}

	return Atom(left), nil
}

func (p *TbParser) bracedObjSlice(tb *tokenBlock) ([]Obj, error) {
	params := []Obj{}
	tb.header.skip(glob.KeySymbolLeftBrace)

	if !tb.header.is(glob.KeySymbolRightBrace) {
		for {
			obj, err := p.Obj(tb)
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

func (p *TbParser) bracketedObj(tb *tokenBlock) (Obj, error) {
	tb.header.skip(glob.KeySymbolLeftBracket)

	obj, err := p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	tb.header.skip(glob.KeySymbolRightBracket)

	return obj, nil
}

func (p *TbParser) bracedObj(tb *tokenBlock) (Obj, error) {
	if err := tb.header.skip(glob.KeySymbolLeftBrace); err != nil {
		return nil, fmt.Errorf("expected '(': %s", err)
	}

	// Peek after first expression to check for comma
	firstExpr, err := p.Obj(tb)
	if err != nil {
		return nil, err
	}

	// 如果是 , 那说明是 tuple
	if tb.header.is(glob.KeySymbolComma) {
		// Collect all expressions in the tuple
		tupleObjs := []Obj{firstExpr}

		for {
			// Skip comma
			tb.header.skip(glob.KeySymbolComma)

			// if tb.header.is(glob.KeySymbolRightBrace) {
			// 	break
			// }

			// Parse next expression
			obj, err := p.Obj(tb)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			tupleObjs = append(tupleObjs, obj)

			// Check if we're done (next token is ')')
			if tb.header.is(glob.KeySymbolRightBrace) {
				break
			}

			// If not ')', must be a comma
			// If we see a binary operator here, it means we parsed too much
			// (e.g., in "(a, b / c)", we shouldn't parse "/" as part of the tuple element)
			curToken, err := tb.header.currentToken()
			if err != nil {
				return nil, parserErrAtTb(fmt.Errorf("unexpected end of input in tuple"), tb)
			}
			_, isBinary := glob.BuiltinOptPrecedenceMap[curToken]
			if isBinary {
				return nil, parserErrAtTb(fmt.Errorf("unexpected binary operator '%s' in tuple (did you forget a comma or closing parenthesis?)", curToken), tb)
			}
			if !tb.header.is(glob.KeySymbolComma) {
				return nil, parserErrAtTb(fmt.Errorf("expected ',' or ')' but got '%s'", curToken), tb)
			}
		}

		// Skip closing ')'
		if err := tb.header.skip(glob.KeySymbolRightBrace); err != nil {
			return nil, fmt.Errorf("expected ')': %s", err)
		}

		// Special case: if tuple is followed by a binary operator, bind it to the last element
		// e.g., "(a, b) / c" should be parsed as "(a, b / c)"
		if !tb.header.ExceedEnd() {
			curToken, err := tb.header.currentToken()
			if err == nil {
				curPrec, isBinary := glob.BuiltinOptPrecedenceMap[curToken]
				if isBinary {
					// The last element is the left operand, operator is curToken, need to parse right operand
					lastIdx := len(tupleObjs) - 1
					leftOperand := tupleObjs[lastIdx]

					// Skip the operator
					tb.header.skip("")

					// Parse the right operand with the operator's precedence
					rightOperand, err := p.objInfixExpr(tb, curPrec)
					if err != nil {
						return nil, parserErrAtTb(err, tb)
					}

					// Replace the last element with the combined expression: operator(left, right)
					tupleObjs[lastIdx] = NewFnObj(Atom(curToken), []Obj{leftOperand, rightOperand})
				}
			}
		}

		// Return tuple as FnObj with TupleOpt as head
		return NewFnObj(Atom(glob.KeywordTuple), tupleObjs), nil
	}

	// If no comma, expect a single expression followed by ')'
	if err := tb.header.skip(glob.KeySymbolRightBrace); err != nil {
		return nil, fmt.Errorf("expected ')': %s", err)
	}

	return firstExpr, nil
}

// fnObjWithRepeatedBraceAndBracket parses function calls with multiple consecutive parentheses pairs
// and bracket indexing operations.
// For example, a()()()() will be parsed as (((a()())())()).
// Each () pair is parsed as a separate argument list.
// Each [] pair is parsed as an index operation (prefix opt) using IndexOpt.
// The function continues until there are no more left braces or left brackets.
func (p *TbParser) fnObjWithRepeatedBraceAndBracket(tb *tokenBlock, head Obj) (Obj, error) {
	for !tb.header.ExceedEnd() {
		if tb.header.is(glob.KeySymbolLeftBrace) {
			// Parse function call arguments: ()
			objParams, err := p.bracedObjSlice(tb)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			head = NewFnObj(head, objParams)
		} else if tb.header.is(glob.KeySymbolLeftBracket) {
			// Parse index operation: []
			obj, err := p.bracketedObj(tb)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			// IndexOpt is a prefix operator, so it's applied as IndexOpt(head, ...params)
			head = NewFnObj(Atom(glob.KeywordIndexOpt), []Obj{head, obj})
		} else {
			// No more braces or brackets
			break
		}
	}

	return head, nil
}

func (p *TbParser) fnSet(tb *tokenBlock) (Obj, error) {
	tb.header.skip(glob.KeywordFn)
	tb.header.skip(glob.KeySymbolLeftBrace)

	fnSets := []Obj{}
	var retSet Obj
	for !(tb.header.is(glob.KeySymbolRightBrace)) {
		fnSet, err := p.Obj(tb)
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

	retSet, err = p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	ret := NewFnObj(NewFnObj(Atom(glob.KeywordFn), fnSets), []Obj{retSet})

	return ret, nil
}

func (p *TbParser) backSlashExpr(tb *tokenBlock) (Obj, error) {
	err := tb.header.skip(glob.KeySymbolBackSlash)
	if err != nil {
		return nil, err
	}

	obj, err := tb.header.next()
	if err != nil {
		return nil, err
	}

	return Atom(obj), nil
}

func (p *TbParser) EnumSetObjOrSetBuilderObj(tb *tokenBlock) (Obj, error) {
	err := tb.header.skip(glob.KeySymbolLeftCurly)
	if err != nil {
		return nil, err
	}

	if tb.header.is(glob.KeySymbolRightCurly) {
		err = tb.header.skip(glob.KeySymbolRightCurly)
		if err != nil {
			return nil, err
		}
		return MakeEnumSetObj([]Obj{}), nil
	}

	obj, err := p.Obj(tb)
	if err != nil {
		return nil, err
	}

	if !tb.header.is(glob.KeySymbolComma) && !tb.header.is(glob.KeySymbolRightCurly) {
		return p.setBuilderObj(tb, obj)
	} else {
		return p.enumSetObj(tb, obj)
	}
}

func (p *TbParser) enumSetObj(tb *tokenBlock, firstParam Obj) (Obj, error) {
	enumItems := []Obj{firstParam}

	// 跳过第一个逗号（如果存在）
	tb.header.skipIfIs(glob.KeySymbolComma)

	// 循环读取后续对象，直到遇到右花括号
	for !tb.header.is(glob.KeySymbolRightCurly) {
		curItem, err := p.Obj(tb)
		if err != nil {
			return nil, err
		}
		enumItems = append(enumItems, curItem)

		// 跳过逗号（如果存在）
		tb.header.skipIfIs(glob.KeySymbolComma)
	}

	// 跳过右花括号
	err := tb.header.skip(glob.KeySymbolRightCurly)
	if err != nil {
		return nil, err
	}

	return MakeEnumSetObj(enumItems), nil
}

// {x R: specific fact, ..., specific fact}
func (p *TbParser) setBuilderObj(tb *tokenBlock, paramAsObj Obj) (Obj, error) {
	param, ok := paramAsObj.(Atom)
	if !ok {
		return nil, fmt.Errorf("expect parameter as self")
	}

	// 这个atom不能有 pkg
	if strings.Contains(string(param), glob.PkgNameAtomSeparator) {
		return nil, fmt.Errorf("parameter cannot have package name")
	}

	paramStr := string(param)

	// Check for conflicts with existing FreeParams
	if _, exists := p.FreeParams[paramStr]; exists {
		return nil, parserErrAtTb(fmt.Errorf("parameter %s in set builder conflicts with a free parameter in the outer scope", paramStr), tb)
	}

	// Add set builder param to FreeParams
	p.FreeParams[paramStr] = struct{}{}

	// Defer: remove the param we added when leaving this set builder scope
	defer func() {
		delete(p.FreeParams, paramStr)
	}()

	parentSet, err := p.Obj(tb)
	if err != nil {
		return nil, err
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, err
	}

	facts := SpecFactPtrSlice{}
	for !tb.header.is(glob.KeySymbolRightCurly) {
		specFact, err := p.specFactStmt(tb)
		if err != nil {
			return nil, err
		}
		facts = append(facts, specFact)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
			continue
		}
	}

	// 跳过右花括号
	err = tb.header.skip(glob.KeySymbolRightCurly)
	if err != nil {
		return nil, err
	}

	return MakeSetBuilderObj(paramStr, parentSet, facts)
}
