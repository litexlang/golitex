// // Copyright 2024 Jiachen Shen.
// //
// // Licensed under the Apache License, Version 2.0 (the "License");
// // you may not use this file except in compliance with the License.
// // You may obtain a copy of the License at
// //
// //     http://www.apache.org/licenses/LICENSE-2.0
// //
// // Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// // Litex email: <litexlang@outlook.com>
// // Litex website: https://litexlang.com
// // Litex github repository: https://github.com/litexlang/golitex
// // Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_parser

// import (
// 	"fmt"
// 	ast "golitex/ast"
// 	glob "golitex/glob"
// )

// // ============================================================================
// // Main entry point for parsing objects
// // ============================================================================

// // Obj parses an object expression. It uses precedence-based parsing to handle
// // infix operators correctly (e.g., a + b * c should be parsed as a + (b * c)).
// // Obj()
// // → objInfixExpr() [按优先级解析中缀表达式]
// //
// //	  → unaryOptObj() [处理一元运算符]
// //		→ primaryExpr() [处理基本表达式]
// //		  → atomObj() [解析原子，支持 pkgName.atomName]
// //		  → numberStr() [解析数字]
// //		  → fnSet() [解析函数集合]
// //		  → bracedExpr_orTuple() [解析括号表达式]
// func (tb *tokenBlock) Obj() (ast.Obj, error) {
// 	if tb.header.is(glob.KeySymbolLeftCurly) {
// 		return tb.EnumSetObjOrIntensionalSetObj()
// 	}

// 	return tb.objInfixExpr(glob.PrecLowest)
// }

// // ============================================================================
// // Precedence-based infix expression parsing
// // ============================================================================

// // objInfixExpr parses infix expressions using operator precedence.
// // Higher precedence operators are parsed first (e.g., * before +).
// // This ensures expressions like "a + b * c" are parsed as "a + (b * c)".
// func (tb *tokenBlock) objInfixExpr(currentPrec glob.BuiltinOptPrecedence) (ast.Obj, error) {
// 	// Parse left operand (starting with unary operators or primary expressions)
// 	left, err := tb.unaryOptObj()
// 	if err != nil {
// 		return nil, err
// 	}

// 	// Parse infix operators with higher precedence than currentPrec
// 	for !tb.header.ExceedEnd() {
// 		curToken, err := tb.header.currentToken()
// 		if err != nil {
// 			return nil, fmt.Errorf("unexpected end of input while parsing infix expression")
// 		}

// 		// Handle backslash operator (e.g., x \mul y)
// 		if curToken == glob.KeySymbolBackSlash {
// 			fn, err := tb.backSlashExpr()
// 			if err != nil {
// 				return nil, err
// 			}
// 			right, err := tb.objInfixExpr(glob.PrecLowest)
// 			if err != nil {
// 				return nil, err
// 			}
// 			left = ast.NewFnObj(fn, []ast.Obj{left, right})
// 			break
// 		}

// 		// Check if current token is a binary operator
// 		curPrec, isBinary := glob.BuiltinOptPrecedenceMap[curToken]
// 		if !isBinary {
// 			break
// 		}

// 		// Stop if current operator has lower or equal precedence
// 		if curPrec <= currentPrec {
// 			break
// 		}

// 		// Parse right operand with current operator's precedence
// 		tb.header.skip("") // consume operator
// 		right, err := tb.objInfixExpr(curPrec)
// 		if err != nil {
// 			return nil, err
// 		}

// 		// Build function object: operator(left, right)
// 		leftHead := ast.Atom(curToken)
// 		left = ast.NewFnObj(leftHead, []ast.Obj{left, right})
// 	}

// 	return left, nil
// }

// // unaryOptObj parses unary operators (currently only "-").
// // If no unary operator is present, it parses a primary expression.
// func (tb *tokenBlock) unaryOptObj() (ast.Obj, error) {
// 	unaryOp, err := tb.header.currentToken()
// 	if err != nil {
// 		return nil, err
// 	}

// 	if unaryOp != glob.KeySymbolMinus {
// 		return tb.fnSetObjAndBracedExprAndAtomObjAndFnObj()
// 	}

// 	// Handle unary minus
// 	tb.header.skip(unaryOp)

// 	// Special case: if followed by comma, return "-" as an atom
// 	if tb.header.is(glob.KeySymbolComma) {
// 		return ast.Atom(unaryOp), nil
// 	}

// 	// Parse right operand and convert to -1 * right
// 	right, err := tb.unaryOptObj()
// 	if err != nil {
// 		return nil, err
// 	}
// 	return ast.NewFnObj(ast.Atom(glob.KeySymbolStar), []ast.Obj{ast.Atom("-1"), right}), nil
// }

// // fnSetObjAndBracedExprAndAtomObjAndFnObj parses primary expressions: atoms, numbers, function sets, or parenthesized expressions.
// // Higher precedence means more "primitive" - parentheses and atoms are at the bottom of the precedence hierarchy.
// func (tb *tokenBlock) fnSetObjAndBracedExprAndAtomObjAndFnObj() (ast.Obj, error) {
// 	if tb.header.is(glob.KeywordFn) {
// 		return tb.fnSet()
// 	}

// 	if tb.header.is(glob.KeySymbolLeftBrace) {
// 		expr, err := tb.bracedObj()
// 		if err != nil {
// 			return nil, err
// 		}
// 		return tb.fnObjWithRepeatedBraceAndBracket(expr)
// 	}

// 	if tb.header.curTokenBeginWithNumber() {
// 		expr, err := tb.numberAtom()
// 		if err != nil {
// 			return nil, err
// 		}
// 		if tb.header.is(glob.KeySymbolLeftBrace) {
// 			return nil, fmt.Errorf("unexpected left brace after number")
// 		}
// 		return expr, nil
// 	}

// 	// Parse atom (identifier, possibly with package name)
// 	atom, err := tb.notNumberAtom()
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	// Check if atom is followed by function arguments
// 	return tb.fnObjWithRepeatedBraceAndBracket(atom)
// }

// // ============================================================================
// // Atom parsing
// // ============================================================================

// // notNumberAtom parses an atom (identifier). Supports package name notation: pkgName.atomName
// // For example, "a.b" means atom "b" in package "a".
// func (tb *tokenBlock) notNumberAtom() (ast.Atom, error) {
// 	value, err := tb.header.next()
// 	if err != nil {
// 		return ast.Atom(""), err
// 	}

// 	// Check for package name separator (e.g., "a.b")
// 	if tb.header.is(glob.PkgNameAtomSeparator) {
// 		tb.header.skip(glob.PkgNameAtomSeparator)
// 		rightValue, err := tb.header.next()
// 		if err != nil {
// 			return "", parserErrAtTb(err, tb)
// 		}
// 		return ast.Atom(fmt.Sprintf("%s%s%s", value, glob.PkgNameAtomSeparator, rightValue)), nil
// 	}

// 	return ast.Atom(value), nil
// }

// // numberAtom parses a numeric literal (integer or decimal).
// func (tb *tokenBlock) numberAtom() (ast.Atom, error) {
// 	left, err := tb.header.next()
// 	if err != nil {
// 		return ast.Atom(""), err
// 	}

// 	// Validate all characters are digits
// 	for _, c := range left {
// 		if c < '0' || c > '9' {
// 			return ast.Atom(""), fmt.Errorf("invalid number: %s", left)
// 		}
// 	}

// 	// Check for decimal point
// 	if tb.header.is(glob.KeySymbolDot) {
// 		// Peek ahead to check if next token is all digits (decimal part)
// 		nextChar := tb.header.strAtCurIndexPlus(1)
// 		if len(nextChar) == 0 {
// 			return ast.Atom(left), nil
// 		}

// 		allDigits := true
// 		for _, c := range nextChar {
// 			if c < '0' || c > '9' {
// 				allDigits = false
// 				break
// 			}
// 		}

// 		if allDigits {
// 			tb.header.skip("")
// 			right, err := tb.header.next()
// 			if err != nil {
// 				return ast.Atom(""), fmt.Errorf("invalid number: %s", right)
// 			}
// 			return ast.Atom(fmt.Sprintf("%s.%s", left, right)), nil
// 		} else {
// 			return ast.Atom(""), fmt.Errorf("invalid number: %s", left)
// 		}
// 	}

// 	// Integer: cannot start with 0 unless it's exactly "0"
// 	if left[0] == '0' && len(left) > 1 {
// 		return ast.Atom(""), fmt.Errorf("invalid number: %s", left)
// 	}

// 	return ast.Atom(left), nil
// }

// func (tb *tokenBlock) bracedObjSlice() ([]ast.Obj, error) {
// 	params := []ast.Obj{}
// 	tb.header.skip(glob.KeySymbolLeftBrace)

// 	if !tb.header.is(glob.KeySymbolRightBrace) {
// 		for {
// 			obj, err := tb.Obj()
// 			if err != nil {
// 				return nil, parserErrAtTb(err, tb)
// 			}
// 			params = append(params, obj)

// 			done, err := tb.expectAndSkipCommaOr(glob.KeySymbolRightBrace)
// 			if err != nil {
// 				return nil, err
// 			}
// 			if done {
// 				break
// 			}
// 		}
// 	}

// 	tb.header.skip(glob.KeySymbolRightBrace)

// 	return params, nil
// }

// func (tb *tokenBlock) bracketedObj() (ast.Obj, error) {
// 	tb.header.skip(glob.KeySymbolLeftBracket)

// 	obj, err := tb.Obj()
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	tb.header.skip(glob.KeySymbolRightBracket)

// 	return obj, nil
// }

// func (tb *tokenBlock) bracedObj() (ast.Obj, error) {
// 	if err := tb.header.skip(glob.KeySymbolLeftBrace); err != nil {
// 		return nil, fmt.Errorf("expected '(': %s", err)
// 	}

// 	// Peek after first expression to check for comma
// 	firstExpr, err := tb.Obj()
// 	if err != nil {
// 		return nil, err
// 	}

// 	// 如果是 , 那说明是 tuple
// 	if tb.header.is(glob.KeySymbolComma) {
// 		// Collect all expressions in the tuple
// 		tupleObjs := []ast.Obj{firstExpr}

// 		for {
// 			// Skip comma
// 			tb.header.skip(glob.KeySymbolComma)

// 			// if tb.header.is(glob.KeySymbolRightBrace) {
// 			// 	break
// 			// }

// 			// Parse next expression
// 			obj, err := tb.Obj()
// 			if err != nil {
// 				return nil, parserErrAtTb(err, tb)
// 			}
// 			tupleObjs = append(tupleObjs, obj)

// 			// Check if we're done (next token is ')')
// 			if tb.header.is(glob.KeySymbolRightBrace) {
// 				break
// 			}

// 			// If not ')', must be a comma
// 			// If we see a binary operator here, it means we parsed too much
// 			// (e.g., in "(a, b / c)", we shouldn't parse "/" as part of the tuple element)
// 			curToken, err := tb.header.currentToken()
// 			if err != nil {
// 				return nil, parserErrAtTb(fmt.Errorf("unexpected end of input in tuple"), tb)
// 			}
// 			_, isBinary := glob.BuiltinOptPrecedenceMap[curToken]
// 			if isBinary {
// 				return nil, parserErrAtTb(fmt.Errorf("unexpected binary operator '%s' in tuple (did you forget a comma or closing parenthesis?)", curToken), tb)
// 			}
// 			if !tb.header.is(glob.KeySymbolComma) {
// 				return nil, parserErrAtTb(fmt.Errorf("expected ',' or ')' but got '%s'", curToken), tb)
// 			}
// 		}

// 		// Skip closing ')'
// 		if err := tb.header.skip(glob.KeySymbolRightBrace); err != nil {
// 			return nil, fmt.Errorf("expected ')': %s", err)
// 		}

// 		// Special case: if tuple is followed by a binary operator, bind it to the last element
// 		// e.g., "(a, b) / c" should be parsed as "(a, b / c)"
// 		if !tb.header.ExceedEnd() {
// 			curToken, err := tb.header.currentToken()
// 			if err == nil {
// 				curPrec, isBinary := glob.BuiltinOptPrecedenceMap[curToken]
// 				if isBinary {
// 					// The last element is the left operand, operator is curToken, need to parse right operand
// 					lastIdx := len(tupleObjs) - 1
// 					leftOperand := tupleObjs[lastIdx]

// 					// Skip the operator
// 					tb.header.skip("")

// 					// Parse the right operand with the operator's precedence
// 					rightOperand, err := tb.objInfixExpr(curPrec)
// 					if err != nil {
// 						return nil, parserErrAtTb(err, tb)
// 					}

// 					// Replace the last element with the combined expression: operator(left, right)
// 					tupleObjs[lastIdx] = ast.NewFnObj(ast.Atom(curToken), []ast.Obj{leftOperand, rightOperand})
// 				}
// 			}
// 		}

// 		// Return tuple as FnObj with TupleOpt as head
// 		return ast.NewFnObj(ast.Atom(glob.KeywordTuple), tupleObjs), nil
// 	}

// 	// If no comma, expect a single expression followed by ')'
// 	if err := tb.header.skip(glob.KeySymbolRightBrace); err != nil {
// 		return nil, fmt.Errorf("expected ')': %s", err)
// 	}

// 	return firstExpr, nil
// }

// // fnObjWithRepeatedBraceAndBracket parses function calls with multiple consecutive parentheses pairs
// // and bracket indexing operations.
// // For example, a()()()() will be parsed as (((a()())())()).
// // Each () pair is parsed as a separate argument list.
// // Each [] pair is parsed as an index operation (prefix opt) using IndexOpt.
// // The function continues until there are no more left braces or left brackets.
// func (tb *tokenBlock) fnObjWithRepeatedBraceAndBracket(head ast.Obj) (ast.Obj, error) {
// 	for !tb.header.ExceedEnd() {
// 		if tb.header.is(glob.KeySymbolLeftBrace) {
// 			// Parse function call arguments: ()
// 			objParams, err := tb.bracedObjSlice()
// 			if err != nil {
// 				return nil, parserErrAtTb(err, tb)
// 			}
// 			head = ast.NewFnObj(head, objParams)
// 		} else if tb.header.is(glob.KeySymbolLeftBracket) {
// 			// Parse index operation: []
// 			obj, err := tb.bracketedObj()
// 			if err != nil {
// 				return nil, parserErrAtTb(err, tb)
// 			}
// 			// IndexOpt is a prefix operator, so it's applied as IndexOpt(head, ...params)
// 			head = ast.NewFnObj(ast.Atom(glob.KeywordIndexOpt), []ast.Obj{head, obj})
// 		} else {
// 			// No more braces or brackets
// 			break
// 		}
// 	}

// 	return head, nil
// }

// func (tb *tokenBlock) fnSet() (ast.Obj, error) {
// 	tb.header.skip(glob.KeywordFn)
// 	tb.header.skip(glob.KeySymbolLeftBrace)

// 	fnSets := []ast.Obj{}
// 	var retSet ast.Obj
// 	for !(tb.header.is(glob.KeySymbolRightBrace)) {
// 		fnSet, err := tb.Obj()
// 		if err != nil {
// 			return nil, parserErrAtTb(err, tb)
// 		}
// 		fnSets = append(fnSets, fnSet)

// 		done, err := tb.expectAndSkipCommaOr(glob.KeySymbolRightBrace)
// 		if err != nil {
// 			return nil, err
// 		}
// 		if done {
// 			break
// 		}
// 	}

// 	err := tb.header.skip(glob.KeySymbolRightBrace)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	retSet, err = tb.Obj()
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	ret := ast.NewFnObj(ast.NewFnObj(ast.Atom(glob.KeywordFn), fnSets), []ast.Obj{retSet})

// 	return ret, nil
// }

// func (tb *tokenBlock) backSlashExpr() (ast.Obj, error) {
// 	err := tb.header.skip(glob.KeySymbolBackSlash)
// 	if err != nil {
// 		return nil, err
// 	}

// 	obj, err := tb.header.next()
// 	if err != nil {
// 		return nil, err
// 	}

// 	return ast.Atom(obj), nil
// }

// func (tb *tokenBlock) EnumSetObjOrIntensionalSetObj() (ast.Obj, error) {
// 	err := tb.header.skip(glob.KeySymbolLeftCurly)
// 	if err != nil {
// 		return nil, err
// 	}

// 	if tb.header.is(glob.KeySymbolRightCurly) {
// 		err = tb.header.skip(glob.KeySymbolRightCurly)
// 		if err != nil {
// 			return nil, err
// 		}
// 		return ast.MakeEnumSetObj([]ast.Obj{}), nil
// 	}

// 	obj, err := tb.Obj()
// 	if err != nil {
// 		return nil, err
// 	}

// 	if !tb.header.is(glob.KeySymbolComma) && !tb.header.is(glob.KeySymbolRightCurly) {
// 		return tb.intensionalSetObj(obj)
// 	} else {
// 		return tb.enumSetObj(obj)
// 	}
// }

// func (tb *tokenBlock) intensionalSetObj(paramAsObj ast.Obj) (ast.Obj, error) {
// 	param, ok := paramAsObj.(ast.Atom)
// 	if !ok {
// 		return nil, fmt.Errorf("expect parameter as atom")
// 	}

// 	if err := glob.IsValidUserDefinedNameWithoutPkgName(string(param)); err != nil {
// 		return nil, err
// 	}

// 	parentSet, err := tb.Obj()
// 	if err != nil {
// 		return nil, err
// 	}

// 	err = tb.header.skip(glob.KeySymbolColon)
// 	if err != nil {
// 		return nil, err
// 	}

// 	facts := []ast.FactStmt{}
// 	for !tb.header.is(glob.KeySymbolRightCurly) {
// 		curFact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals([]string{glob.KeySymbolRightCurly})
// 		if err != nil {
// 			return nil, err
// 		}
// 		// 检查如果是 forall fact，它的参数里不应该等于 param
// 		if uniFactParams := ast.ExtractParamsFromFact(curFact); uniFactParams != nil {
// 			for _, uniFactParam := range uniFactParams {
// 				if uniFactParam == string(param) {
// 					return nil, fmt.Errorf("parameter %s in forall fact conflicts with intensional set parameter %s", uniFactParam, string(param))
// 				}
// 			}
// 		}
// 		facts = append(facts, curFact)
// 	}

// 	// 跳过右花括号
// 	err = tb.header.skip(glob.KeySymbolRightCurly)
// 	if err != nil {
// 		return nil, err
// 	}

// 	return ast.MakeIntensionalSetObj(string(param), parentSet, facts), nil
// }

// func (tb *tokenBlock) enumSetObj(firstParam ast.Obj) (ast.Obj, error) {
// 	enumItems := []ast.Obj{firstParam}

// 	// 跳过第一个逗号（如果存在）
// 	tb.header.skipIfIs(glob.KeySymbolComma)

// 	// 循环读取后续对象，直到遇到右花括号
// 	for !tb.header.is(glob.KeySymbolRightCurly) {
// 		curItem, err := tb.Obj()
// 		if err != nil {
// 			return nil, err
// 		}
// 		enumItems = append(enumItems, curItem)

// 		// 跳过逗号（如果存在）
// 		tb.header.skipIfIs(glob.KeySymbolComma)
// 	}

// 	// 跳过右花括号
// 	err := tb.header.skip(glob.KeySymbolRightCurly)
// 	if err != nil {
// 		return nil, err
// 	}

// 	return ast.MakeEnumSetObj(enumItems), nil
// }
