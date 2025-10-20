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
	"strings"
)

func (tb *tokenBlock) RawFc() (ast.Fc, error) {
	expr, err := tb.fcInfixExpr(glob.PrecLowest)
	if err != nil {
		return nil, err
	}

	return expr, nil
}

// “数学”优先级越高，越是底层。所以把括号表达式放在这里处理
func (tb *tokenBlock) fcAtomAndFcFn() (ast.Fc, error) {
	var expr ast.Fc
	var err error

	if tb.header.is(glob.KeywordFn) {
		return tb.fnSet()
	} else if tb.header.is(glob.KeySymbolLeftBrace) {
		expr, err = tb.bracedExpr_orTuple()
		if err != nil {
			return nil, err
		}
		return tb.whenTheNextTokIsLeftBrace_MakeFcFn(expr)
	} else if tb.header.curTokenBeginWithNumber() {
		expr, err = tb.numberStr()
		if err != nil {
			return nil, err
		}
		if tb.header.is(glob.KeySymbolLeftBrace) {
			return nil, fmt.Errorf("unexpected left brace after number")
		} else {
			return expr, nil
		}
	} else {
		fcStr, err := tb.rawFcAtom()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		ret, err := tb.whenTheNextTokIsLeftBrace_MakeFcFn(fcStr)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		return ret, nil
	}
}

func (tb *tokenBlock) rawFcAtom() (ast.FcAtom, error) {
	values := []string{}

	value, err := tb.header.next()
	if err != nil {
		return ast.FcAtom(""), err
	}

	for tb.header.is(glob.KeySymbolColonColon) {
		tb.header.skip(glob.KeySymbolColonColon)
		values = append(values, value)
		value, err = tb.header.next()
		if err != nil {
			return ast.FcAtom(""), err
		}
	}

	if glob.CurrentPkg != "" && !glob.IsBuiltinKeywordOrBuiltinSymbolOrNumber(value) {
		values = append([]string{glob.CurrentPkg}, values...)
	}

	values = append(values, value)

	return ast.FcAtom(strings.Join(values, glob.KeySymbolColonColon)), nil
}

func (tb *tokenBlock) fcInfixExpr(currentPrec glob.BuiltinOptPrecedence) (ast.Fc, error) {
	left, err := tb.unaryOptFc()
	if err != nil {
		return nil, err
	}

	for !tb.header.ExceedEnd() {
		curToken, err := tb.header.currentToken()
		if err != nil {
			return nil, fmt.Errorf("unexpected end of input while parsing infix expression")
		}

		if curToken == glob.KeySymbolBackSlash {
			// tb.header.skip("") // 消耗curToken

			// fn, err := tb.header.next() // 只允许 \ 后面跟 fcAtom 格式出现的 函数，而不是是 fcFn 格式出现的函数，否则 x \mul (y \mul z) 会被解析成 mul(mul(y,z))(x) 而不是 mul(x, mul(y, z))
			// if err != nil {
			// 	return nil, err
			// }

			// right, err := tb.fcInfixExpr(glob.PrecLowest)
			// if err != nil {
			// 	return nil, err
			// }

			// left = ast.NewFcFn(ast.FcAtom(fn), []ast.Fc{left, right})

			fn, err := tb.backSlashExpr()
			if err != nil {
				return nil, err
			}

			right, err := tb.fcInfixExpr(glob.PrecLowest)
			if err != nil {
				return nil, err
			}

			left = ast.NewFcFn(fn, []ast.Fc{left, right})

			break
		}

		// 检查是否是运算符
		curPrec, isBinary := glob.BuiltinOptPrecedenceMap[curToken]

		if !isBinary {
			break
		}

		if curPrec <= currentPrec {
			break
		}

		tb.header.skip("") // 消耗运算符
		right, err := tb.fcInfixExpr(curPrec)
		if err != nil {
			return nil, err
		}

		leftHead := ast.FcAtom(curToken)
		left = ast.NewFcFn(
			leftHead,
			[]ast.Fc{left, right},
		)
	}

	return left, nil
}

// TODO： 现在只有 - 是单目运算符，其他都是双目运算符。以后可能会添加其他单目运算符
func (tb *tokenBlock) unaryOptFc() (ast.Fc, error) {
	unaryOp, err := tb.header.currentToken()
	if err != nil {
		return nil, err
	}
	if unaryOp != glob.KeySymbolMinus {
		// return tb.squareBracketExpr()
		return tb.fcAtomAndFcFn()
	} else {
		tb.header.skip(unaryOp)

		// 如果后面跟的是逗号，那只返回 -
		if tb.header.is(glob.KeySymbolComma) {
			return ast.FcAtom(unaryOp), nil
		}

		right, err := tb.unaryOptFc()
		if err != nil {
			return nil, err
		}

		// 方法1： 返回 -1 * right，好处： -a 可以直接和 -5 对应，因为 -5 其实是 -1 * 5, -n是 -1 * n；缺点是，如果是 -1 * 5
		return ast.NewFcFn(ast.FcAtom(glob.KeySymbolStar), []ast.Fc{ast.FcAtom("-1"), right}), nil

		// 方法2： 如果right是数字，那返回 - right，否则是 -1 * right
		// if rightAtom, ok := right.(ast.FcAtom); ok && glob.IsNumLitStr(string(rightAtom)) {
		// 	return ast.FcAtom("-" + string(rightAtom)), nil
		// } else {
		// 	return ast.NewFcFn(ast.FcAtom(glob.KeySymbolStar), []ast.Fc{ast.FcAtom("-1"), right}), nil
		// }

	}
}

func (tb *tokenBlock) numberStr() (ast.FcAtom, error) {
	left, err := tb.header.next()
	if err != nil {
		return ast.FcAtom(""), err
	}

	// 检查left是否全是数字
	for _, c := range left {
		if c < '0' || c > '9' {
			return ast.FcAtom(""), fmt.Errorf("invalid number: %s", left)
		}
	}

	if tb.header.is(glob.KeySymbolDot) {
		// 检查下一个字符是否是数字
		nextChar := tb.header.strAtCurIndexPlus(1)
		if len(nextChar) == 0 {
			return ast.FcAtom(left), nil
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
				return ast.FcAtom(""), fmt.Errorf("invalid number: %s", right)
			}
			return ast.FcAtom(fmt.Sprintf("%s.%s", left, right)), nil
		} else {
			return ast.FcAtom(""), fmt.Errorf("invalid number: %s", left)
		}
		// return ast.FcAtom(left), nil
	} else {
		// 不能开头是0，除非你真的是0
		if left[0] == '0' && len(left) > 1 {
			return ast.FcAtom(""), fmt.Errorf("invalid number: %s", left)
		}

		return ast.FcAtom(left), nil
	}
}

func (tb *tokenBlock) bracedFcSlice() ([]ast.Fc, error) {
	params := []ast.Fc{}
	tb.header.skip(glob.KeySymbolLeftBrace)

	if !tb.header.is(glob.KeySymbolRightBrace) {
		for {
			fc, err := tb.RawFc()

			if err != nil {
				return nil, tbErr(err, tb)
			}

			params = append(params, fc)

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
				continue
			}

			if tb.header.is(glob.KeySymbolRightBrace) {
				break
			}

			return nil, tbErr(fmt.Errorf("expected ',' or '%s' but got '%s'", glob.KeySymbolRightBrace, tb.header.strAtCurIndexPlus(0)), tb)
		}
	}

	tb.header.skip(glob.KeySymbolRightBrace)

	return params, nil
}

// func (tb *tokenBlock) bracedExpr_orTuple() (ast.Fc, error) {
// 	tb.header.skip(glob.KeySymbolLeftBrace)
// 	if tb.header.ExceedEnd() {
// 		return nil, fmt.Errorf("unexpected end of input after '('")
// 	}

// 	// head, err := tb.fcInfixExpr(glob.PrecLowest)
// 	head, err := tb.RawFc()
// 	if err != nil {
// 		return nil, err
// 	}

// 	if tb.header.ExceedEnd() {
// 		return nil, fmt.Errorf("unexpected end of input, expected ')'")
// 	}

// 	if err := tb.header.skip(glob.KeySymbolRightBrace); err != nil {
// 		return nil, fmt.Errorf("expected '%s': %s", glob.KeySymbolRightBrace, err)
// 	}

// 	if !tb.header.is(glob.KeySymbolLeftBrace) {
// 		return head, nil
// 	}

// 	return head, nil

// }

func (tb *tokenBlock) bracedExpr_orTuple() (ast.Fc, error) {
	if err := tb.header.skip(glob.KeySymbolLeftBrace); err != nil {
		return nil, fmt.Errorf("expected '(': %s", err)
	}

	if tb.header.ExceedEnd() {
		return nil, fmt.Errorf("unexpected end of input after '('")
	}

	// Peek after first expression to check for comma
	firstExpr, err := tb.RawFc()
	if err != nil {
		return nil, err
	}

	// Check if it's a tuple: look for comma
	if tb.header.is(glob.KeySymbolComma) {
		// It's a tuple — collect all expressions until ')'
		exprs := []ast.Fc{firstExpr}
		for tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)

			if tb.header.is(glob.KeySymbolRightBrace) {
				// Allow trailing comma: (1, 2, 3,)
				break
			}

			nextExpr, err := tb.RawFc()
			if err != nil {
				return nil, err
			}
			exprs = append(exprs, nextExpr)
		}

		if err := tb.header.skip(glob.KeySymbolRightBrace); err != nil {
			return nil, fmt.Errorf("expected ')': %s", err)
		}

		return ast.NewFcFn(ast.FcAtom(glob.TupleFcFnHead), exprs), nil
	}

	// If no comma, expect a single expression followed by ')'
	if err := tb.header.skip(glob.KeySymbolRightBrace); err != nil {
		return nil, fmt.Errorf("expected ')': %s", err)
	}

	return firstExpr, nil
}

func (tb *tokenBlock) whenTheNextTokIsLeftBrace_MakeFcFn(head ast.Fc) (ast.Fc, error) {
	for !tb.header.ExceedEnd() && (tb.header.is(glob.KeySymbolLeftBrace)) {
		objParamsPtr, err := tb.bracedFcSlice()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		head = ast.NewFcFn(head, objParamsPtr)
	}

	return head, nil
}

func (tb *tokenBlock) fnSet() (ast.Fc, error) {
	tb.header.skip(glob.KeywordFn)
	tb.header.skip(glob.KeySymbolLeftBrace)

	fnSets := []ast.Fc{}
	var retSet ast.Fc
	for !tb.header.ExceedEnd() && !(tb.header.is(glob.KeySymbolRightBrace)) {
		fnSet, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		fnSets = append(fnSets, fnSet)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
			continue
		}
	}

	err := tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	retSet, err = tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	ret := ast.NewFcFn(ast.NewFcFn(ast.FcAtom(glob.KeywordFn), fnSets), []ast.Fc{retSet})

	return ret, nil
}

func ParseSourceCodeGetFc(s string) (ast.Fc, error) {
	blocks, err := makeTokenBlocks([]string{s})
	if err != nil {
		return nil, err
	}

	fc, err := blocks[0].RawFc()
	if err != nil {
		return nil, err
	}

	return fc, nil
}

func (tb *tokenBlock) backSlashExpr() (ast.Fc, error) {
	err := tb.header.skip(glob.KeySymbolBackSlash)
	if err != nil {
		return nil, err
	}

	fc, err := tb.header.next()
	if err != nil {
		return nil, err
	}

	// fc, err := tb.unaryOptFc()
	// if err != nil {
	// 	return nil, err
	// }

	// err = tb.header.skip(glob.KeySymbolBackSlash)
	// if err != nil {
	// 	return nil, err
	// }

	return ast.FcAtom(fc), nil
}
