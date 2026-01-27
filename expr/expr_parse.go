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
// Litex Zulip community: https://litexlang.zulipchat.com/join/c4e7foogy6paz2sghjnbov/

package litex_expr

import (
	"unicode"
)

// exprNode 表示表达式节点
type exprNode struct {
	typ      nodeType
	value    string        // 对于数字、变量、函数调用
	children []*exprNode   // 对于运算符节点
	operator string        // +, -, *, /, ^
}

type nodeType int

const (
	nodeNumber nodeType = iota
	nodeVariable
	nodeFunction
	nodeAdd
	nodeSubtract
	nodeMultiply
	nodeDivide
	nodePower
)

// token 表示词法单元
type token struct {
	typ   tokenType
	value string
}

type tokenType int

const (
	tokNumber tokenType = iota
	tokVariable
	tokOperator
	tokLParen
	tokRParen
	tokLBracket
	tokRBracket
	tokComma
	tokEOF
)

// tokenize 将字符串转换为 token 流
func tokenize(s string) []token {
	var tokens []token
	i := 0
	
	for i < len(s) {
		// 跳过空格
		if s[i] == ' ' || s[i] == '\t' {
			i++
			continue
		}
		
		// 操作符
		if isOperator(s[i]) {
			tokens = append(tokens, token{tokOperator, string(s[i])})
			i++
			continue
		}
		
		// 括号
		if s[i] == '(' {
			tokens = append(tokens, token{tokLParen, "("})
			i++
			continue
		}
		if s[i] == ')' {
			tokens = append(tokens, token{tokRParen, ")"})
			i++
			continue
		}
		
		if s[i] == ',' {
			tokens = append(tokens, token{tokComma, ","})
			i++
			continue
		}
		
		// 方括号（索引访问）
		if s[i] == '[' {
			tokens = append(tokens, token{tokLBracket, "["})
			i++
			continue
		}
		if s[i] == ']' {
			tokens = append(tokens, token{tokRBracket, "]"})
			i++
			continue
		}
		
		// 数字
		if unicode.IsDigit(rune(s[i])) || s[i] == '.' {
			j := i
			for j < len(s) && (unicode.IsDigit(rune(s[j])) || s[j] == '.' || s[j] == 'e' || s[j] == 'E' || (j > i && (s[j] == '+' || s[j] == '-'))) {
				j++
			}
			tokens = append(tokens, token{tokNumber, s[i:j]})
			i = j
			continue
		}
		
		// 变量或函数名
		if unicode.IsLetter(rune(s[i])) || s[i] == '_' {
			j := i
			for j < len(s) && (unicode.IsLetter(rune(s[j])) || unicode.IsDigit(rune(s[j])) || s[j] == '_') {
				j++
			}
			
			// 检查是否是函数调用（后面跟着左括号）
			k := j
			for k < len(s) && (s[k] == ' ' || s[k] == '\t') {
				k++
			}
			
			if k < len(s) && s[k] == '(' {
				// 这是函数调用，但我们现在只记录函数名，括号会在解析时处理
				tokens = append(tokens, token{tokVariable, s[i:j]}) // 函数名也作为变量类型处理
				i = j
				continue
			}
			
			tokens = append(tokens, token{tokVariable, s[i:j]})
			i = j
			continue
		}
		
		// 未知字符，跳过或报错
		i++
	}
	
	tokens = append(tokens, token{tokEOF, ""})
	return tokens
}

func isOperator(c byte) bool {
	return c == '+' || c == '-' || c == '*' || c == '/' || c == '^'
}

// parser 解析器
type parser struct {
	tokens []token
	pos    int
}

func parseExpression(s string) *exprNode {
	tokens := tokenize(s)
	p := &parser{tokens: tokens, pos: 0}
	return p.parseExpr()
}

// parseExpr 解析表达式（处理 +, -）
// expr = term { (+|-) term }
func (p *parser) parseExpr() *exprNode {
	node := p.parseTerm()
	
	for {
		if p.matchOperator("+") {
			right := p.parseTerm()
			node = &exprNode{typ: nodeAdd, operator: "+", children: []*exprNode{node, right}}
		} else if p.matchOperator("-") {
			right := p.parseTerm()
			node = &exprNode{typ: nodeSubtract, operator: "-", children: []*exprNode{node, right}}
		} else {
			break
		}
	}
	
	return node
}

// parseTerm 解析项（处理 *, /）
// term = factor { (*|/) factor }
func (p *parser) parseTerm() *exprNode {
	node := p.parseFactor()
	
	for {
		if p.matchOperator("*") {
			right := p.parseFactor()
			node = &exprNode{typ: nodeMultiply, operator: "*", children: []*exprNode{node, right}}
		} else if p.matchOperator("/") {
			right := p.parseFactor()
			node = &exprNode{typ: nodeDivide, operator: "/", children: []*exprNode{node, right}}
		} else {
			break
		}
	}
	
	return node
}

// parseFactor 解析因子（处理 ^, 括号, 函数调用）
// factor = base { ^ factor } | (expr) | number | variable | function(expr, ...)
func (p *parser) parseFactor() *exprNode {
	node := p.parseBase()
	
	// 处理指数运算（右结合）
	if p.matchOperator("^") {
		right := p.parseFactor()
		node = &exprNode{typ: nodePower, operator: "^", children: []*exprNode{node, right}}
	}
	
	return node
}

// parseBase 解析基础元素
func (p *parser) parseBase() *exprNode {
	if p.match(tokNumber) {
		val := p.prev().value
		return &exprNode{typ: nodeNumber, value: val}
	}
	
	if p.match(tokVariable) {
		varName := p.prev().value
		return p.parseFunctionOrVariable(varName)
	}
	
	if p.match(tokLParen) {
		node := p.parseExpr()
		if !p.match(tokRParen) {
			panic("missing closing parenthesis")
		}
		// 解析完括号后，继续处理可能的函数调用和索引访问
		return p.parseFunctionCallsAndIndices(node)
	}
	
	panic("unexpected token")
}

// parseFunctionOrVariable 解析函数调用或变量
// 支持链式调用 f(a)(b) 和索引访问 [1]
func (p *parser) parseFunctionOrVariable(varName string) *exprNode {
	var node *exprNode
	
	// 首先检查是否是函数调用
	if p.match(tokLParen) {
		// 解析函数参数
		var args []*exprNode
		if !p.match(tokRParen) {
			args = append(args, p.parseExpr())
			for p.match(tokComma) {
				args = append(args, p.parseExpr())
			}
			if !p.match(tokRParen) {
				panic("missing closing parenthesis in function call")
			}
		}
		
		// 创建函数调用节点
		node = &exprNode{typ: nodeFunction, value: varName, children: args}
	} else {
		// 普通变量
		node = &exprNode{typ: nodeVariable, value: varName}
	}
	
	// 继续处理可能的链式调用和索引访问
	return p.parseFunctionCallsAndIndices(node)
}

// parseFunctionCallsAndIndices 处理链式函数调用和索引访问
// 例如：f(a)(b)[1] 会被解析为链式调用
func (p *parser) parseFunctionCallsAndIndices(node *exprNode) *exprNode {
	for {
		// 检查是否有函数调用 (a)(b)...
		if p.match(tokLParen) {
			var args []*exprNode
			if !p.match(tokRParen) {
				args = append(args, p.parseExpr())
				for p.match(tokComma) {
					args = append(args, p.parseExpr())
				}
				if !p.match(tokRParen) {
					panic("missing closing parenthesis in function call")
				}
			}
			
			// 对于链式调用 f(a)(b)，我们需要创建嵌套的函数调用结构
			// 将当前节点作为新函数调用的"函数名"（实际上是一个函数调用节点）
			// 对于链式调用，我们使用 nodeFunction 类型，但 value 是前一个函数的字符串表示
			if node.typ == nodeFunction {
				// 如果已经是函数，创建嵌套的函数调用
				// f(a)(b) 表示：将 f(a) 作为函数，用 b 作为参数调用
				// 我们使用 nodeFunction，value 是 f(a) 的字符串表示，children 是 [b]
				funcName := node.String()
				node = &exprNode{typ: nodeFunction, value: funcName, children: args}
			} else {
				// 如果不是函数，创建新的函数调用
				funcName := node.String()
				node = &exprNode{typ: nodeFunction, value: funcName, children: args}
			}
			continue
		}
		
		// 检查是否有索引访问 [1]
		if p.match(tokLBracket) {
			indexExpr := p.parseExpr()
			if !p.match(tokRBracket) {
				panic("missing closing bracket in index access")
			}
			
			// 索引访问也作为函数调用处理（简化）
			// 例如 node[1] 处理为索引操作
			// 这里我们将索引作为函数调用的最后一个参数
			if node.typ == nodeFunction {
				node.children = append(node.children, indexExpr)
			} else {
				funcName := node.String()
				node = &exprNode{typ: nodeFunction, value: funcName, children: []*exprNode{indexExpr}}
			}
			continue
		}
		
		// 没有更多的函数调用或索引访问
		break
	}
	
	return node
}

func (p *parser) match(typ tokenType) bool {
	if p.pos < len(p.tokens) && p.tokens[p.pos].typ == typ {
		p.pos++
		return true
	}
	return false
}

func (p *parser) matchOperator(op string) bool {
	if p.pos < len(p.tokens) && p.tokens[p.pos].typ == tokOperator && p.tokens[p.pos].value == op {
		p.pos++
		return true
	}
	return false
}

func (p *parser) prev() token {
	return p.tokens[p.pos-1]
}

