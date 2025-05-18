package litex_comparator

import "fmt"

type exprNode struct {
	Opt   string
	Left  interface{} // *ExprNode 或 string 或 int
	Right interface{} // *ExprNode 或 string 或 int
}

func (e *exprNode) Simplify() interface{} {
	// 先递归化简子树
	if left, ok := e.Left.(*exprNode); ok {
		e.Left = left.Simplify()
	}
	if right, ok := e.Right.(*exprNode); ok {
		e.Right = right.Simplify()
	}

	// 处理加法合并同类项
	if e.Opt == "+" {
		// 尝试将加法转换为乘法形式
		if simplified := tryCombineTerms(e); simplified != nil {
			return simplified
		}
	}

	return e
}

// 尝试合并同类项
func tryCombineTerms(e *exprNode) interface{} {
	terms := flattenAddition(e)
	termMap := make(map[string]int)

	// 统计每个变量的系数
	for _, term := range terms {
		switch t := term.(type) {
		case string:
			termMap[t]++
		case int:
			// 常数项单独处理
			if _, ok := termMap["_const"]; !ok {
				termMap["_const"] = t
			} else {
				termMap["_const"] += t
			}
		case *exprNode:
			if t.Opt == "*" {
				// 处理系数*变量的情况
				if coeff, ok := t.Left.(int); ok {
					if varName, ok := t.Right.(string); ok {
						termMap[varName] += coeff
						continue
					}
				}
			}
			// 无法合并的项保留原样
			key := fmt.Sprintf("%v", t)
			termMap[key]++
		}
	}

	// 重建表达式树
	var result interface{}
	first := true

	// 处理常数项
	if constVal, ok := termMap["_const"]; ok && constVal != 0 {
		result = constVal
		first = false
		delete(termMap, "_const")
	}

	// 处理变量项
	for varName, coeff := range termMap {
		if varName == "_const" {
			continue
		}

		var term interface{}
		if coeff == 1 {
			if varName[0] == '(' { // 这是一个复杂表达式
				term = varName
			} else {
				term = varName
			}
		} else {
			if varName[0] == '(' { // 复杂表达式无法合并系数
				for i := 0; i < coeff; i++ {
					if first {
						result = varName
						first = false
					} else {
						result = &exprNode{Opt: "+", Left: result, Right: varName}
					}
				}
				continue
			} else {
				term = &exprNode{Opt: "*", Left: coeff, Right: varName}
			}
		}

		if first {
			result = term
			first = false
		} else {
			result = &exprNode{Opt: "+", Left: result, Right: term}
		}
	}

	// 如果没有项，返回0
	if result == nil {
		return 0
	}

	// 如果只有一个项，直接返回它
	if !first && len(termMap) == 0 {
		return result
	}

	return result
}

// 将加法表达式展平为项列表
func flattenAddition(e *exprNode) []interface{} {
	var terms []interface{}

	if e.Opt == "+" {
		leftTerms := []interface{}{}
		if left, ok := e.Left.(*exprNode); ok && left.Opt == "+" {
			leftTerms = flattenAddition(left)
		} else {
			leftTerms = append(leftTerms, e.Left)
		}

		rightTerms := []interface{}{}
		if right, ok := e.Right.(*exprNode); ok && right.Opt == "+" {
			rightTerms = flattenAddition(right)
		} else {
			rightTerms = append(rightTerms, e.Right)
		}

		terms = append(leftTerms, rightTerms...)
	} else {
		terms = append(terms, e)
	}

	return terms
}
