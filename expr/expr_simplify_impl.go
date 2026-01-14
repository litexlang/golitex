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
	"fmt"
	"sort"
	"strings"

	num "golitex/number"
)

// simplifyNode 化简表达式节点
func simplifyNode(node *exprNode) *exprNode {
	if node == nil {
		return nil
	}

	switch node.typ {
	case nodeNumber, nodeVariable:
		return node
	case nodeFunction:
		// 函数调用内部不变，只递归处理参数
		newArgs := make([]*exprNode, len(node.children))
		for i, arg := range node.children {
			newArgs[i] = simplifyNode(arg)
		}
		return &exprNode{typ: nodeFunction, value: node.value, children: newArgs}
	case nodeAdd:
		return simplifyAdd(node)
	case nodeSubtract:
		return simplifySubtract(node)
	case nodeMultiply:
		return simplifyMultiply(node)
	case nodeDivide:
		return simplifyDivide(node)
	case nodePower:
		return simplifyPower(node)
	default:
		return node
	}
}

// simplifyAdd 化简加法：按 + 和 - 分割，合并同类项
func simplifyAdd(node *exprNode) *exprNode {
	// 先递归处理子节点
	left := simplifyNode(node.children[0])
	right := simplifyNode(node.children[1])

	// 合并为加法节点，然后收集所有项
	addNode := &exprNode{typ: nodeAdd, operator: "+", children: []*exprNode{left, right}}
	allTerms := collectAllTerms(addNode)

	// 合并同类项（按用户要求的方法）
	merged := mergeLikeTermsV2(allTerms)

	// 如果没有任何项，返回 0
	if len(merged) == 0 {
		return &exprNode{typ: nodeNumber, value: "0"}
	}

	// 排序
	sorted := sortTerms(merged)

	// 如果有分数项，需要合并成分数形式
	if hasFraction(sorted) {
		return combineToFraction(sorted)
	}

	// 否则合并为加法表达式
	return combineTermsToAdd(sorted)
}

// simplifySubtract 化简减法：a - b = a + (-1) * b
func simplifySubtract(node *exprNode) *exprNode {
	left := simplifyNode(node.children[0])
	right := simplifyNode(node.children[1])

	// a - b 转换为 a + (-1) * b
	negOne := &exprNode{typ: nodeNumber, value: "-1"}
	negRight := &exprNode{typ: nodeMultiply, operator: "*", children: []*exprNode{negOne, right}}

	return simplifyAdd(&exprNode{typ: nodeAdd, operator: "+", children: []*exprNode{left, negRight}})
}

// simplifyMultiply 化简乘法：展开后合并
func simplifyMultiply(node *exprNode) *exprNode {
	left := simplifyNode(node.children[0])
	right := simplifyNode(node.children[1])

	// 将两个节点展开为项列表
	leftTerms := expandToTerms(left)
	rightTerms := expandToTerms(right)

	// 交叉相乘所有项
	var resultTerms []*term
	for _, lt := range leftTerms {
		for _, rt := range rightTerms {
			resultTerms = append(resultTerms, multiplyTerms(lt, rt))
		}
	}

	// 合并同类项并排序
	merged := mergeLikeTerms(resultTerms)
	sorted := sortTerms(merged)

	// 如果只有一项，直接返回该项的节点
	if len(sorted) == 1 {
		return termToNode(sorted[0])
	}

	// 如果有分数项，需要合并成分数形式
	if hasFraction(sorted) {
		return combineToFraction(sorted)
	}

	// 否则合并为加法表达式
	return combineTermsToAdd(sorted)
}

// simplifyDivide 化简除法：保持为分数形式
func simplifyDivide(node *exprNode) *exprNode {
	num := simplifyNode(node.children[0])
	den := simplifyNode(node.children[1])

	// 除法保持为分数形式
	return &exprNode{typ: nodeDivide, operator: "/", children: []*exprNode{num, den}}
}

// simplifyPower 化简指数：保持形式不变（除非是特殊情况）
func simplifyPower(node *exprNode) *exprNode {
	base := simplifyNode(node.children[0])
	exp := simplifyNode(node.children[1])
	return &exprNode{typ: nodePower, operator: "^", children: []*exprNode{base, exp}}
}

// term 表示一个项（可以是分数形式）
// 使用 scalar * element / denominator 的形式
// 例如：2 * f(a) → scalar: "2", element: f(a), denominator: [1]
//      f(a) * 3 → scalar: "3", element: f(a), denominator: [1]
//      f(a) → scalar: "1", element: f(a), denominator: [1]
type term struct {
	scalar     string       // 标量系数（字符串，用于数字计算）
	element    *exprNode    // 元素部分（变量、函数调用等，或乘积节点）
	denominator []*exprNode // 分母部分（用于分数，如果没有分数则为 [1]）
}

// convertNodesToTerm 将节点列表转换为 term（scalar, element 形式）
// 将数字节点提取为 scalar，非数字节点组合为 element
func convertNodesToTerm(nodes []*exprNode, denominator []*exprNode) *term {
	var scalarNodes []*exprNode
	var elementNodes []*exprNode
	
	for _, node := range nodes {
		if node.typ == nodeNumber {
			scalarNodes = append(scalarNodes, node)
		} else {
			elementNodes = append(elementNodes, node)
		}
	}
	
	// 计算 scalar（所有数字节点的乘积）
	scalar := "1"
	for _, node := range scalarNodes {
		scalar = num.MulDecimalStr(scalar, node.value)
	}
	
	// 构建 element（非数字节点的乘积）
	var element *exprNode
	if len(elementNodes) == 0 {
		// 如果没有任何非数字节点，element 为 1
		element = &exprNode{typ: nodeNumber, value: "1"}
	} else if len(elementNodes) == 1 {
		element = elementNodes[0]
	} else {
		// 多个节点，组合为乘法节点
		element = multiplyNodes(elementNodes)
	}
	
	return &term{
		scalar:     scalar,
		element:    element,
		denominator: denominator,
	}
}

// expandToTerms 将节点展开为项的列表
func expandToTerms(node *exprNode) []*term {
	switch node.typ {
	case nodeNumber, nodeVariable, nodeFunction:
		// 单个节点：根据类型设置 scalar 和 element
		var scalar string
		var element *exprNode
		if node.typ == nodeNumber {
			scalar = node.value
			element = &exprNode{typ: nodeNumber, value: "1"}
		} else {
			scalar = "1"
			element = node
		}
		return []*term{{scalar: scalar, element: element, denominator: []*exprNode{&exprNode{typ: nodeNumber, value: "1"}}}}
	case nodeAdd:
		// 加法：展开左右两边并合并
		leftTerms := expandToTerms(node.children[0])
		rightTerms := expandToTerms(node.children[1])
		return append(leftTerms, rightTerms...)
	case nodeSubtract:
		// 减法：a - b 转换为 a + (-1) * b
		leftTerms := expandToTerms(node.children[0])
		rightTerms := expandToTerms(node.children[1])
		// 将右项的 scalar 乘以 -1
		var negRightTerms []*term
		for _, rt := range rightTerms {
			negScalar := num.MulDecimalStr("-1", rt.scalar)
			negRightTerms = append(negRightTerms, &term{
				scalar:     negScalar,
				element:    rt.element,
				denominator: rt.denominator,
			})
		}
		return append(leftTerms, negRightTerms...)
	case nodeMultiply:
		// 乘法：需要分配
		leftTerms := expandToTerms(node.children[0])
		rightTerms := expandToTerms(node.children[1])
		var result []*term
		for _, lt := range leftTerms {
			for _, rt := range rightTerms {
				// 合并两个项：scalar 相乘，element 相乘，denominator 相乘
				newScalar := num.MulDecimalStr(lt.scalar, rt.scalar)
				newElement := multiplyElementNodes(lt.element, rt.element)
				newDen := append([]*exprNode{}, lt.denominator...)
				newDen = append(newDen, rt.denominator...)
				// 规范化 denominator：如果所有节点都是 1，只保留一个 [1]
				newDen = normalizeDenominator(newDen)
				result = append(result, &term{scalar: newScalar, element: newElement, denominator: newDen})
			}
		}
		return result
	case nodeDivide:
		// 除法：转换为分数形式
		numTerms := expandToTerms(node.children[0])
		denTerms := expandToTerms(node.children[1])
		var result []*term
		for _, nt := range numTerms {
			for _, dt := range denTerms {
				// a/b / c/d = (a*d)/(b*c)
				// scalar 保持不变，element 保持不变
				newDen := append([]*exprNode{}, nt.denominator...)
				newDen = append(newDen, dt.element)
				// 将 dt.denominator 移到分子（实际上保持 scalar 和 element 不变，只调整 denominator）
				result = append(result, &term{
					scalar:     nt.scalar,
					element:    nt.element,
					denominator: newDen,
				})
			}
		}
		return result
	case nodePower:
		// 指数：保持形式不变，作为原子项
		return []*term{{scalar: "1", element: node, denominator: []*exprNode{&exprNode{typ: nodeNumber, value: "1"}}}}
	default:
		return []*term{{scalar: "1", element: node, denominator: []*exprNode{&exprNode{typ: nodeNumber, value: "1"}}}}
	}
}

// multiplyElementNodes 将两个 element 节点相乘
func multiplyElementNodes(e1, e2 *exprNode) *exprNode {
	// 如果 element 是 1，直接返回另一个
	if isOne(e1) {
		return e2
	}
	if isOne(e2) {
		return e1
	}
	// 否则创建乘法节点
	return &exprNode{typ: nodeMultiply, operator: "*", children: []*exprNode{e1, e2}}
}

// multiplyTerms 两个项相乘
func multiplyTerms(t1, t2 *term) *term {
	// scalar 相乘，element 相乘，denominator 相乘
	newScalar := num.MulDecimalStr(t1.scalar, t2.scalar)
	newElement := multiplyElementNodes(t1.element, t2.element)
	newDen := append([]*exprNode{}, t1.denominator...)
	newDen = append(newDen, t2.denominator...)
	// 规范化 denominator：如果所有节点都是 1，只保留一个 [1]
	newDen = normalizeDenominator(newDen)
	return &term{scalar: newScalar, element: newElement, denominator: newDen}
}

// extractCoeffAndVars 从项的分子中提取系数和变量部分
// 返回：(系数字符串, 变量部分节点列表)
func extractCoeffAndVars(numerator []*exprNode) (string, []*exprNode) {
	var coeffNodes []*exprNode
	var varNodes []*exprNode

	for _, node := range numerator {
		if node.typ == nodeNumber {
			coeffNodes = append(coeffNodes, node)
		} else {
			varNodes = append(varNodes, node)
		}
	}

	// 计算系数（所有数字节点的乘积）
	coeff := "1"
	for _, node := range coeffNodes {
		coeff = num.MulDecimalStr(coeff, node.value)
	}

	return coeff, varNodes
}

// termVarKey 生成项的变量部分 key（用于识别同类项，不包括系数）
func termVarKey(t *term) string {
	// 使用 element 的字符串表示作为 key
	elementKey := nodeToString(t.element)

	// 分母部分也需要考虑
	denVarKey := termPartString(t.denominator)

	// 如果分母不是 1，则包含在 key 中
	if denVarKey != "1" && denVarKey != "" {
		return fmt.Sprintf("%s/%s", elementKey, denVarKey)
	}

	return elementKey
}

// collectAllTerms 从加法/减法表达式中收集所有项
// 按 + 和 - 分割表达式，将每个项转换为 scalar-term pair
func collectAllTerms(node *exprNode) []*term {
	switch node.typ {
	case nodeAdd:
		// 递归收集左右两边的项
		leftTerms := collectAllTerms(node.children[0])
		rightTerms := collectAllTerms(node.children[1])
		return append(leftTerms, rightTerms...)
	case nodeSubtract:
		// a - b 转换为 a + (-1) * b
		leftTerms := collectAllTerms(node.children[0])
		rightTerms := collectAllTerms(node.children[1])
		// 将右项的 scalar 乘以 -1
		var negRightTerms []*term
		for _, rt := range rightTerms {
			negScalar := num.MulDecimalStr("-1", rt.scalar)
			negRightTerms = append(negRightTerms, &term{
				scalar:     negScalar,
				element:    rt.element,
				denominator: rt.denominator,
			})
		}
		return append(leftTerms, negRightTerms...)
	default:
		// 其他类型（数字、变量、函数、乘法、除法等），展开为项
		return expandToTerms(node)
	}
}

// mergeLikeTermsV2 按照用户要求的方法合并同类项
// 1. 得到所有 scalar-term pairs
// 2. 如果 term 相同，合并 scalar
// 3. 如果 scalar 为 0，移除该项
func mergeLikeTermsV2(terms []*term) []*term {
	if len(terms) == 0 {
		return terms
	}

	// 使用 termVarKey 来分组同类项
	termMap := make(map[string]*term)

	for _, t := range terms {
		key := termVarKey(t)
		
		if existing, exists := termMap[key]; exists {
			// 合并 scalar
			existing.scalar = num.AddDecimalStr(existing.scalar, t.scalar)
		} else {
			// 创建新的项（复制以避免修改原项）
			termMap[key] = &term{
				scalar:     t.scalar,
				element:    t.element,
				denominator: append([]*exprNode{}, t.denominator...),
			}
		}
	}

	// 收集结果，移除 scalar 为 0 的项
	var result []*term
	for _, t := range termMap {
		if t.scalar != "0" {
			result = append(result, t)
		}
	}

	return result
}

// mergeLikeTerms 合并同类项
func mergeLikeTerms(terms []*term) []*term {
	if len(terms) == 0 {
		return terms
	}

	// 使用变量部分的 key 来分组同类项
	termGroups := make(map[string][]*term)

	for _, t := range terms {
		key := termVarKey(t)
		termGroups[key] = append(termGroups[key], t)
	}

	var result []*term
	for _, group := range termGroups {
		if len(group) == 1 {
			result = append(result, group[0])
		} else {
			// 合并同类项
			merged := mergeTermsInGroup(group)
			if merged != nil {
				result = append(result, merged)
			}
		}
	}

	return result
}

// mergeTermsInGroup 合并一组同类项
func mergeTermsInGroup(terms []*term) *term {
	if len(terms) == 0 {
		return nil
	}

	// 使用第一个项作为模板（element 和 denominator 相同）
	template := terms[0]

	// 累加所有项的 scalar
	totalScalar := template.scalar
	for i := 1; i < len(terms); i++ {
		totalScalar = num.AddDecimalStr(totalScalar, terms[i].scalar)
	}

	// 如果 scalar 为 0，返回 nil（表示该项被抵消）
	if totalScalar == "0" {
		return nil
	}

	// 构建新的项（scalar 累加，element 和 denominator 保持不变）
	return &term{
		scalar:     totalScalar,
		element:    template.element,
		denominator: template.denominator,
	}
}

// termKey 生成项的 key（用于排序，包括 scalar）
func termKey(t *term) string {
	elementStr := nodeToString(t.element)
	denStr := termPartString(t.denominator)
	return fmt.Sprintf("%s*%s/%s", t.scalar, elementStr, denStr)
}

func termPartString(parts []*exprNode) string {
	var strs []string
	for _, p := range parts {
		strs = append(strs, nodeToString(p))
	}
	sort.Strings(strs)
	return strings.Join(strs, "*")
}

// sortTerms 对项进行字典序排序
func sortTerms(terms []*term) []*term {
	sort.Slice(terms, func(i, j int) bool {
		return termKey(terms[i]) < termKey(terms[j])
	})
	return terms
}

// hasFraction 检查是否有分数项
func hasFraction(terms []*term) bool {
	for _, t := range terms {
		if len(t.denominator) > 1 || (len(t.denominator) == 1 && !isOne(t.denominator[0])) {
			return true
		}
	}
	return false
}

func isOne(node *exprNode) bool {
	if node == nil {
		return false
	}
	if node.typ == nodeNumber {
		// 检查是否是 1（包括 "1", "1.0", "1.00" 等）
		val := strings.TrimSpace(node.value)
		return val == "1" || val == "1.0" || val == "1.00" || val == "+1"
	}
	// 如果是乘法节点，检查所有子节点是否都是 1
	if node.typ == nodeMultiply {
		for _, child := range node.children {
			if !isOne(child) {
				return false
			}
		}
		return len(node.children) > 0
	}
	return false
}

// normalizeDenominator 规范化 denominator：如果所有节点都是 1，只保留一个 [1]
func normalizeDenominator(den []*exprNode) []*exprNode {
	if len(den) == 0 {
		return []*exprNode{&exprNode{typ: nodeNumber, value: "1"}}
	}
	
	// 检查是否所有节点都是 1
	allOnes := true
	for _, node := range den {
		if !isOne(node) {
			allOnes = false
			break
		}
	}
	
	// 如果所有节点都是 1，只返回一个 [1]
	if allOnes {
		return []*exprNode{&exprNode{typ: nodeNumber, value: "1"}}
	}
	
	// 否则返回原数组
	return den
}

// combineToFraction 将项合并为一个分数
func combineToFraction(terms []*term) *exprNode {
	// 将所有项转换为 a/b 的形式，然后合并为 (a1*b2 + a2*b1) / (b1*b2) 的形式
	// 如果所有项的分母都是1，应该使用 combineTermsToAdd 而不是 combineToFraction
	// 这个函数只在真正有分数的情况下才被调用

	if len(terms) == 0 {
		return &exprNode{typ: nodeNumber, value: "0"}
	}

	if len(terms) == 1 {
		return termToFractionNode(terms[0])
	}

	// 多个项的情况：需要通分
	// 暂时使用 combineTermsToAdd 的逻辑，因为真正的通分实现比较复杂
	// 未来可以优化为真正的通分
	return combineTermsToAdd(terms)
}

// combineTermsToAdd 将项列表合并为加法表达式
func combineTermsToAdd(terms []*term) *exprNode {
	if len(terms) == 0 {
		return &exprNode{typ: nodeNumber, value: "0"}
	}

	if len(terms) == 1 {
		return termToNode(terms[0])
	}

	result := termToNode(terms[0])
	for i := 1; i < len(terms); i++ {
		result = &exprNode{typ: nodeAdd, operator: "+", children: []*exprNode{result, termToNode(terms[i])}}
	}

	return result
}

// termToNode 将项转换为节点
func termToNode(t *term) *exprNode {
	// 先计算分母节点
	denNode := multiplyNodes(t.denominator)

	// 构建分子：scalar * element
	var numNode *exprNode
	if t.scalar == "1" {
		numNode = t.element
	} else if t.scalar == "-1" {
		// -1 * element = -element
		if t.element.typ == nodeNumber && t.element.value == "1" {
			numNode = &exprNode{typ: nodeNumber, value: "-1"}
		} else {
			numNode = &exprNode{typ: nodeMultiply, operator: "*", children: []*exprNode{&exprNode{typ: nodeNumber, value: "-1"}, t.element}}
		}
	} else {
		scalarNode := &exprNode{typ: nodeNumber, value: t.scalar}
		if isOne(t.element) {
			numNode = scalarNode
		} else {
			numNode = &exprNode{typ: nodeMultiply, operator: "*", children: []*exprNode{scalarNode, t.element}}
		}
	}

	// 检查分母是否为 1
	if isOne(denNode) {
		return numNode
	}

	// 分母不是 1，需要创建分数形式
	return &exprNode{typ: nodeDivide, operator: "/", children: []*exprNode{numNode, denNode}}
}

func termToFractionNode(t *term) *exprNode {
	return termToNode(t)
}

// multiplyNodes 将节点列表相乘
func multiplyNodes(nodes []*exprNode) *exprNode {
	if len(nodes) == 0 {
		return &exprNode{typ: nodeNumber, value: "1"}
	}
	if len(nodes) == 1 {
		return nodes[0]
	}

	result := nodes[0]
	for i := 1; i < len(nodes); i++ {
		result = &exprNode{typ: nodeMultiply, operator: "*", children: []*exprNode{result, nodes[i]}}
	}
	return result
}

// nodeToString 将节点转换为字符串
func (n *exprNode) String() string {
	return nodeToString(n)
}

func nodeToString(node *exprNode) string {
	if node == nil {
		return ""
	}

	switch node.typ {
	case nodeNumber, nodeVariable:
		return node.value
	case nodeFunction:
		var args []string
		for _, arg := range node.children {
			args = append(args, nodeToString(arg))
		}
		return fmt.Sprintf("%s(%s)", node.value, strings.Join(args, ", "))
	case nodeAdd, nodeSubtract, nodeMultiply, nodeDivide:
		if len(node.children) != 2 {
			return ""
		}
		left := nodeToString(node.children[0])
		right := nodeToString(node.children[1])

		// 根据运算符添加括号（简化处理）
		return fmt.Sprintf("(%s %s %s)", left, node.operator, right)
	case nodePower:
		if len(node.children) != 2 {
			return ""
		}
		base := nodeToString(node.children[0])
		exp := nodeToString(node.children[1])
		return fmt.Sprintf("(%s ^ %s)", base, exp)
	default:
		return ""
	}
}

// fraction 表示分数形式
type fraction struct {
	numerator   string
	denominator string
}

// toFraction 将表达式转换为分数形式
func toFraction(expr string) fraction {
	// 简化实现：检查是否包含 "/"
	if strings.Contains(expr, "/") {
		parts := strings.SplitN(expr, "/", 2)
		return fraction{numerator: strings.TrimSpace(parts[0]), denominator: strings.TrimSpace(parts[1])}
	}

	return fraction{numerator: expr, denominator: "1"}
}
