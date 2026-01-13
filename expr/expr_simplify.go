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
	"strings"
)

// Simplify 将算术表达式化简到最简形式
// 包括：展开括号、合并同类项、字典序排序、分数合并
func Simplify(expr string) string {
	expr = strings.TrimSpace(expr)
	if expr == "" {
		return ""
	}
	
	node := parseExpression(expr)
	simplified := simplifyNode(node)
	return simplified.String()
}

// Equal 比较两个表达式是否相等
// 通过将两个表达式都化简到最简形式，然后比较
func Equal(left, right string) bool {
	leftSimplified := Simplify(left)
	rightSimplified := Simplify(right)
	
	// 如果都是普通表达式（没有分数），直接比较字符串
	if !strings.Contains(leftSimplified, "/") && !strings.Contains(rightSimplified, "/") {
		return leftSimplified == rightSimplified
	}
	
	// 如果有分数，转换为分数形式比较
	leftFrac := toFraction(leftSimplified)
	rightFrac := toFraction(rightSimplified)
	
	// a/b = c/d 当且仅当 b*c = a*d
	// 即证明 b*c - a*d = 0
	leftNumerator := fmt.Sprintf("(%s) * (%s)", leftFrac.denominator, rightFrac.numerator)
	rightNumerator := fmt.Sprintf("(%s) * (%s)", leftFrac.numerator, rightFrac.denominator)
	
	leftSimplified = Simplify(leftNumerator)
	rightSimplified = Simplify(rightNumerator)
	
	return leftSimplified == rightSimplified
}

