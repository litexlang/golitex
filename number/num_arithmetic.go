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
	"sort"
	"strconv"
	"strings"
)

// Term 表示一个项，包含系数和符号列表
type Term struct {
	Coefficient float64
	Symbols     []string
}

// 展开表达式并返回排序后的多项式
func expandExpression(expr string) ([]Term, error) {
	// 分割表达式为各个部分
	parts := strings.Split(expr, " * ")

	var terms []Term
	terms = append(terms, Term{Coefficient: 1.0}) // 初始化为1.0

	for _, part := range parts {
		if part[0] == '(' && part[len(part)-1] == ')' {
			// 处理括号内的加法表达式
			inner := part[1 : len(part)-1]
			sumParts := strings.Split(inner, " + ")

			var newTerms []Term
			for _, t := range terms {
				for _, s := range sumParts {
					coef, err := strconv.ParseFloat(s, 64)
					if err != nil {
						// 如果不是数字，则作为符号处理
						newTerm := Term{
							Coefficient: t.Coefficient,
							Symbols:     append(append([]string{}, t.Symbols...), s),
						}
						newTerms = append(newTerms, newTerm)
					} else {
						// 是数字，乘以系数
						newTerm := Term{
							Coefficient: t.Coefficient * coef,
							Symbols:     append([]string{}, t.Symbols...),
						}
						newTerms = append(newTerms, newTerm)
					}
				}
			}
			terms = newTerms
		} else {
			// 处理乘法部分
			num, err := strconv.ParseFloat(part, 64)
			if err == nil {
				// 是数字，乘以所有项的系数
				for i := range terms {
					terms[i].Coefficient *= num
				}
			} else {
				// 是符号，添加到所有项的符号列表
				for i := range terms {
					terms[i].Symbols = append(terms[i].Symbols, part)
				}
			}
		}
	}

	// 合并同类项
	termMap := make(map[string]Term)
	for _, term := range terms {
		// 对符号进行排序以确保相同的符号组合有相同的key
		sort.Strings(term.Symbols)
		key := strings.Join(term.Symbols, "*")
		if existing, ok := termMap[key]; ok {
			existing.Coefficient += term.Coefficient
			termMap[key] = existing
		} else {
			termMap[key] = term
		}
	}

	// 转换为切片并排序
	var result []Term
	for _, term := range termMap {
		result = append(result, term)
	}

	// 按字典序排序
	sort.Slice(result, func(i, j int) bool {
		return strings.Join(result[i].Symbols, "*") < strings.Join(result[j].Symbols, "*")
	})

	return result, nil
}
