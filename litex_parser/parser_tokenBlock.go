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

package litex_parser

import (
	"fmt"
	glob "golitex/litex_global"
	"strings"
)

type tokenBlock struct {
	header strSliceCursor
	body   []tokenBlock
}

func (b *tokenBlock) String() string {
	return b.stringWithIndent(0)
}

func (b *tokenBlock) stringWithIndent(indentLevel int) string {
	indent := strings.Repeat(glob.Scope4Indents, indentLevel) // 根据缩进级别生成缩进字符串
	result := fmt.Sprintf("%s%s\n", indent, strings.Join(b.header.getSlice(), " "))

	// 递归处理子块
	if b.body != nil {
		for _, subBlock := range b.body {
			result += subBlock.stringWithIndent(indentLevel + 1)
		}
	}

	return result
}

// makeTokenBlocks 合并 tokenization 和 scope 解析的入口函数
func makeTokenBlocks(lines []string) ([]tokenBlock, error) {
	t := newTokenizerWithScope(lines)
	return t.parseBlocks(0)
}
