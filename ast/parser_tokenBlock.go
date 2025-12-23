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

type tokenBlock struct {
	header strSliceCursor
	body   []tokenBlock

	line uint // header 的行数
}

func newTokenBlock(header strSliceCursor, body []tokenBlock, line uint) *tokenBlock {
	return &tokenBlock{
		header: header,
		body:   body,
		line:   line + 1,
	}
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

// MakeTokenBlocks 合并 tokenization 和 scope 解析的入口函数
func MakeTokenBlocks(lines []string) ([]tokenBlock, error) {
	t := newTokenizerWithScope(lines)
	return t.parseBlocks(0)
}

func (tb *tokenBlock) TokenAtHeaderIndexIs(index int, kw string) bool {
	return index < len(tb.header.slice) && tb.header.slice[index] == kw
}

func (tb *tokenBlock) GetEnd() string {
	if len(tb.header.slice) == 0 {
		return ""
	}
	return tb.header.slice[len(tb.header.slice)-1]
}

func (tb *tokenBlock) EndWith(s string) bool {
	return tb.GetEnd() == s
}
