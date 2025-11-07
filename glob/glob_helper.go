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

package litex_global

import (
	"runtime"
	"strings"
)

func CopyMap[T any](src map[string]T) map[string]T {
	dst := make(map[string]T)
	for k, v := range src {
		dst[k] = v
	}
	return dst
}

func MergeMap[T any](from map[string]T, to map[string]T) map[string]T {
	for k, v := range from {
		to[k] = v
	}
	return to
}

func CopySlice[T any](src []T) []T {
	dst := make([]T, len(src))
	copy(dst, src)
	return dst
}

func numberToLetters(num int) string {
	result := ""
	for num > 0 {
		num-- // 调整为 0-based
		result = string(rune('a'+(num%26))) + result
		num /= 26
	}
	return result
}

func GenerateNamesLikeExcelColumnNames(n int) []string {
	names := make([]string, n)
	for i := 1; i <= n; i++ {
		names[i-1] = numberToLetters(i)
	}
	return names
}

// RemoveWindowsCarriageReturn 移除 Windows 换行符中的回车符(\r)，将 CRLF 转换为 LF
// 这样可以让 Windows 格式的代码在 Unix/Linux 系统上也能正常处理
func RemoveWindowsCarriageReturn(code string) string {
	if runtime.GOOS == "windows" {
		return strings.ReplaceAll(code, "\r", "")
	}
	return code
}

func AddWindowsCarriageReturn(code string) string {
	if runtime.GOOS == "windows" {
		return strings.ReplaceAll(code, "\n", "\r\n")
	}
	return code
}
