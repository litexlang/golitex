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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_global

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
