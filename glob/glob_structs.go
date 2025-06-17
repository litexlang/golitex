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
// Litex Zulip community: https://litex.zulipchat.com

package litex_global

type Map2D[T any] map[string]map[string]T

func (m Map2D[T]) Set(key1, key2 string, value T) {
	if _, ok := m[key1]; !ok {
		m[key1] = make(map[string]T)
	}
	m[key1][key2] = value
}

func (m Map2D[T]) Get(key1, key2 string) (T, bool) {
	if innerMap, ok := m[key1]; ok {
		if val, ok := innerMap[key2]; ok {
			return val, true
		}
	}
	var zero T
	return zero, false
}
