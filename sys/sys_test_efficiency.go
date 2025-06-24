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

package litex_sys

import (
	"fmt"
	"testing"
	"time"
)

func TestRun(t *testing.T) {
	type testStruct struct {
		field1 string
		field2 string
	}
	var v testStruct = testStruct{"", "s"}
	var v2 testStruct = testStruct{"", "2"}
	var v3 testStruct = testStruct{"", "s"}
	startTime := time.Now()
	for i := 0; i < 1000000000; i++ {
		_ = v.field1 == v2.field1 && v.field2 == v2.field2
	}
	for i := 0; i < 1000000000; i++ {
		_ = v.field1 == v3.field1 && v.field2 == v3.field2
	}
	timeTaken := time.Since(startTime)
	fmt.Println(timeTaken)

	startTime = time.Now()
	s1 := "s"
	s2 := "2"
	s3 := "s"
	for i := 0; i < 1000000000; i++ {
		_ = s1 == s2
	}
	for i := 0; i < 1000000000; i++ {
		_ = s1 == s3
	}
	timeTaken = time.Since(startTime)
	fmt.Println(timeTaken)
}
