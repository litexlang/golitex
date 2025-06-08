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
// Litex discord server: https://discord.gg/uvrHM7eS
// Litex zulip chat: https://litex.zulipchat.com/

package litex_num

import (
	"fmt"
	"strings"
	"testing"
)

func TestExpandExpression(t *testing.T) {
	// expr := "3*[x] + [f(x)]*[y/2] + ([x] + [y]) * [z] + 5*[x]"
	expr := "1 + 2 * 4 + [t(x)] + 9 + 4 * [F(t)]"
	fmt.Println("Input:", expr)
	poly := ParseAndExpandPolynomial(expr)

	var parts []string
	for _, t := range poly {
		parts = append(parts, t.String())
	}
	fmt.Println("Expanded:", strings.Join(parts, " + "))

}
