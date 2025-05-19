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
	ast "golitex/ast"
	"testing"
)

func sourceCodeToFc(sourceCode ...string) ([]ast.Fc, error) {
	blocks, err := makeTokenBlocks(sourceCode, NewParserEnv())
	if err != nil {
		return nil, err
	}

	ret := []ast.Fc{}
	for _, block := range blocks {
		cur, err := block.header.rawFc()
		if err != nil {
			return nil, err
		}
		ret = append(ret, cur)
	}

	return ret, nil
}

func TestOrder(t *testing.T) {
	fcSlice, err := sourceCodeToFc("1+2 + f(x)-f(y)")
	if err != nil {
		t.Fatal(err)
	}

	for _, fc := range fcSlice {
		orderedFc, _, _ := ast.IsNumberExpr_OrderIt(fc)
		if orderedFc == nil {
			t.Fatal("not a number expr")
		}
		fmt.Println(orderedFc.String())
	}
}
