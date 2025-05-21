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
	num "golitex/number"
	"strings"
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
	sourceCode := []string{
		"1+2*(4+ t(x)(x)) + 9 + 4*F(t) + (x-y)*(a+b) ",
		"x + x",
	}
	fcSlice := []ast.Fc{}
	for _, code := range sourceCode {
		fc, err := sourceCodeToFc(code)
		if err != nil {
			t.Fatal(err)
		}
		fcSlice = append(fcSlice, fc...)
	}

	for _, fc := range fcSlice {
		bracketedStr := num.FcString(fc)
		fmt.Println(bracketedStr)
		ploy := num.ParseAndExpand(bracketedStr)
		var parts []string
		for _, t := range ploy {
			parts = append(parts, t.String())
		}
		fmt.Println("Expanded:", strings.Join(parts, " + "))

	}
}
