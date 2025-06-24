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

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
	num "golitex/number"
	"strings"
	"testing"
)

func sourceCodeToFc(sourceCode ...string) ([]ast.Fc, error) {
	blocks, err := makeTokenBlocks(sourceCode)
	if err != nil {
		return nil, err
	}

	ret := []ast.Fc{}
	for _, block := range blocks {
		cur, err := block.header.RawFc()
		if err != nil {
			return nil, err
		}
		ret = append(ret, cur)
	}

	return ret, nil
}

func TestOrder(t *testing.T) {
	sourceCode := []string{
		"1+2*(4+ t(x)(x)) + 9 + 4*F(t) + (x-y)*(a+b) + 1/2*x",
		"x + x",
		"2*x",
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
		bracketedStr := num.FcStringForParseAndExpandPolynomial(fc)
		fmt.Println(bracketedStr)
		ploy := num.ParseAndExpandPolynomial(bracketedStr)
		var parts []string
		for _, t := range ploy {
			parts = append(parts, t.String())
		}
		fmt.Println("Expanded:", strings.Join(parts, " + "))
	}
}

func TestFcDot(t *testing.T) {
	sourceCode := []string{
		"x.y",
		"x + y.z",
		"f(x.y)",
		"f(x.y).z",
		"f(x.y).z (a.b)", // 这里不报错，其实是有问题的
		"f(1.2).z",
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
		fmt.Println(fc)
	}
}

func TestColonColon(t *testing.T) {
	sourceCode := []string{
		"a::b",
		"a::b::c::d",
	}
	for _, code := range sourceCode {
		fc, err := ParseSourceCodeGetFc(code)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(fc.String())
		fmt.Println(fc.(*ast.FcAtom).PkgName)
		fmt.Println(fc.(*ast.FcAtom).Name)
	}
}
