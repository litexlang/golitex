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

package litex_verifier

import ast "golitex/ast"

// 在用uniFact来验证specFact时，这个已知的uniFact 可能形如 forall a x: $p(a,x)。然后我代入的x刚好是a。于是整个forall被instantiate成 forall a a: $p(a,a)。然后我要验证这个 forall a a: $p(a,a) 我发现a已经在外面定义go了，于是把它替换成了乱码ABCD, 然后变成验证 forall ABCD ABCD: $p(ABCD,ABCD)。总之就错了。避免这个的办法是，让knownUniFact先把param先随机化啦，然后再代入
func (ver *Verifier) instantiateUniFactWithoutDuplicate(oldStmt *ast.UniFactStmt) (*ast.UniFactStmt, error) {
	paramMap, paramMapStrToStr := processUniFactParamsDuplicateDeclared(ver.env, oldStmt.Params)

	if len(paramMap) == 0 {
		return oldStmt, nil
	}

	instantiatedOldStmt, err := ast.InstantiateUniFact(oldStmt, paramMap)
	if err != nil {
		return nil, err
	}

	newParams := []string{}
	for _, param := range oldStmt.Params {
		if newParam, ok := paramMapStrToStr[param]; ok {
			newParams = append(newParams, newParam)
		} else {
			newParams = append(newParams, param)
		}
	}

	newStmtPtr := ast.NewUniFact(newParams, instantiatedOldStmt.ParamSets, instantiatedOldStmt.DomFacts, instantiatedOldStmt.ThenFacts)

	return newStmtPtr, nil
}
