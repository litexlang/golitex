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

// 如果我尝试通过逐个子命题 m 的方式，使用“其余为假，m 为真”的方法去验证 a ∨ b ∨ c ∨ ... ∨ n，但全部尝试都失败了，那就可以断言 a ∨ b ∨ c ∨ ... ∨ n 为假。反过来，只要有一次成立了，那就可以断言 a ∨ b ∨ c ∨ ... ∨ n 为真。

// 反过来，用已知的 a ∨ b ∨ c ∨ ... ∨ n 为真，去验证 a ，需要先验证b, c, ... , n 为假，才能得到 a 为真。

func (ver *Verifier) verOrStmt(stmt *ast.OrStmt, state VerState) (bool, error) {
	nextState := state.addRound()
	for i := range stmt.Facts {
		ok, err := ver.verFactAtIndex_WhenOthersAreFalse(stmt.Facts, i, nextState)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) verFactAtIndex_WhenOthersAreFalse(facts []ast.SpecFactStmt, i int, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchProp)
	defer ver.deleteEnvAndRetainMsg()

	for j := range facts {
		if j == i {
			continue
		}
		err := ver.env.NewFact(facts[j].ReverseTrue())
		if err != nil {
			return false, err
		}
	}

	ok, err := ver.VerFactStmt(&facts[i], state)
	if err != nil {
		return false, err
	}
	return ok, nil
}
