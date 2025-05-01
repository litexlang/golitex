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

package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	mem "golitex/litex_memory"
)

// state 只能是 Round1 或者 Spec
func (ver *Verifier) specFactUni(knownFact *mem.StoredUniSpecFact, uniConMap map[string]ast.Fc, state VerState) (bool, error) {
	// 这里貌似不需要对整个uniFact实例化，只要实例化then
	insKnownUniFact, err := knownFact.UniFact.Instantiate(uniConMap)
	if err != nil {
		return false, err
	}
	insKnownUniFactAsUniFact, ok := insKnownUniFact.(*ast.ConUniFactStmt)
	if !ok {
		return false, fmt.Errorf("")
	}

	ok, err = ver.instUniFactDomFacts(insKnownUniFactAsUniFact, state)
	if err != nil {
		return false, err
	}

	return ok, nil
}

// * 如果是 dom 是 specfact，那就直接specFactspec，我不继续往下走，以避免n^2的检查；如果dom 是 uni，那如果现在我是 round1，我允许你往下走；我不确定这么干有没有问题。
// 下面这个 可以被证明
// prove:
//
//	know:
//	    forall x nat:
//	        forall y nat:
//	            $p(x,y)
//	        then:
//	            $q(x)
//	    forall y nat:
//	        $p(1,y)
//
// $q(1)
func (ver *Verifier) instUniFactDomFacts(insUniFact *ast.ConUniFactStmt, state VerState) (bool, error) {
	if state.isRound1() {
		for _, fact := range insUniFact.DomFacts {
			asSpecFact, ok := fact.(*ast.SpecFactStmt)
			if ok {
				ok, err := ver.SpecFactSpec(asSpecFact, state)
				if err != nil {
					return false, err
				}
				if !ok {
					return false, nil
				}
			} else {
				ok, err := ver.FactStmt(fact, state)
				if err != nil {
					return false, err
				}
				if !ok {
					return false, nil
				}
			}
		}
		return true, nil
	} else if state.isSpec() {
		for _, fact := range insUniFact.DomFacts {
			asSpecFact, ok := fact.(*ast.SpecFactStmt)
			if !ok {
				return false, nil
			}
			ok, err := ver.SpecFactSpec(asSpecFact, state)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}
		return true, nil
	} else {
		return false, fmt.Errorf("")
	}

}
