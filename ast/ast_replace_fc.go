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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_ast

func (stmt *SpecFactStmt) ReplaceFc(oldFc Fc, newFc Fc) FactStmt {
	newParams := make([]Fc, len(stmt.Params))
	for i, param := range stmt.Params {
		newParams[i] = param.ReplaceFc(oldFc, newFc)
	}

	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams, stmt.GetLine())
}

func (stmt *UniFactStmt) ReplaceFc(oldFc Fc, newFc Fc) FactStmt {
	newParamSets := make([]Fc, len(stmt.ParamSets))
	for i, paramSet := range stmt.ParamSets {
		newParamSets[i] = paramSet.ReplaceFc(oldFc, newFc)
	}

	newDomFacts := make([]FactStmt, len(stmt.DomFacts))
	for i, domFact := range stmt.DomFacts {
		newDomFacts[i] = domFact.ReplaceFc(oldFc, newFc)
	}

	newThenFacts := make([]FactStmt, len(stmt.ThenFacts))
	for i, thenFact := range stmt.ThenFacts {
		newThenFacts[i] = thenFact.ReplaceFc(oldFc, newFc)
	}

	return NewUniFact(stmt.Params, newParamSets, newDomFacts, newThenFacts)
}

func (stmt *UniFactWithIffStmt) ReplaceFc(oldFc Fc, newFc Fc) FactStmt {
	panic("")
}

func (stmt *OrStmt) ReplaceFc(oldFc Fc, newFc Fc) FactStmt {
	panic("")
}

func (stmt *EnumStmt) ReplaceFc(oldFc Fc, newFc Fc) FactStmt {
	panic("")
}

func (stmt *IntensionalSetStmt) ReplaceFc(oldFc Fc, newFc Fc) FactStmt {
	panic("")
}

func (stmt *EqualsFactStmt) ReplaceFc(oldFc Fc, newFc Fc) FactStmt {
	panic("")
}
