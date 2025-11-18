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

func (stmt *SpecFactStmt) ReplaceObj(oldObj Obj, newObj Obj) FactStmt {
	newParams := make([]Obj, len(stmt.Params))
	for i, param := range stmt.Params {
		newParams[i] = param.ReplaceObj(oldObj, newObj)
	}

	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams, stmt.GetLine())
}

func (stmt *UniFactStmt) ReplaceObj(oldObj Obj, newObj Obj) FactStmt {
	newParamSets := make([]Obj, len(stmt.ParamSets))
	for i, paramSet := range stmt.ParamSets {
		newParamSets[i] = paramSet.ReplaceObj(oldObj, newObj)
	}

	newDomFacts := make([]FactStmt, len(stmt.DomFacts))
	for i, domFact := range stmt.DomFacts {
		newDomFacts[i] = domFact.ReplaceObj(oldObj, newObj)
	}

	newThenFacts := make([]FactStmt, len(stmt.ThenFacts))
	for i, thenFact := range stmt.ThenFacts {
		newThenFacts[i] = thenFact.ReplaceObj(oldObj, newObj)
	}

	return NewUniFact(stmt.Params, newParamSets, newDomFacts, newThenFacts, stmt.Line)
}

func (stmt *UniFactWithIffStmt) ReplaceObj(oldObj Obj, newObj Obj) FactStmt {
	panic("")
}

func (stmt *OrStmt) ReplaceObj(oldObj Obj, newObj Obj) FactStmt {
	panic("")
}

func (stmt *EnumStmt) ReplaceObj(oldObj Obj, newObj Obj) FactStmt {
	panic("")
}

func (stmt *IntensionalSetStmt) ReplaceObj(oldObj Obj, newObj Obj) FactStmt {
	panic("")
}

func (stmt *EqualsFactStmt) ReplaceObj(oldObj Obj, newObj Obj) FactStmt {
	panic("")
}
