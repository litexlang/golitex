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

import (
	glob "golitex/glob"
)

func GetForallXOnlyOneYSatisfyGivenProp(domSet, rangeSet Obj, propName AtomObj) *UniFactStmt {
	params := []string{"x", "y1", "y2"}
	setParams := []Obj{domSet, rangeSet, rangeSet}
	domFacts := []FactStmt{
		NewSpecFactStmt(TruePure, propName, []Obj{AtomObj("x"), AtomObj("y1")}, glob.InnerGenLine),
		NewSpecFactStmt(TruePure, propName, []Obj{AtomObj("x"), AtomObj("y2")}, glob.InnerGenLine),
	}
	thenFacts := []FactStmt{
		NewSpecFactStmt(TruePure, AtomObj(glob.LastTwoObjectsAreEqual), []Obj{AtomObj("x"), AtomObj("y1"), AtomObj("y2")}, glob.InnerGenLine),
	}
	return NewUniFact(params, setParams, domFacts, thenFacts, glob.InnerGenLine)
}
