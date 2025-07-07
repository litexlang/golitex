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

package litex_ast

import glob "golitex/glob"

func (stmt *HaveSetByReplacementStmt) ForallXOnlyOneYSatisfyGivenProp() *UniFactStmt {
	params := []string{"x", "y1", "y2"}
	setParams := []Fc{stmt.DomSet, stmt.RangeSet, stmt.RangeSet}
	domFacts := []FactStmt{
		NewSpecFactStmt(TruePure, stmt.PropName, []Fc{FcAtom("x"), FcAtom("y1")}),
		NewSpecFactStmt(TruePure, stmt.PropName, []Fc{FcAtom("x"), FcAtom("y2")}),
	}
	thenFacts := []FactStmt{
		NewSpecFactStmt(TruePure, FcAtom(glob.LastTwoObjectsAreEqual), []Fc{FcAtom("x"), FcAtom("y1"), FcAtom("y2")}),
	}
	return NewUniFact(params, setParams, domFacts, thenFacts)
}
