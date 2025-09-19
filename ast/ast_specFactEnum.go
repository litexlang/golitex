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

type SpecFactEnum uint8

const (
	TruePure SpecFactEnum = iota
	FalsePure
	TrueExist_St
	FalseExist_St
)

func (stmt *SpecFactStmt) ReverseTrue() *SpecFactStmt {
	if stmt.TypeEnum == TruePure {
		return NewSpecFactStmt(FalsePure, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == FalsePure {
		return NewSpecFactStmt(TruePure, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == TrueExist_St {
		return NewSpecFactStmt(FalseExist_St, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == FalseExist_St {
		return NewSpecFactStmt(TrueExist_St, stmt.PropName, stmt.Params)
	}
	return nil
}

func (f *SpecFactStmt) IsPropNameEqual() bool {
	return string(f.PropName) == glob.KeySymbolEqual
}

func (f *SpecFactStmt) IsPureFact() bool {
	return f.TypeEnum == TruePure || f.TypeEnum == FalsePure
}

func (f *SpecFactStmt) IsExist_St_Fact() bool {
	return f.TypeEnum == TrueExist_St || f.TypeEnum == FalseExist_St
}

func (f *SpecFactStmt) IsTrue() bool {
	return f.TypeEnum == TruePure || f.TypeEnum == TrueExist_St
}

func (f *SpecFactStmt) NameIs(givenName string) bool {
	return string(f.PropName) == givenName
}
