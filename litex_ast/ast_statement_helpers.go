// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_ast

import (
	glob "golitex/litex_global"
)

type SpecFactEnum uint8

const (
	TrueAtom SpecFactEnum = iota
	FalseAtom
	TrueExist
	FalseExist
	TrueHave
	FalseHave
)

func (stmt *SpecFactStmt) ReverseIsTrue() *SpecFactStmt {
	if stmt.TypeEnum == TrueAtom {
		return NewSpecFactStmt(FalseAtom, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == FalseAtom {
		return NewSpecFactStmt(TrueAtom, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == TrueExist {
		return NewSpecFactStmt(FalseExist, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == FalseExist {
		return NewSpecFactStmt(TrueExist, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == TrueHave {
		return NewSpecFactStmt(FalseHave, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == FalseHave {
		return NewSpecFactStmt(TrueHave, stmt.PropName, stmt.Params)
	}
	panic("unknown spec fact type")
}

func (f *SpecFactStmt) IsEqualFact() bool {
	return f.PropName.PropName == glob.KeySymbolEqual && f.PropName.PkgName == glob.BuiltinInfixPkgName
}
