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

package litex_ast

import glob "golitex/glob"

type SpecFactEnum uint8

const (
	TruePure SpecFactEnum = iota
	FalsePure
	// TrueExist
	// FalseExist
	TrueExist_St
	FalseExist_St
)

func (stmt *SpecFactStmt) ReverseSpecFact() *SpecFactStmt {
	if stmt.TypeEnum == TruePure {
		return NewSpecFactStmt(FalsePure, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == FalsePure {
		return NewSpecFactStmt(TruePure, stmt.PropName, stmt.Params)
		// } else if stmt.TypeEnum == TrueExist {
		// 	return NewSpecFactStmt(FalseExist, stmt.PropName, stmt.Params)
		// } else if stmt.TypeEnum == FalseExist {
		// 	return NewSpecFactStmt(TrueExist, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == TrueExist_St {
		return NewSpecFactStmt(FalseExist_St, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == FalseExist_St {
		return NewSpecFactStmt(TrueExist_St, stmt.PropName, stmt.Params)
	}
	panic("unknown spec fact type")
}

func (f *SpecFactStmt) IsPropNameEqual() bool {
	return f.PropName.Name == glob.KeySymbolEqual && f.PropName.PkgName == glob.EmptyPkg
}

// func (f *SpecFactStmt) IsExistFact() bool {
// 	return f.TypeEnum == TrueExist || f.TypeEnum == FalseExist
// }

func (f *SpecFactStmt) IsPureFact() bool {
	return f.TypeEnum == TruePure || f.TypeEnum == FalsePure
}

func (f *SpecFactStmt) IsExist_St_Fact() bool {
	return f.TypeEnum == TrueExist_St || f.TypeEnum == FalseExist_St
}

func (f *SpecFactStmt) IsTrue() bool {
	// return f.TypeEnum == TruePure || f.TypeEnum == TrueExist || f.TypeEnum == TrueExist_St
	return f.TypeEnum == TruePure || f.TypeEnum == TrueExist_St
}

func (f *SpecFactStmt) Exist_St_SeparatorIndex() int {
	for i, param := range f.Params {
		paramAsAtom, ok := param.(*FcAtom)
		if ok && paramAsAtom.PkgName == glob.EmptyPkg && paramAsAtom.Name == glob.BuiltinExist_St_FactExistParamPropParmSep {
			return i
		}
	}
	return -1
}

func (f *SpecFactStmt) PropNameIsGiven_PkgNameEmpty(name FcAtom, givenName string) bool {
	return name.PkgName == glob.EmptyPkg && name.Name == givenName
}
