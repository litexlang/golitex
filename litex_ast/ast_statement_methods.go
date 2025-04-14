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
	"fmt"
	glob "golitex/litex_global"
)

func (stmt *SpecFactStmt) ReverseIsTrue() *SpecFactStmt {
	return NewSpecFactStmt(!stmt.IsTrue, stmt.PropName, stmt.Params)
}

func (f *SpecFactStmt) IsEqualFact() bool {
	return f.PropName.Value == glob.KeySymbolEqual && f.PropName.PkgName == glob.BuiltinInfixPkgName
}

func ReverseIsTrue(fact FactStmt) (FactStmt, error) {
	switch fact := fact.(type) {
	case *SpecFactStmt:
		return fact.ReverseIsTrue(), nil
	case *CondFactStmt:
		return nil, fmt.Errorf("TODO: current version cannot reverse cond fact")
	case *ConUniFactStmt:
		return nil, fmt.Errorf("TODO: current version cannot reverse uni fact")
	default:
		panic("unknown fact type")
	}
}
