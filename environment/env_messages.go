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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	"strings"
)

func duplicateDefError(name string) error {
	return fmt.Errorf("duplicate definition of %s", name)
}

func (knownSpecFact *KnownSpecFact_InLogicExpr) String() string {
	var builder strings.Builder
	builder.WriteString(knownSpecFact.LogicExpr.String())
	return builder.String()
}

func (knownSpecFact *KnownSpecFact_InUniFact) String() string {
	var builder strings.Builder
	builder.WriteString(knownSpecFact.UniFact.String())
	return builder.String()
}

func (knownSpecFact *SpecFact_InLogicExpr_InUniFact) String() string {
	var builder strings.Builder
	builder.WriteString(knownSpecFact.UniFact.String())
	return builder.String()
}

func AtomsInFactNotDeclaredMsg(fact ast.FactStmt) string {
	return fmt.Sprintf("some atoms in the following fact are undeclared:\n%s", fact)
}

func AtomsInFcNotDeclaredMsg(fc ast.Obj) string {
	return fmt.Sprintf("some atoms in %s are undeclared", fc)
}
