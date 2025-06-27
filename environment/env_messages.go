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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

func duplicateDefError(pkgName string, name string, keyword string) error {
	if pkgName == "" {
		return fmt.Errorf("duplicate definition of %s, it is a %s", name, keyword)
	} else {
		return fmt.Errorf("duplicate definition of %s in %s package, it is a %s", name, pkgName, keyword)
	}
}

func (env *Env) String() string {
	// TODO
	return ""
}

func (e *Env) AppendMsg2(s string) {
	e.Msgs = append(e.Msgs, s)
}

func (knownSpecFact *KnownSpecFact) String() string {
	// return knownSpecFact.Fact.String()
	var builder strings.Builder
	if knownSpecFact.EnvFact == nil {
		builder.WriteString(knownSpecFact.Fact.String())
		return builder.String()
	} else {
		builder.WriteString(knownSpecFact.EnvFact.String())
		return builder.String()
	}
}

func (knownSpecFact *KnownSpecFact_InLogicExpr) String() string {
	var builder strings.Builder
	if knownSpecFact.EnvFact == nil {
		builder.WriteString(knownSpecFact.LogicExpr.String())
		return builder.String()
	} else {
		builder.WriteString(glob.KeywordSuppose)
		builder.WriteString(" ")
		builder.WriteString(knownSpecFact.EnvFact.String())
		builder.WriteString(":")
		builder.WriteString("\n")
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(knownSpecFact.LogicExpr.String(), 1))
		return builder.String()
	}
}

func (knownSpecFact *KnownSpecFact_InUniFact) String() string {
	var builder strings.Builder
	if knownSpecFact.EnvFact == nil {
		builder.WriteString(knownSpecFact.UniFact.String())
		return builder.String()
	} else {
		builder.WriteString(glob.KeywordSuppose)
		builder.WriteString(" ")
		builder.WriteString(knownSpecFact.EnvFact.String())
		builder.WriteString(":")
		builder.WriteString("\n")
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(knownSpecFact.UniFact.String(), 1))
		return builder.String()
	}
}

func (knownSpecFact *SpecFact_InLogicExpr_InUniFact) String() string {
	var builder strings.Builder
	if knownSpecFact.EnvFact == nil {
		builder.WriteString(knownSpecFact.UniFact.String())
		return builder.String()
	} else {
		builder.WriteString(glob.KeywordSuppose)
		builder.WriteString(" ")
		builder.WriteString(knownSpecFact.EnvFact.String())
		builder.WriteString(":")
		builder.WriteString("\n")
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(knownSpecFact.UniFact.String(), 1))
		return builder.String()
	}
}

func AtomsInFactNotDeclaredMsg(fact ast.FactStmt) string {
	return fmt.Sprintf("some atoms in the following fact are undeclared:\n%s", fact.String())
}

func AtomsInFcNotDeclaredMsg(fc ast.Fc) string {
	return fmt.Sprintf("some atoms in %s are undeclared", fc.String())
}
