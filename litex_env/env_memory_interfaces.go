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

package litex_env

import ast "golitex/litex_ast"

type SpecFactMem struct {
	PureFacts         map[string]map[string][]KnownSpecFact
	NotPureFacts      map[string]map[string][]KnownSpecFact
	ExistFacts        map[string]map[string][]KnownSpecFact
	NotExistFacts     map[string]map[string][]KnownSpecFact
	Exist_St_Facts    map[string]map[string][]KnownSpecFact
	NotExist_St_Facts map[string]map[string][]KnownSpecFact
}

func (s SpecFactMem) NewFact(stmt *ast.SpecFactStmt) {
	// 要考虑pkgName和propName是否存在
	if _, ok := s.PureFacts[stmt.PropName.PkgName]; !ok {
		s.PureFacts[stmt.PropName.PkgName] = make(map[string][]KnownSpecFact)
	}
	if _, ok := s.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name]; !ok {
		s.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name] = []KnownSpecFact{}
	}
	s.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name] = append(s.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name], KnownSpecFact{stmt})
}

func (s SpecFactMem) GetSameEnum_Pkg_PropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact, bool) {
	if _, ok := s.PureFacts[stmt.PropName.PkgName]; !ok {
		return nil, false
	}
	if _, ok := s.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name]; !ok {
		return nil, false
	}
	return s.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name], true
}

type SpecFactInLogicExprMem struct {
	PureFacts         map[string]map[string][]KnownSpecFact_InLogicExpr
	NotPureFacts      map[string]map[string][]KnownSpecFact_InLogicExpr
	ExistFacts        map[string]map[string][]KnownSpecFact_InLogicExpr
	NotExistFacts     map[string]map[string][]KnownSpecFact_InLogicExpr
	Exist_St_Facts    map[string]map[string][]KnownSpecFact_InLogicExpr
	NotExist_St_Facts map[string]map[string][]KnownSpecFact_InLogicExpr
}
