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

type TopStmt struct {
	Stmt  Stmt
	IsPub bool
}

type DefObjStmt struct {
	Objs    []string
	ObjSets []Fc
	Facts   []FactStmt
	// ParamInSetsFacts []FactStmt
}

type DefHeader struct {
	Name      string
	Params    []string
	SetParams []Fc
	// ParamInSetsFacts []FactStmt
}

type DefPropStmt struct {
	DefHeader DefHeader
	DomFacts  []FactStmt // 如果输入的参数不满足dom，那就是error
	IffFacts  []FactStmt
	// IsCommutative bool
}

type DefExistPropStmtBody struct {
	DefHeader DefHeader
	DomFacts  []FactStmt
	// 必须是 iff，因为 not exist XXX <=> forall not XXX，而 not XXX 要求 XXX 是 logic_or_spec_stmt
	IffFacts []LogicOrSpec_Stmt
}

type DefExistPropStmt struct {
	DefBody     DefExistPropStmtBody
	ExistParams []string
	// ExistParamSets   []Fc
	ExistInSetsFacts []FactStmt
}

type DefFnStmt struct {
	DefHeader DefHeader
	DomFacts  []FactStmt
	ThenFacts []FactStmt
	RetSet    Fc
}

type UniFactStmt struct {
	Params    []string
	ParamSets []Fc
	DomFacts  []FactStmt
	ThenFacts []FactStmt
	IffFacts  []FactStmt // TODO: 需要注意到，我存储的所有事实，这一项都是空。未来为了节约空间，可以考虑用新的结构体来存储
	// ParamInSetsFacts []FactStmt
}

type SpecFactStmt struct {
	TypeEnum SpecFactEnum
	PropName FcAtom
	Params   []Fc
}

type ClaimStmt struct {
	IsProve     bool
	ToCheckFact FactStmt
	Proofs      []Stmt
}

type KnowFactStmt struct {
	Facts []FactStmt
}

type KnowPropStmt struct {
	Prop DefPropStmt
}

type FcFnDecl struct {
	Name   string
	Params []string
}

// have 是可能引入 fn 和 prop 的
type HaveStmt struct {
	ObjNames []string
	Fact     SpecFactStmt
}

type SetDefSetBuilderStmt struct {
	SetName   string
	ParentSet Fc
	Facts     []FactStmt
}

type SupposeStmt struct {
	Fact SpecFactStmt
	Body []Stmt
}

type WithPropMatchStmt struct {
	Fact SpecFactStmt
	Body []Stmt
}

type ProveInEachCaseStmt struct {
	OrFact    OrStmt
	ThenFacts []FactStmt
	Proofs    [][]Stmt
}

type KnowExistPropStmt struct {
	ExistProp DefExistPropStmt
}

type KnowSupposeStmt struct {
	SupposeStmt SupposeStmt
}

type OrStmt struct {
	Facts []SpecFactStmt
}
