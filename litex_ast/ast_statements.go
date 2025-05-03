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
}

type DefInterfaceStmt struct {
}

type DefTypeStmt struct {
}

type DefConPropStmt struct {
	DefHeader ConDefHeader
	DomFacts  []FactStmt // 如果输入的参数不满足dom，那就是error
	// IffFacts []*SpecFactStmt
	IffFacts []FactStmt
}

type ExistPropDef struct {
	DefHeader ConDefHeader
	DomFacts  []FactStmt
	IffFacts  []*SpecFactStmt // 必须是 iff，因为 not exist XXX <=> forall not XXX，而 not XXX 要求 XXX 是 spec
}

type DefConExistPropStmt struct {
	Def            ExistPropDef
	ExistParams    []string
	ExistParamSets []Fc
}

type DefConFnStmt struct {
	DefHeader ConDefHeader
	RetSet    Fc
	DomFacts  []FactStmt
	// ThenFacts []*SpecFactStmt
	ThenFacts []FactStmt
}

type ConUniFactStmt struct {
	Params    []string // 它可能也是来自另外一个被share的地方。比如defConFn里面的Params，在被存成facts的时候，整个struct被复制到了这里，但本质上它们共享了一片内存
	ParamSets []Fc
	DomFacts  []FactStmt
	// ThenFacts []*SpecFactStmt
	ThenFacts []FactStmt
	IffFacts  []FactStmt // TODO: 需要注意到，我存储的所有事实，这一项都是空。未来为了节约空间，可以考虑用新的结构体来存储

}

var EmptyIffFacts []FactStmt = nil

func (enum SpecFactEnum) IsTrue() bool {
	return enum == TrueAtom || enum == TrueExist || enum == TrueExist_St
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

var ClaimStmtEmptyToCheck FactStmt = nil

type KnowStmt struct {
	Facts []FactStmt
}

// syntax sugar for defining spec prop + claim forall true
type AxiomStmt struct {
	Decl DefPropOrExistPropStmt
}

// syntax sugar for defining spec prop + claim forall true + prove it
type ThmStmt struct {
	Decl  DefPropOrExistPropStmt
	Proof []Stmt
}

type CondFactStmt struct {
	CondFacts []FactStmt
	// ThenFacts []*SpecFactStmt
	ThenFacts []FactStmt
}

type FcFnDecl struct {
	Name   string
	Params []string
}

type ConDefHeader struct {
	Name      string
	Params    []string
	SetParams []Fc
}

type LogicExprStmt struct {
	IsOr  bool
	Facts []LogicExprOrSpecFactStmt
}

type ExistObjDefStmt struct {
	ObjNames []string
	Fact     SpecFactStmt
}

type SetDefSetBuilderStmt struct {
	SetName   string
	ParentSet Fc
	Facts     []FactStmt
}

type SetDefEnumtmt struct {
	SetName string
	Elems   []Fc
}

type MatcherEnvStmt struct {
	MatcherName FcAtom // pkgName::matcherName
	Params      []Fc
	Body        []Stmt
}
