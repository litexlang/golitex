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
	IffFacts  []*SpecFactStmt
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
}

type GenUniStmt struct {
	TypeParams     []string
	TypeInterfaces []*FcAtom
	UniFact        ConUniFactStmt
}

func (enum SpecFactEnum) IsTrue() bool {
	return enum == TrueAtom || enum == TrueExist || enum == TrueExist_St
}

type SpecFactStmt struct {
	TypeEnum SpecFactEnum
	PropName FcAtom
	Params   []Fc
}

type ClaimProveStmt struct {
	IsProve      bool
	ToCheckFacts []FactStmt
	Proofs       []Stmt
}

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
	Facts []FactStmt
}

type ExistObjDefStmt struct {
	ObjNames []string
	Fact     SpecFactStmt
}

type SetDefStmt struct {
	ObjNames []string
	Fact     SpecFactStmt
}
