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
	DomFacts  []FactStmt      // 如果输入的参数不满足dom，那就是error
	IffFacts  []*SpecFactStmt // 如果输入参数满足dom，满足iff，那就true. 这里必须是spec，因为我需要 know forall x: prop+dom => iffFacts，而iffFacts出现在了then的位置
}

type DefConExistPropStmt struct {
	Def DefConPropStmt
}

type DefConFnStmt struct {
	DefHeader ConDefHeader
	RetSet    Fc
	DomFacts  []FactStmt
	ThenFacts []*SpecFactStmt
}

type ConUniFactStmt struct {
	Params    []string // 它可能也是来自另外一个被share的地方。比如defConFn里面的Params，在被存成facts的时候，整个struct被复制到了这里，但本质上它们共享了一片内存
	ParamSets []Fc
	DomFacts  []FactStmt
	ThenFacts []*SpecFactStmt
}

type GenUniStmt struct {
	TypeParams     []string
	TypeInterfaces []*FcAtom
	UniFact        ConUniFactStmt
}

type SpecFactEnum uint8

const (
	TrueAtom SpecFactEnum = iota
	FalseAtom
	TrueExist
	FalseExist
)

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

type HaveStmt struct {
	PropStmt SpecFactStmt
	Member   []string
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
	ThenFacts []*SpecFactStmt
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

type OrAndFactStmt struct {
	IsOr  bool
	Facts []FactStmt
}
