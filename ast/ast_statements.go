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

type DefHeader struct {
	Name      string
	Params    []string
	SetParams []Fc
}

type DefPropStmt struct {
	DefHeader DefHeader
	DomFacts  []FactStmt // 如果输入的参数不满足dom，那就是error
	IffFacts  []FactStmt
	// IsCommutative bool
}

type ExistPropDef struct {
	DefHeader DefHeader
	DomFacts  []FactStmt
	// 必须是 iff，因为 not exist XXX <=> forall not XXX，而 not XXX 要求 XXX 是 reversable_logic_or_spec_stmt
	IffFacts []Reversable_LogicOrSpec_Stmt
}

type DefExistPropStmt struct {
	Def            ExistPropDef
	ExistParams    []string
	ExistParamSets []Fc
}

type DefFnStmt struct {
	DefHeader DefHeader
	RetSet    Fc
	DomFacts  []FactStmt
	ThenFacts []FactStmt
}

type UniFactStmt struct {
	Params    []string
	ParamSets []Fc
	DomFacts  []FactStmt
	ThenFacts []FactStmt
	IffFacts  []FactStmt // TODO: 需要注意到，我存储的所有事实，这一项都是空。未来为了节约空间，可以考虑用新的结构体来存储
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

type KnowStmt struct {
	Facts []FactStmt
}

type KnowPropStmt struct {
	Prop DefPropStmt
}

type FcFnDecl struct {
	Name   string
	Params []string
}

type LogicExprStmt struct {
	IsOr  bool
	Facts []Reversable_LogicOrSpec_Stmt
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
	// finiteItems 是语法糖，可以暂时用 know forall x X: or: x = a1 or x = a2 or ... 来表示
	// FiniteItems []Fc // 在 prove forall, prove not exist 的时候用到。这有 setDefEnum型集合，可能正面证明not exist和forall，其他方式不能证明. 为nil时说明它暂时没有具体的有限表示。可能之后要配合其他的语义来赋予这个field值。本质上这个field的操作和我其他的 forall=>specific 的逻辑是不一样的。某种程度上，prove in each case 的语义和这里的”特殊性“是一样的.
}

type MatcherEnvStmt struct {
	MatcherName FcAtom // pkgName::matcherName
	Params      []Fc
	Body        []Stmt
}

// 之后可以考虑引入 不是 orfact 来证明，而是如果一个集合元素是有限的，那我也可以prove by case
type ProveInEachCaseStmt struct {
	OrFact    LogicExprStmt
	ThenFacts []FactStmt
	Proofs    [][]Stmt
}
