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

package litex_ast

type FactStmtSlice []FactStmt
type StmtSlice []Stmt
type SpecFactPtrSlice []*SpecFactStmt
type StrSlice []string
type FcSlice []Fc
type ReversibleFacts []Spec_OrFact

type DefObjStmt struct {
	Objs    StrSlice
	ObjSets FcSlice
	Facts   FactStmtSlice

	Line uint
}

type DefHeader struct {
	Name      FcAtom
	Params    StrSlice
	ParamSets FcSlice
}

type DefPropStmt struct {
	DefHeader DefHeader
	DomFacts  FactStmtSlice
	IffFacts  FactStmtSlice
	ThenFacts FactStmtSlice

	Line uint
}

// 虽然它和 defProp 一样，但不排除之后要让iffFacts只能是可逆的事实
type DefExistPropStmtBody struct {
	DefHeader DefHeader
	DomFacts  FactStmtSlice
	IffFacts  FactStmtSlice
	ThenFacts FactStmtSlice

	Line uint
}

// how to  use not exist to prove and store not forall in iff section of exist_prop: define a new exist_prop, give a name to that forall, and make this exist_prop equivalent to original exist_prop. Then use prove_by_contradiction to prove the new exist_prop is also false, then the not forall is proved.
type DefExistPropStmt struct {
	DefBody        DefExistPropStmtBody
	ExistParams    StrSlice
	ExistParamSets FcSlice

	Line uint
}

type DefFnStmt struct {
	Name       string
	FnTemplate FnTStruct

	Line uint
}

type UniFactStmt struct {
	Params    StrSlice
	ParamSets FcSlice
	DomFacts  FactStmtSlice
	ThenFacts FactStmtSlice

	Line uint
}

type UniFactWithIffStmt struct {
	UniFact  UniFactStmt
	IffFacts FactStmtSlice

	Line uint
}

type SpecFactStmt struct {
	TypeEnum SpecFactEnum
	PropName FcAtom
	Params   FcSlice

	Line uint
}

type ClaimProveStmt struct {
	ToCheckFact FactStmt
	Proofs      StmtSlice

	Line uint
}

type ClaimProveByContradictionStmt struct {
	ClaimProveStmt ClaimProveStmt

	Line uint
}

type ClaimPropStmt struct {
	Prop    DefPropStmt
	Proofs  StmtSlice
	IsProve bool

	Line uint
}

type KnowFactStmt struct {
	Facts CanBeKnownStmtSlice

	Line uint
}

type KnowPropStmt struct {
	Prop DefPropStmt

	Line uint
}

// TODO: 这个的parser还没有像claim_prop那样改成用@
type ClaimExistPropStmt struct {
	ExistPropWithoutDom DefExistPropStmt
	Proofs              StmtSlice
	HaveObj             []Fc

	Line uint
}

type HaveObjStStmt struct {
	ObjNames StrSlice
	Fact     SpecFactStmt

	Line uint
}

type ProveInEachCaseStmt struct {
	OrFact    OrStmt
	ThenFacts FactStmtSlice
	Proofs    []StmtSlice

	Line uint
}

type OrStmt struct {
	Facts SpecFactPtrSlice

	Line uint
}

type ImportDirStmt struct {
	Path      string
	AsPkgName string

	Line uint
}

type ProveStmt struct {
	Proof StmtSlice

	Line uint
}

// s := {1,2,3} 是枚举语法糖，等价于 forall x s: x = 1 or x = 2 or x = 3; 1 $in s; 2 $in s; 3 $in s;
// s := {} 表示 这是个空集
type EnumStmt struct {
	CurSet Fc
	Items  FcSlice

	Line uint
}

type ImportFileStmt struct {
	Path string

	Line uint
}

type IntensionalSetStmt struct {
	CurSet    Fc
	Param     string
	ParentSet Fc
	Proofs    SpecFactPtrSlice

	Line uint
}

// 某种程度上这个关键词是不必要的，因为如果我发现涉及到的uniFact里面的所有的 paramSet 都是有 enum 的，那我就默认迭代去证明这个forall。但是我还是引入这个关键词以突出我现在用的是iterative的情况
type ProveOverFiniteSetStmt struct {
	Fact        UniFactStmt
	ProofsSlice []StmtSlice

	Line uint
}

// have xxx st exist_in 的语法糖
type HaveObjInNonEmptySetStmt struct {
	Objs    StrSlice
	ObjSets FcSlice

	Line uint
}

// 由朴素集合论，枚举法定义集合，用specification的方式去定义集合，是可以的。这样定义出来的集合的存在性是直接得到保证的。这个功能必须写入内核，因为have是引入新东西的方式。
type HaveSetStmt struct {
	Fact EnumSet_IntensionalSet_EqualDom

	Line uint
}

// 定义返回值是集合的函数；这个的好处是，fn的定义不能保证函数的存在性；而have可以保证函数的存在性
type HaveSetFnStmt struct {
	DefHeader DefHeader
	Param     string
	ParentSet Fc
	Proofs    SpecFactPtrSlice

	Line uint
}

// TODO: 这里需要变成factStmt, haveSetInterface，而不是只被用在声明的时候
// 还需要对 enum 也有这样的 fn
type HaveSetDefinedByReplacementStmt struct {
	Name     string
	DomSet   Fc
	RangeSet Fc
	PropName FcAtom

	Line uint
}

type NamedUniFactStmt struct {
	DefPropStmt DefPropStmt

	Line uint
}

type EqualsFactStmt struct {
	Params FcSlice

	Line uint
}

type KnowExistPropStmt struct {
	ExistProp DefExistPropStmt

	Line uint
}

type LatexStmt struct {
	Comment string

	Line uint
}

type FnTemplateDefStmt struct {
	TemplateDefHeader DefHeader
	TemplateDomFacts  FactStmtSlice
	Fn                FnTStruct

	Line uint
}

type FnTStruct struct {
	Params    StrSlice
	ParamSets FcSlice
	RetSet    Fc
	DomFacts  FactStmtSlice
	ThenFacts FactStmtSlice

	Line uint
}

type ClearStmt struct {
	Line uint
}

type InlineFactsStmt struct {
	Facts FactStmtSlice

	Line uint
}

type ProveByInductionStmt struct {
	Fact  *SpecFactStmt
	Param string
	Start Fc

	Line uint
}

type HaveObjEqualStmt struct {
	ObjNames    StrSlice
	ObjEqualTos FcSlice
	ObjSets     FcSlice

	Line uint
}

type HaveFnEqualStmt struct {
	DefHeader DefHeader
	RetSet    Fc
	EqualTo   Fc

	Line uint
}

type HaveFnLiftStmt struct {
	FnName                     string
	Opt                        Fc
	DomainOfEachParamOfGivenFn FcSlice

	Line uint
}

type HaveFnStmt struct {
	DefFnStmt        DefFnStmt
	Proofs           StmtSlice
	HaveObjSatisfyFn Fc

	Line uint
}

type MarkdownStmt struct {
	Markdown string

	Line uint
}

type ProveInRange2tmt struct {
	Start     int64
	End       int64
	Param     string
	DomFacts  ReversibleFacts
	ThenFacts FactStmtSlice
	Proofs    StmtSlice

	Line uint
}

type ProveInRangeStmt struct {
	Start          int64
	End            int64
	Param          string
	IntensionalSet Fc
	ThenFacts      FactStmtSlice
	Proofs         StmtSlice

	Line uint
}

type ClaimIffStmt struct {
	UniFactWithIffStmt UniFactWithIffStmt
	ProofThenToIff     StmtSlice
	ProofIffToThen     StmtSlice

	Line uint
}
