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

package litex_ast

type FactStmtSlice []FactStmt
type StmtSlice []Stmt
type SpecFactPtrSlice []*SpecFactStmt
type StrSlice []string
type FcSlice []Fc

type DefObjStmt struct {
	Objs    StrSlice
	ObjSets FcSlice
	Facts   FactStmtSlice
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
}

// 虽然它和 defProp 一样，但不排除之后要让iffFacts只能是可逆的事实
type DefExistPropStmtBody struct {
	DefHeader DefHeader
	DomFacts  FactStmtSlice
	IffFacts  FactStmtSlice
}

// how to  use not exist to prove and store not forall in iff section of exist_prop: define a new exist_prop, give a name to that forall, and make this exist_prop equivalent to original exist_prop. Then use prove_by_contradiction to prove the new exist_prop is also false, then the not forall is proved.
type DefExistPropStmt struct {
	DefBody        DefExistPropStmtBody
	ExistParams    StrSlice
	ExistParamSets FcSlice
}

type DefFnStmt struct {
	Name       string
	FnTemplate FnTStruct
}

type UniFactStmt struct {
	Params    StrSlice
	ParamSets FcSlice
	DomFacts  FactStmtSlice
	ThenFacts FactStmtSlice
}

type UniFactWithIffStmt struct {
	UniFact  UniFactStmt
	IffFacts FactStmtSlice
}

type SpecFactStmt struct {
	TypeEnum SpecFactEnum
	PropName FcAtom
	Params   FcSlice
}

type ClaimProveStmt struct {
	ToCheckFact FactStmt
	Proofs      StmtSlice
}

type ClaimProveByContradictionStmt struct {
	ClaimProveStmt ClaimProveStmt
}

type ClaimPropStmt struct {
	Prop    DefPropStmt
	Proofs  StmtSlice
	IsProve bool
}

type KnowFactStmt struct {
	Facts CanBeKnownStmtSlice
}

type KnowPropStmt struct {
	Prop DefPropStmt
}

// TODO: 这个的parser还没有像claim_prop那样改成用@
type ClaimExistPropStmt struct {
	ExistProp DefExistPropStmt
	Proofs    StmtSlice
}

type HaveObjStStmt struct {
	ObjNames StrSlice
	Fact     SpecFactStmt
}

type ProveInEachCaseStmt struct {
	OrFact    OrStmt
	ThenFacts FactStmtSlice
	Proofs    []StmtSlice
}

type OrStmt struct {
	Facts SpecFactPtrSlice
}

type ImportDirStmt struct {
	Path      string
	AsPkgName string
}

type ProveStmt struct {
	Proof StmtSlice
}

// type DefFnTemplateStmt struct {
// 	FnTemplateStmt FnTemplateStmt
// }

// s := {1,2,3} 是枚举语法糖，等价于 forall x s: x = 1 or x = 2 or x = 3; 1 $in s; 2 $in s; 3 $in s;
// s := {} 表示 这是个空集
type EnumStmt struct {
	CurSet Fc
	Items  FcSlice
}

type ImportFileStmt struct {
	Path string
}

// Fact表示一个事实，paramIndex表示第n位是变化的n $in N(默认第0位是开始)，其他参数固定，start是递归从start开始(默认从0开始)
// type ProveByMathInductionStmt struct {
// 	Fact       *SpecFactStmt
// 	ParamIndex int
// 	Start      int
// }

type IntensionalSetStmt struct {
	CurSet    Fc
	Param     string
	ParentSet Fc
	Proofs    SpecFactPtrSlice
}

// 某种程度上这个关键词是不必要的，因为如果我发现涉及到的uniFact里面的所有的 paramSet 都是有 enum 的，那我就默认迭代去证明这个forall。但是我还是引入这个关键词以突出我现在用的是iterative的情况
type ProveOverFiniteSetStmt struct {
	Fact        UniFactStmt
	ProofsSlice []StmtSlice
}

// have xxx st exist_in 的语法糖
type HaveObjInNonEmptySetStmt struct {
	Objs    StrSlice
	ObjSets FcSlice
}

// 由朴素集合论，枚举法定义集合，用specification的方式去定义集合，是可以的。这样定义出来的集合的存在性是直接得到保证的。这个功能必须写入内核，因为have是引入新东西的方式。
type HaveSetStmt struct {
	Fact EnumSet_IntensionalSet_EqualDom
}

// 定义返回值是集合的函数；这个的好处是，fn的定义不能保证函数的存在性；而have可以保证函数的存在性
type HaveSetFnStmt struct {
	DefHeader DefHeader
	Param     string
	ParentSet Fc
	Proofs    SpecFactPtrSlice
}

// TODO: 这里需要变成factStmt, haveSetInterface，而不是只被用在声明的时候
// 还需要对 enum 也有这样的 fn
type HaveSetDefinedByReplacementStmt struct {
	Name     string
	DomSet   Fc
	RangeSet Fc
	PropName FcAtom
}

type NamedUniFactStmt struct {
	DefPropStmt DefPropStmt
}

type EqualsFactStmt struct {
	Params FcSlice
}

type KnowExistPropStmt struct {
	ExistProp DefExistPropStmt
}

type CommentStmt struct {
	Comment string
}

type FnTemplateDefStmt struct {
	TemplateDefHeader DefHeader
	TemplateDomFacts  FactStmtSlice
	Fn                FnTStruct
}

type FnTStruct struct {
	Params    StrSlice
	ParamSets FcSlice
	RetSet    Fc
	DomFacts  FactStmtSlice
	ThenFacts FactStmtSlice
}

type ClearStmt struct{}

type InlineFactsStmt struct {
	Facts FactStmtSlice
}

type ProveByInductionStmt struct {
	Fact  *SpecFactStmt
	Param string
	Start Fc
}

type HaveObjEqualStmt struct {
	ObjNames    StrSlice
	ObjEqualTos FcSlice
	ObjSets     FcSlice
}

type HaveFnEqualStmt struct {
	DefHeader DefHeader
	RetSet    Fc
	EqualTo   Fc
}

type HaveFnLiftStmt struct {
	FnName                     string
	Opt                        Fc
	DomainOfEachParamOfGivenFn FcSlice
}

type HaveFnStmt struct {
	DefFnStmt        DefFnStmt
	Proofs           StmtSlice
	HaveObjSatisfyFn Fc
}
