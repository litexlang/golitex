// Copyright Jiachen Shen.
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
type StmtSliceSlice []StmtSlice
type SpecFactPtrSlice []*SpecFactStmt
type StrSlice []string // 在定义的时候，用string而不是 atom 是有道理的，因为atom可能引入::，而string不会
type ObjSlice []Obj
type ReversibleFacts []Spec_OrFact
type FactOrByStmtSlice []FactOrByStmt

type DefLetStmt struct {
	Objs    StrSlice
	ObjSets ObjSlice
	Facts   FactStmtSlice

	Line uint
}

type DefHeader struct {
	Name      string
	Params    StrSlice
	ParamSets ObjSlice
}

type DefPropStmt struct {
	DefHeader             *DefHeader
	DomFactsOrNil         FactStmtSlice
	IffFactsOrNil         FactStmtSlice // nil 表示没有iff，无法从定义来验证prop正确性；如果是 []FactStmt{}，表示只要dom和def满足了，那就prop成立。1
	ImplicationFactsOrNil FactStmtSlice

	Line uint
}

type LetFnStmt struct {
	Name       string
	FnTemplate *AnonymousFn

	Line uint
}

type UniFactStmt struct {
	Params    StrSlice
	ParamSets ObjSlice
	DomFacts  FactStmtSlice
	ThenFacts FactStmtSlice

	Line uint
}

type UniFactWithIffStmt struct {
	UniFact  *UniFactStmt
	IffFacts FactStmtSlice

	Line uint
}

type SpecFactStmt struct {
	FactType SpecFactType
	PropName Atom
	Params   ObjSlice

	Line uint
}

type ClaimProveStmt struct {
	ToCheckFact FactStmt
	Proofs      StmtSlice

	Line uint
}

type ClaimProveByContradictionStmt struct {
	ClaimProveStmt *ClaimProveStmt

	Line uint
}

type ClaimImplicationStmt struct {
	Implication *DefPropStmt
	Proofs      StmtSlice

	Line uint
}

type KnowFactStmt struct {
	Facts CanBeKnownStmtSlice

	Line uint
}

type KnowPropInferStmt struct {
	DefProp *DefPropStmt

	Line uint
}

type ProveCaseByCaseStmt struct {
	CaseFacts  SpecFactPtrSlice
	ThenFacts  FactStmtSlice
	Proofs     StmtSliceSlice
	ProveCases StmtSlice

	Line uint
}

type OrStmt struct {
	Facts SpecFactPtrSlice

	Line uint
}

// import sys as s
// import "your_dir" as a
type ImportDirStmt struct {
	RelativePathOrGlobalPkgName string
	AsPkgName                   string
	IsGlobalPkg                 bool

	Line uint
}

type ProveStmt struct {
	Proof StmtSlice

	Line uint
}

// run "xxx.lit"
type RunFileStmt struct {
	Path string

	Line uint
}

// 某种程度上这个关键词是不必要的，因为如果我发现涉及到的uniFact里面的所有的 paramSet 都是有 enum 的，那我就默认迭代去证明这个forall。但是我还是引入这个关键词以突出我现在用的是iterative的情况
// prove_by_enum(x s, y s2, z s3...):
//
//		dom:
//			...
//		=>:
//			...
//	    prove:
//		    ...

// prove_by_enum(x s, y s2, z s3...):
//
//	=>:
//		...
//	prove:
//		...

// prove_by_enum(x s, y s2, z s3...):
//
//	....
type ProveByEnumStmt struct {
	Fact  *UniFactStmt
	Proof StmtSlice

	Line uint
}

type HaveObjInNonEmptySetStmt struct {
	Objs    StrSlice
	ObjSets ObjSlice

	Line uint
}

type EqualsFactStmt struct {
	Params ObjSlice

	Line uint
}
type DefFnSetStmt struct {
	TemplateDefHeader *DefHeader
	TemplateDomFacts  FactStmtSlice
	AnonymousFn       *AnonymousFn

	Line uint
}

type AnonymousFn struct {
	Params    StrSlice
	ParamSets ObjSlice
	RetSet    Obj
	DomFacts  FactStmtSlice
	ThenFacts FactStmtSlice

	Line uint
}

type ClearStmt struct {
	Line uint
}

type DoNothingStmt struct {
	Line uint
}

type InlineFactsStmt struct {
	Facts FactStmtSlice

	Line uint
}

type ProveByInductionStmt struct {
	Fact  FactStmt
	Param string
	Proof StmtSlice

	Line uint
}

type HaveObjEqualStmt struct {
	ObjNames    StrSlice
	ObjEqualTos ObjSlice
	ObjSets     ObjSlice

	Line uint
}

// 这是have fn 语法糖。理论上可以用 exist_prop + have fn equal case by case + 给定义的函数定义它的函数集合，来彻底实现
type HaveFnEqualStmt struct {
	DefHeader *DefHeader
	RetSet    Obj
	EqualTo   Obj
	Proofs    StmtSlice

	Line uint
}

// 这是have fn case by case，然后case by case下fn的then都满足的语法糖。理论上可以用 exist_prop + have fn equal case by case + fn_template (可以写复杂的dom, then) + 在定义的外部写如果参数符合dom，那对应的equalTo符合fn_template的then，来彻底实现have fn case by case 的功能。
// Have fn case by case 和 have fn equal 就是单纯的语法糖，不要想有什么额外的功能。不要想着怎么让 HaveFn, HaveFnCaseByCase 用HaveEqual 来替代。
type HaveFnEqualCaseByCaseStmt struct {
	DefHeader         *DefHeader
	RetSet            Obj
	CaseByCaseFacts   SpecFactPtrSlice
	CaseByCaseEqualTo ObjSlice
	Proofs            StmtSliceSlice
	ProveCases        StmtSlice

	Line uint
}

/*
have fn:

	f(x R) R:
	    ...
	    =>:
	        ...
	prove:
	    ...
	= ...
*/
type HaveFnStmt struct {
	DefFnStmt        *LetFnStmt
	Proofs           StmtSlice
	HaveObjSatisfyFn Obj

	Line uint
}

/*
have fn:

	g(x R) R:
	    ...
	    =>:
	        ...
	case ...:
	    ...
	= ...
	case ...:
	    ...
	= ...
*/
type HaveFnCaseByCaseStmt struct {
	DefFnStmt       *LetFnStmt
	CaseByCaseFacts SpecFactPtrSlice
	Proofs          StmtSliceSlice
	EqualToObjs     ObjSlice
	ProveCases      StmtSlice

	Line uint
}

type ClaimIffStmt struct {
	UniFactWithIffStmt *UniFactWithIffStmt
	ProofThenToIff     StmtSlice
	ProofIffToThen     StmtSlice

	Line uint
}

type ProveIsTransitivePropStmt struct {
	Prop   Atom
	Params StrSlice
	Proofs StmtSlice

	Line uint
}

type ProveIsCommutativePropStmt struct {
	// Prop              FcAtom
	// Params            StrSlice
	SpecFact          *SpecFactStmt
	Proofs            StmtSlice
	ProofsRightToLeft StmtSlice

	Line uint
}

type AlgoStmtSlice []AlgoStmt

// type ProveAlgoStmtSlice []ProveAlgoStmt

type AlgoIfStmt struct {
	Conditions FactStmtSlice
	ThenStmts  AlgoStmtSlice

	Line uint
}

type AlgoReturnStmt struct {
	Value Obj

	Line uint
}

type DefAlgoStmt struct {
	FuncName string
	Params   StrSlice
	Stmts    AlgoStmtSlice

	Line uint
}

type EvalStmt struct {
	ObjToEval Obj

	Line uint
}

// type DefProveAlgoStmt struct {
// 	ProveAlgoName string
// 	Params        StrSlice
// 	Stmts         ProveAlgoStmtSlice
//
// 	Line uint
// }

// type ByStmt struct {
// 	ProveAlgoName string
// 	Params        ObjSlice
//
// 	Line uint
// }

// type ProveAlgoIfStmt struct {
// 	Conditions FactStmtSlice
// 	ThenStmts  ProveAlgoStmtSlice
//
// 	Line uint
// }

// type ProveAlgoReturnStmt struct {
// 	Facts FactOrByStmtSlice
//
// 	Line uint
// }

type ProveForStmt struct {
	Params        StrSlice
	Lefts         ObjSlice
	Rights        ObjSlice
	IsProveIRange []bool // true for range, false for closed_range
	DomFacts      FactStmtSlice
	ThenFacts     FactStmtSlice
	Proofs        StmtSlice

	Line uint
}

// type DefImplicationStmt struct {
// 	DefHeader        *DefHeader
// 	DomFacts         FactStmtSlice
// 	ImplicationFacts FactStmtSlice

// 	Line uint
// }

type ProveInferStmt struct {
	SpecFact        *SpecFactStmt
	ImplicationFact FactStmtSlice
	Proofs          StmtSlice

	Line uint
}

// have objectName setName, objectName2 setName2 st $propName(...)
type HaveObjStStmt struct {
	ObjNames StrSlice
	ObjSets  ObjSlice
	Fact     *SpecFactStmt

	Line uint
}

type WitnessStmt struct {
	ExistParams    StrSlice
	ExistParamSets ObjSlice
	EqualTos       ObjSlice
	Fact           *SpecFactStmt
	Proofs         StmtSlice

	Line uint
}

type WitnessShortStmt struct {
	SpecFact *SpecFactStmt
	Proofs   StmtSlice

	Line uint
}

type InferStmt struct {
	DomFacts  ReversibleFacts
	ThenFacts ReversibleFacts

	Line uint
}

type InferTemplateStmt struct {
	Params    StrSlice
	ParamSets ObjSlice
	DomFacts  ReversibleFacts
	ThenFacts ReversibleFacts
	Proof     StmtSlice

	IfFacts FactStmtSlice

	Line uint
}

type KnowInferStmt struct {
	Params    StrSlice
	ParamSets ObjSlice
	DomFacts  ReversibleFacts
	ThenFacts ReversibleFacts
	IfFacts   FactStmtSlice

	Line uint
}

type EqualSetStmt struct {
	Left   Obj
	Right  Obj
	Proofs StmtSlice

	Line uint
}

type WitnessNonemptyStmt struct {
	Obj    Obj
	ObjSet Obj
	Proofs StmtSlice

	Line uint
}

type ImpossibleStmt struct {
	Fact Spec_OrFact

	Line uint
}
