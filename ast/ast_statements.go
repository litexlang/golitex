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
	IffFactsOrNil         FactStmtSlice
	ImplicationFactsOrNil FactStmtSlice

	Line uint
}

// 虽然它和 defProp 一样，但不排除之后要让iffFacts只能是可逆的事实
type DefExistPropStmtBody struct {
	DefHeader             *DefHeader
	DomFactsOrNil         FactStmtSlice
	IffFactsOrNil         FactStmtSlice
	ImplicationFactsOrNil FactStmtSlice

	Line uint
}

// how to  use not exist to prove and store not forall in iff section of exist_prop: define a new exist_prop, give a name to that forall, and make this exist_prop equivalent to original exist_prop. Then use prove_by_contradiction to prove the new exist_prop is also false, then the not forall is proved.
type DefExistPropStmt struct {
	DefBody        *DefExistPropStmtBody
	ExistParams    StrSlice
	ExistParamSets ObjSlice

	Line uint
}

type DefFnStmt struct {
	Name       string
	FnTemplate *FnTemplate

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
	FactType SpecFactEnum
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
	Implication *ImplicationStmt
	Proofs      StmtSlice

	Line uint
}

type KnowFactStmt struct {
	Facts CanBeKnownStmtSlice

	Line uint
}

type KnowImplicationStmt struct {
	Prop *DefPropStmt

	Line uint
}

// TODO: 这个的parser还没有像claim_prop那样改成用@
type ClaimExistPropStmt struct {
	ExistPropWithoutDom *DefExistPropStmt
	Proofs              StmtSlice
	HaveObj             ObjSlice

	Line uint
}

type HaveObjStStmt struct {
	ObjNames StrSlice
	Fact     *SpecFactStmt

	Line uint
}

type ProveInEachCaseStmt struct {
	OrFact    *OrStmt
	ThenFacts FactStmtSlice
	Proofs    StmtSliceSlice

	Line uint
}

type ProveCaseByCaseStmt struct {
	CaseFacts SpecFactPtrSlice
	ThenFacts FactStmtSlice
	Proofs    StmtSliceSlice

	Line uint
}

type OrStmt struct {
	Facts SpecFactPtrSlice

	Line uint
}

// """
// import sys # 相当于 import sys as sys

// import "xxx.lit"

// import sys as s

// import "your_dir" as a

// """
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

// s := {1,2,3} 是枚举语法糖，等价于 forall x s: x = 1 or x = 2 or x = 3; 1 $in s; 2 $in s; 3 $in s;
// s := {} 表示 这是个空集
// type EnumStmt struct {
// 	CurSet Obj
// 	Items  ObjSlice

// 	Line uint
// }

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

// type NamedUniFactStmt struct {
// 	DefPropStmt *DefPropStmt

// 	Line uint
// }

type EqualsFactStmt struct {
	Params ObjSlice

	Line uint
}

type KnowExistPropStmt struct {
	ExistProp *DefExistPropStmt

	Line uint
}

// have fn_set seq(s set):
//
//	fn (n N_pos) s # 这是fn_template了
type DefFnSetStmt struct {
	TemplateDefHeader *DefHeader
	TemplateDomFacts  FactStmtSlice
	Fn                *FnTemplate

	Line uint
}

type FnTemplate struct {
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
	Fact  *SpecFactStmt
	Param string
	Start Obj

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

	Line uint
}

// 这是have fn case by case，然后case by case下fn的then都满足的语法糖。理论上可以用 exist_prop + have fn equal case by case + fn_template (可以写复杂的dom, then) + 在定义的外部写如果参数符合dom，那对应的equalTo符合fn_template的then，来彻底实现have fn case by case 的功能。
// Have fn case by case 和 have fn equal 就是单纯的语法糖，不要想有什么额外的功能。不要想着怎么让 HaveFn, HaveFnCaseByCase 用HaveEqual 来替代。
type HaveFnEqualCaseByCaseStmt struct {
	DefHeader         *DefHeader
	RetSet            Obj
	CaseByCaseFacts   SpecFactPtrSlice
	CaseByCaseEqualTo ObjSlice

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
	DefFnStmt        *DefFnStmt
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
	DefFnStmt       *DefFnStmt
	CaseByCaseFacts SpecFactPtrSlice
	Proofs          StmtSliceSlice
	EqualToObjs     ObjSlice

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

type ProveAlgoStmtSlice []ProveAlgoStmt

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

type DefProveAlgoStmt struct {
	ProveAlgoName string
	Params        StrSlice
	Stmts         ProveAlgoStmtSlice

	Line uint
}

type ByStmt struct {
	ProveAlgoName string
	Params        ObjSlice

	Line uint
}

type ProveAlgoIfStmt struct {
	Conditions FactStmtSlice
	ThenStmts  ProveAlgoStmtSlice

	Line uint
}

type ProveAlgoReturnStmt struct {
	Facts FactOrByStmtSlice

	Line uint
}

// type HelpStmt struct {
// 	Keyword string

// 	Line uint
// }

// 这是必要的，因为要证明从n到m有且只有n, n+1, ..., m-1, m这些数，必须要用特殊的关键词

// TODO 应该没什么用
// type HaveObjFromCartSetStmt struct {
// 	ObjName string
// 	CartSet *FnObj
// 	EqualTo Obj

// 	Line uint
// }

// prove_for i range(1, 10):
//     =>:
//         $p(i)
//     prove:
//         know $p(i)

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

type ImplicationStmt struct {
	DefHeader        *DefHeader
	DomFacts         FactStmtSlice
	ImplicationFacts FactStmtSlice

	Line uint
}

type ProveImplyStmt struct {
	SpecFact        *SpecFactStmt
	ImplicationFact FactStmtSlice
	Proofs           StmtSlice

	Line uint
}
