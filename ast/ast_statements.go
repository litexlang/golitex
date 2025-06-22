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

type DefObjStmt struct {
	Objs    []string
	ObjSets []Fc
	Facts   FactStmtSlice
}

type DefHeader struct {
	Name      string
	Params    []string
	SetParams []Fc
}

type DefPropStmt struct {
	DefHeader DefHeader
	DomFacts  FactStmtSlice
	IffFacts  FactStmtSlice
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
	ExistParams    []string
	ExistParamSets []Fc
}

// 这里 fn(p Z, F(p) set) 其实有点问题，因为F可能需要对p有一些要求，这些要求是写在dom里的，需要先运行dom然后才能运行
type DefFnStmt struct {
	DefHeader DefHeader
	DomFacts  FactStmtSlice
	ThenFacts FactStmtSlice
	RetSet    Fc
}

type UniFactStmt struct {
	Params    []string
	ParamSets []Fc
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
	Params   []Fc
}

type ClaimProveStmt struct {
	// IsProve     bool
	ToCheckFact FactStmt
	Proofs      []Stmt
}

type ClaimProveByContradictionStmt struct {
	ClaimProveStmt
}

type KnowFactStmt struct {
	Facts FactStmtSlice
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

type SupposeStmt struct {
	Fact SpecFactStmt
	Body []Stmt
}

type WithStmt struct {
	Fact SpecFactStmt
	Body []Stmt
}

type ProveInEachCaseStmt struct {
	OrFact    OrStmt
	ThenFacts FactStmtSlice
	Proofs    [][]Stmt
}

type KnowExistPropStmt struct {
	ExistProp DefExistPropStmt
}

type OrStmt struct {
	Facts []SpecFactStmt
}

type ImportStmt struct {
	Path      string
	AsPkgName string
}

type PubStmt struct {
	Stmts []Stmt
}

type ProveStmt struct {
	Proof []Stmt
}

type DefFnTemplateStmt struct {
	DefFnStmt DefFnStmt
}
