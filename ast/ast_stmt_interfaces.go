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

type Stmt interface {
	stmt()
	String() string
	ToLatexString() string
	InlineString() string
	GetLine() uint
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
	SetLine(line uint)
}

func (s *DefLetStmt) stmt()     {}
func (s *DefPropStmt) stmt()    {}
func (s *LetFnStmt) stmt()      {}
func (s *UniFactStmt) stmt()    {}
func (s *SpecFactStmt) stmt()   {}
func (s *ClaimProveStmt) stmt() {}
func (s *KnowFactStmt) stmt()   {}

// func (s *DefExistPropStmt) stmt()              {}
// func (s *HaveObjStStmt) stmt()                 {}
func (s *HaveObjStStmt) stmt() {}
func (s *ProveCaseByCaseStmt) stmt()        {}
func (s *KnowPropInferStmt) stmt()        {}
func (s *OrStmt) stmt()                     {}
func (s *InferStmt) stmt()                  {}
func (s *InferTemplateStmt) stmt()          {}
func (s *ImportDirStmt) stmt()              {}
func (s *RunFileStmt) stmt()                {}
func (s *ProveStmt) stmt()                  {}
func (s *ProveForStmt) stmt()               {}
func (s *ProveInferStmt) stmt()             {}

// func (s *DefImplicationStmt) stmt()            {}
func (s *UniFactWithIffStmt) stmt()            {}
func (s *ClaimProveByContradictionStmt) stmt() {}
func (s *ClaimImplicationStmt) stmt()          {}

// func (s *ClaimExistPropStmt) stmt()            {}
func (s *ProveByEnumStmt) stmt()          {}
func (s *HaveObjInNonEmptySetStmt) stmt() {}
func (s *EqualsFactStmt) stmt()           {}

// func (s *KnowExistPropStmt) stmt()             {}
func (s *DefFnSetStmt) stmt()               {}
func (s *ClearStmt) stmt()                  {}
func (s *DoNothingStmt) stmt()              {}
func (s *InlineFactsStmt) stmt()            {}
func (s *ProveByInductionStmt) stmt()       {}
func (s *HaveObjEqualStmt) stmt()           {}
func (s *HaveFnEqualStmt) stmt()            {}
func (s *HaveFnStmt) stmt()                 {}
func (s *ProveIsCommutativePropStmt) stmt() {}
func (s *ClaimIffStmt) stmt()               {}
func (s *ProveIsTransitivePropStmt) stmt()  {}
func (s *DefAlgoStmt) stmt()                {}
func (s *EvalStmt) stmt()                   {}
// func (s *DefProveAlgoStmt) stmt()           {}
// func (s *ByStmt) stmt()                     {}
func (s *HaveFnEqualCaseByCaseStmt) stmt()  {}
func (s *HaveFnCaseByCaseStmt) stmt()       {}
func (s *ProveExistStmt) stmt()             {}

func (s *DefLetStmt) algoStmt()     {}
func (s *DefPropStmt) algoStmt()    {}
func (s *LetFnStmt) algoStmt()      {}
func (s *UniFactStmt) algoStmt()    {}
func (s *SpecFactStmt) algoStmt()   {}
func (s *ClaimProveStmt) algoStmt() {}
func (s *KnowFactStmt) algoStmt()   {}

// func (s *DefExistPropStmt) algoStmt()                  {}
// func (s *HaveObjStStmt) algoStmt()                 {}
func (s *HaveObjStStmt) algoStmt()    {}
func (s *ProveCaseByCaseStmt) algoStmt()           {}
func (s *KnowPropInferStmt) algoStmt()           {}
func (s *OrStmt) algoStmt()                        {}
func (s *InferStmt) algoStmt()                      {}
func (s *InferTemplateStmt) algoStmt()              {}
func (s *ImportDirStmt) algoStmt()                 {}
func (s *RunFileStmt) algoStmt()                   {}
func (s *ProveStmt) algoStmt()                     {}
func (s *UniFactWithIffStmt) algoStmt()            {}
func (s *ClaimProveByContradictionStmt) algoStmt() {}
func (s *ClaimImplicationStmt) algoStmt()          {}

// func (s *ClaimExistPropStmt) algoStmt()                {}
func (s *ProveByEnumStmt) algoStmt()          {}
func (s *HaveObjInNonEmptySetStmt) algoStmt() {}
func (s *EqualsFactStmt) algoStmt()           {}

// func (s *KnowExistPropStmt) algoStmt()                 {}
func (s *DefFnSetStmt) algoStmt()               {}
func (s *ClearStmt) algoStmt()                  {}
func (s *DoNothingStmt) algoStmt()              {}
func (s *InlineFactsStmt) algoStmt()            {}
func (s *ProveByInductionStmt) algoStmt()       {}
func (s *HaveObjEqualStmt) algoStmt()           {}
func (s *HaveFnEqualStmt) algoStmt()            {}
func (s *HaveFnStmt) algoStmt()                 {}
func (s *ProveIsCommutativePropStmt) algoStmt() {}
// func (s *DefProveAlgoStmt) algoStmt()           {}
// func (s *ByStmt) algoStmt()                     {}
func (s *ClaimIffStmt) algoStmt()               {}
func (s *ProveForStmt) algoStmt()               {}
func (s *ProveInferStmt) algoStmt()             {}

// func (s *DefImplicationStmt) algoStmt()         {}
func (s *ProveIsTransitivePropStmt) algoStmt() {}
func (s *DefAlgoStmt) algoStmt()               {}
func (s *EvalStmt) algoStmt()                  {}
func (s *HaveFnEqualCaseByCaseStmt) algoStmt() {}
func (s *HaveFnCaseByCaseStmt) algoStmt()      {}
func (s *ProveExistStmt) algoStmt()            {}
func (s *DefLetStmt) GetLine() uint            { return s.Line }
func (s *DefPropStmt) GetLine() uint           { return s.Line }
func (s *LetFnStmt) GetLine() uint             { return s.Line }
func (s *UniFactStmt) GetLine() uint           { return s.Line }
func (s *SpecFactStmt) GetLine() uint          { return s.Line }
func (s *ClaimProveStmt) GetLine() uint        { return s.Line }
func (s *KnowFactStmt) GetLine() uint          { return s.Line }

// func (s *DefExistPropStmt) GetLine() uint              { return s.Line }
// func (s *HaveObjStStmt) GetLine() uint                 { return s.Line }
func (s *HaveObjStStmt) GetLine() uint    { return s.Line }
func (s *ProveCaseByCaseStmt) GetLine() uint           { return s.Line }
func (s *KnowPropInferStmt) GetLine() uint           { return s.Line }
func (s *OrStmt) GetLine() uint                        { return s.Line }
func (s *InferStmt) GetLine() uint                     { return s.Line }
func (s *InferTemplateStmt) GetLine() uint             { return s.Line }
func (s *ImportDirStmt) GetLine() uint                 { return s.Line }
func (s *RunFileStmt) GetLine() uint                   { return s.Line }
func (s *ProveStmt) GetLine() uint                     { return s.Line }
func (s *UniFactWithIffStmt) GetLine() uint            { return s.Line }
func (s *ClaimProveByContradictionStmt) GetLine() uint { return s.Line }

func (s *ClaimImplicationStmt) GetLine() uint { return s.Line }

// func (s *ClaimExistPropStmt) GetLine() uint       { return s.Line }
func (s *ProveByEnumStmt) GetLine() uint          { return s.Line }
func (s *HaveObjInNonEmptySetStmt) GetLine() uint { return s.Line }
func (s *EqualsFactStmt) GetLine() uint           { return s.Line }

// func (s *KnowExistPropStmt) GetLine() uint        { return s.Line }

func (s *DefFnSetStmt) GetLine() uint         { return s.Line }
func (s *ClearStmt) GetLine() uint            { return s.Line }
func (s *DoNothingStmt) GetLine() uint        { return s.Line }
func (s *InlineFactsStmt) GetLine() uint      { return s.Line }
func (s *ProveByInductionStmt) GetLine() uint { return s.Line }
func (s *HaveObjEqualStmt) GetLine() uint     { return s.Line }
func (s *HaveFnEqualStmt) GetLine() uint      { return s.Line }

func (s *HaveFnStmt) GetLine() uint { return s.Line }

func (s *ClaimIffStmt) GetLine() uint               { return s.Line }
func (s *ProveIsTransitivePropStmt) GetLine() uint  { return s.Line }
func (s *ProveIsCommutativePropStmt) GetLine() uint { return s.Line }
func (s *DefAlgoStmt) GetLine() uint                { return s.Line }
func (s *EvalStmt) GetLine() uint                   { return s.Line }
// func (s *DefProveAlgoStmt) GetLine() uint           { return s.Line }
// func (s *ByStmt) GetLine() uint                     { return s.Line }
func (s *ProveForStmt) GetLine() uint               { return s.Line }
func (s *ProveInferStmt) GetLine() uint             { return s.Line }

// func (s *DefImplicationStmt) GetLine() uint         { return s.Line }
func (s *HaveFnEqualCaseByCaseStmt) GetLine() uint { return s.Line }
func (s *HaveFnCaseByCaseStmt) GetLine() uint      { return s.Line }
func (s *ProveExistStmt) GetLine() uint            { return s.Line }

func (s *DefLetStmt) SetLine(l uint)     { s.Line = l }
func (s *DefPropStmt) SetLine(l uint)    { s.Line = l }
func (s *LetFnStmt) SetLine(l uint)      { s.Line = l }
func (s *UniFactStmt) SetLine(l uint)    { s.Line = l }
func (s *SpecFactStmt) SetLine(l uint)   { s.Line = l }
func (s *ClaimProveStmt) SetLine(l uint) { s.Line = l }
func (s *KnowFactStmt) SetLine(l uint)   { s.Line = l }

// func (s *DefExistPropStmt) SetLine(l uint)              { s.Line = l }
// func (s *HaveObjStStmt) SetLine(l uint)                 { s.Line = l }
func (s *HaveObjStStmt) SetLine(l uint)    { s.Line = l }
func (s *ProveCaseByCaseStmt) SetLine(l uint)           { s.Line = l }
func (s *KnowPropInferStmt) SetLine(l uint)           { s.Line = l }
func (s *OrStmt) SetLine(l uint)                        { s.Line = l }
func (s *InferStmt) SetLine(l uint)                     { s.Line = l }
func (s *InferTemplateStmt) SetLine(l uint)             { s.Line = l }
func (s *ImportDirStmt) SetLine(l uint)                 { s.Line = l }
func (s *RunFileStmt) SetLine(l uint)                   { s.Line = l }
func (s *ProveStmt) SetLine(l uint)                     { s.Line = l }
func (s *UniFactWithIffStmt) SetLine(l uint)            { s.Line = l }
func (s *ClaimProveByContradictionStmt) SetLine(l uint) { s.Line = l }

func (s *ClaimImplicationStmt) SetLine(l uint) { s.Line = l }

// func (s *ClaimExistPropStmt) SetLine(l uint)       { s.Line = l }
func (s *ProveByEnumStmt) SetLine(l uint)          { s.Line = l }
func (s *HaveObjInNonEmptySetStmt) SetLine(l uint) { s.Line = l }

// func (s *HaveObjFromCartSetStmt) SetLine(l uint)   { s.Line = l}

// func (s *NamedUniFactStmt) SetLine(l uint)  { s.Line = l}
func (s *EqualsFactStmt) SetLine(l uint) { s.Line = l }

// func (s *KnowExistPropStmt) SetLine(l uint) { s.Line = l }

func (s *DefFnSetStmt) SetLine(l uint)         { s.Line = l }
func (s *ClearStmt) SetLine(l uint)            { s.Line = l }
func (s *DoNothingStmt) SetLine(l uint)        { s.Line = l }
func (s *InlineFactsStmt) SetLine(l uint)      { s.Line = l }
func (s *ProveByInductionStmt) SetLine(l uint) { s.Line = l }
func (s *HaveObjEqualStmt) SetLine(l uint)     { s.Line = l }
func (s *HaveFnEqualStmt) SetLine(l uint)      { s.Line = l }

func (s *HaveFnStmt) SetLine(l uint) { s.Line = l }

func (s *ClaimIffStmt) SetLine(l uint)               { s.Line = l }
func (s *ProveIsTransitivePropStmt) SetLine(l uint)  { s.Line = l }
func (s *ProveIsCommutativePropStmt) SetLine(l uint) { s.Line = l }
func (s *DefAlgoStmt) SetLine(l uint)                { s.Line = l }
func (s *EvalStmt) SetLine(l uint)                   { s.Line = l }
// func (s *DefProveAlgoStmt) SetLine(l uint)           { s.Line = l }
// func (s *ByStmt) SetLine(l uint)                     { s.Line = l }
func (s *ProveForStmt) SetLine(l uint)               { s.Line = l }
func (s *ProveInferStmt) SetLine(l uint)             { s.Line = l }

// func (s *DefImplicationStmt) SetLine(l uint)         { s.Line = l }
func (s *HaveFnEqualCaseByCaseStmt) SetLine(l uint) { s.Line = l }
func (s *HaveFnCaseByCaseStmt) SetLine(l uint)      { s.Line = l }
func (s *ProveExistStmt) SetLine(l uint)            { s.Line = l }

type FactStmt interface {
	factStmt()
	stmt()
	String() string
	InstantiateFact(map[string]Obj) (FactStmt, error)
	ToLatexString() string
	canBeKnown()
	InlineString() string
	GetLine() uint
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
	proveAlgoReturnStmt()
	SetLine(l uint)
}

func (p *SpecFactStmt) factStmt()       {}
func (l *UniFactStmt) factStmt()        {}
func (l *UniFactWithIffStmt) factStmt() {}
func (s *OrStmt) factStmt()             {}
func (s *EqualsFactStmt) factStmt()     {}

type Spec_OrFact interface {
	reversibleFact()
	factStmt()
	stmt()
	String() string
	InstantiateFact(uniConMap map[string]Obj) (FactStmt, error)
	ReverseIsTrue() []*SpecFactStmt
	ToLatexString() string
	canBeKnown()
	InlineString() string
	GetLine() uint
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
	SetLine(l uint)
}

func (s *SpecFactStmt) reversibleFact() {}
func (s *OrStmt) reversibleFact()       {}

// Spec_OrFact also implements proveAlgoReturnStmt through FactStmt

func (stmt *SpecFactStmt) ReverseIsTrue() []*SpecFactStmt {
	return []*SpecFactStmt{stmt.ReverseTrue()}
}

func (stmt *OrStmt) ReverseIsTrue() []*SpecFactStmt {
	reversedFacts := make([]*SpecFactStmt, len(stmt.Facts))
	for i, fact := range stmt.Facts {
		reversedFacts[i] = fact.ReverseTrue()
	}
	return reversedFacts
}

type CanBeKnownStmt interface {
	stmt()
	String() string
	ToLatexString() string
	canBeKnown()
	InlineString() string
	GetLine() uint
	Instantiate(map[string]Obj) (Stmt, error)
	SetLine(l uint)
}

func (s *SpecFactStmt) canBeKnown()       {}
func (s *UniFactStmt) canBeKnown()        {}
func (s *UniFactWithIffStmt) canBeKnown() {}
func (s *OrStmt) canBeKnown()             {}

func (s *EqualsFactStmt) canBeKnown()      {}
func (s *KnowPropInferStmt) canBeKnown() {}

type CanBeKnownStmtSlice []CanBeKnownStmt

func (s FactStmtSlice) ToCanBeKnownStmtSlice() CanBeKnownStmtSlice {
	ret := make(CanBeKnownStmtSlice, len(s))
	for i, fact := range s {
		ret[i] = fact.(CanBeKnownStmt)
	}
	return ret
}

// AlgoStmt 不一定是 Stmt
type AlgoStmt interface {
	algoStmt()
	String() string
	ToLatexString() string
	InlineString() string
	GetLine() uint
	SetLine(l uint)
}

func (s *AlgoIfStmt) algoStmt()          {}
func (s *AlgoReturnStmt) algoStmt()      {}
func (s *AlgoIfStmt) GetLine() uint      { return s.Line }
func (s *AlgoReturnStmt) GetLine() uint  { return s.Line }
func (s *AlgoIfStmt) SetLine(l uint)     { s.Line = l }
func (s *AlgoReturnStmt) SetLine(l uint) { s.Line = l }

// type ProveAlgoStmt interface {
// 	proveAlgoStmt()
// 	String() string
// 	ToLatexString() string
// 	InlineString() string
// 	GetLine() uint
// 	SetLine(l uint)
// }

// func (s *ProveAlgoIfStmt) proveAlgoStmt()     {}
// func (s *ProveAlgoReturnStmt) proveAlgoStmt() {}
// func (s *ProveAlgoIfStmt) GetLine() uint      { return s.Line }
// func (s *ProveAlgoReturnStmt) GetLine() uint  { return s.Line }
// func (s *ProveAlgoIfStmt) SetLine(l uint)     { s.Line = l }
// func (s *ProveAlgoReturnStmt) SetLine(l uint) { s.Line = l }

type FactOrByStmt interface {
	proveAlgoReturnStmt()
	String() string
	Instantiate(map[string]Obj) (Stmt, error)
	SetLine(l uint)
}

func (p *SpecFactStmt) proveAlgoReturnStmt()       {}
func (l *UniFactStmt) proveAlgoReturnStmt()        {}
func (l *UniFactWithIffStmt) proveAlgoReturnStmt() {}
func (s *OrStmt) proveAlgoReturnStmt()             {}
func (s *EqualsFactStmt) proveAlgoReturnStmt()     {}
// func (s *ByStmt) proveAlgoReturnStmt()             {}
