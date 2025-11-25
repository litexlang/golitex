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

type Stmt interface {
	stmt()
	String() string
	ToLatexString() string
	InlineString() string
	GetLine() uint
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
}

func (s *DefLetStmt) stmt()                                 {}
func (s *DefPropStmt) stmt()                                {}
func (s *DefFnStmt) stmt()                                  {}
func (s *UniFactStmt) stmt()                                {}
func (s *SpecFactStmt) stmt()                               {}
func (s *ClaimProveStmt) stmt()                             {}
func (s *KnowFactStmt) stmt()                               {}
func (s *DefExistPropStmt) stmt()                           {}
func (s *HaveObjStStmt) stmt()                              {}
func (s *ProveInEachCaseStmt) stmt()                        {}
func (s *ProveCaseByCaseStmt) stmt()                        {}
func (s *KnowPropStmt) stmt()                               {}
func (s *OrStmt) stmt()                                     {}
func (s *ImportDirStmt) stmt()                              {}
func (s *ImportFileStmt) stmt()                             {}
func (s *ProveStmt) stmt()                                  {}
func (s *UniFactWithIffStmt) stmt()                         {}
func (s *ClaimProveByContradictionStmt) stmt()              {}
func (s *EnumStmt) stmt()                                   {}
func (s *IntensionalSetStmt) stmt()                         {}
func (s *ClaimPropStmt) stmt()                              {}
func (s *ClaimExistPropStmt) stmt()                         {}
func (s *ProveByEnumStmt) stmt()                            {}
func (s *HaveObjInNonEmptySetStmt) stmt()                   {}
func (s *HaveEnumSetStmt) stmt()                            {}
func (s *HaveIntensionalSetStmt) stmt()                     {}
func (s *HaveCartSetStmt) stmt()                            {}
func (s *HaveSetFnStmt) stmt()                              {}
func (s *HaveSetDefinedByReplacementStmt) stmt()            {}
func (s *NamedUniFactStmt) stmt()                           {}
func (s *EqualsFactStmt) stmt()                             {}
func (s *KnowExistPropStmt) stmt()                          {}
func (s *LatexStmt) stmt()                                  {}
func (s *FnTemplateDefStmt) stmt()                          {}
func (s *ClearStmt) stmt()                                  {}
func (s *InlineFactsStmt) stmt()                            {}
func (s *ProveByInductionStmt) stmt()                       {}
func (s *HaveObjEqualStmt) stmt()                           {}
func (s *HaveFnEqualStmt) stmt()                            {}
func (s *HaveFnLiftStmt) stmt()                             {}
func (s *HaveFnStmt) stmt()                                 {}
func (s *MarkdownStmt) stmt()                               {}
func (s *ProveIsCommutativePropStmt) stmt()                 {}
func (s *ClaimIffStmt) stmt()                               {}
func (s *ProveInRangeSetStmt) stmt()                        {}
func (s *ProveInRangeStmt) stmt()                           {}
func (s *ProveIsTransitivePropStmt) stmt()                  {}
func (s *DefAlgoStmt) stmt()                                {}
func (s *EvalStmt) stmt()                                   {}
func (s *DefProveAlgoStmt) stmt()                           {}
func (s *ByStmt) stmt()                                     {}
func (s *PrintStmt) stmt()                                  {}
func (s *HelpStmt) stmt()                                   {}
func (s *HaveFnEqualCaseByCaseStmt) stmt()                  {}
func (s *HaveFnCaseByCaseStmt) stmt()                       {}
func (s *DefLetStmt) algoStmt()                             {}
func (s *DefPropStmt) algoStmt()                            {}
func (s *DefFnStmt) algoStmt()                              {}
func (s *UniFactStmt) algoStmt()                            {}
func (s *SpecFactStmt) algoStmt()                           {}
func (s *ClaimProveStmt) algoStmt()                         {}
func (s *KnowFactStmt) algoStmt()                           {}
func (s *DefExistPropStmt) algoStmt()                       {}
func (s *HaveObjStStmt) algoStmt()                          {}
func (s *ProveInEachCaseStmt) algoStmt()                    {}
func (s *ProveCaseByCaseStmt) algoStmt()                    {}
func (s *KnowPropStmt) algoStmt()                           {}
func (s *OrStmt) algoStmt()                                 {}
func (s *ImportDirStmt) algoStmt()                          {}
func (s *ImportFileStmt) algoStmt()                         {}
func (s *ProveStmt) algoStmt()                              {}
func (s *UniFactWithIffStmt) algoStmt()                     {}
func (s *ClaimProveByContradictionStmt) algoStmt()          {}
func (s *EnumStmt) algoStmt()                               {}
func (s *IntensionalSetStmt) algoStmt()                     {}
func (s *ClaimPropStmt) algoStmt()                          {}
func (s *ClaimExistPropStmt) algoStmt()                     {}
func (s *ProveByEnumStmt) algoStmt()                        {}
func (s *HaveObjInNonEmptySetStmt) algoStmt()               {}
func (s *HaveEnumSetStmt) algoStmt()                        {}
func (s *HaveIntensionalSetStmt) algoStmt()                 {}
func (s *HaveCartSetStmt) algoStmt()                        {}
func (s *HaveSetFnStmt) algoStmt()                          {}
func (s *HaveSetDefinedByReplacementStmt) algoStmt()        {}
func (s *NamedUniFactStmt) algoStmt()                       {}
func (s *EqualsFactStmt) algoStmt()                         {}
func (s *KnowExistPropStmt) algoStmt()                      {}
func (s *LatexStmt) algoStmt()                              {}
func (s *FnTemplateDefStmt) algoStmt()                      {}
func (s *ClearStmt) algoStmt()                              {}
func (s *InlineFactsStmt) algoStmt()                        {}
func (s *ProveByInductionStmt) algoStmt()                   {}
func (s *HaveObjEqualStmt) algoStmt()                       {}
func (s *HaveFnEqualStmt) algoStmt()                        {}
func (s *HaveFnLiftStmt) algoStmt()                         {}
func (s *HaveFnStmt) algoStmt()                             {}
func (s *MarkdownStmt) algoStmt()                           {}
func (s *ProveIsCommutativePropStmt) algoStmt()             {}
func (s *DefProveAlgoStmt) algoStmt()                       {}
func (s *ByStmt) algoStmt()                                 {}
func (s *ClaimIffStmt) algoStmt()                           {}
func (s *ProveInRangeSetStmt) algoStmt()                    {}
func (s *ProveInRangeStmt) algoStmt()                       {}
func (s *ProveIsTransitivePropStmt) algoStmt()              {}
func (s *DefAlgoStmt) algoStmt()                            {}
func (s *EvalStmt) algoStmt()                               {}
func (s *PrintStmt) algoStmt()                              {}
func (s *HelpStmt) algoStmt()                               {}
func (s *HaveFnEqualCaseByCaseStmt) algoStmt()              {}
func (s *HaveFnCaseByCaseStmt) algoStmt()                   {}
func (s *DefLetStmt) GetLine() uint                         { return s.Line }
func (s *DefPropStmt) GetLine() uint                        { return s.Line }
func (s *DefFnStmt) GetLine() uint                          { return s.Line }
func (s *UniFactStmt) GetLine() uint                        { return s.Line }
func (s *SpecFactStmt) GetLine() uint                       { return s.Line }
func (s *ClaimProveStmt) GetLine() uint                     { return s.Line }
func (s *KnowFactStmt) GetLine() uint                       { return s.Line }
func (s *DefExistPropStmt) GetLine() uint                   { return s.Line }
func (s *HaveObjStStmt) GetLine() uint                      { return s.Line }
func (s *ProveInEachCaseStmt) GetLine() uint                { return s.Line }
func (s *ProveCaseByCaseStmt) GetLine() uint                { return s.Line }
func (s *KnowPropStmt) GetLine() uint                       { return s.Line }
func (s *OrStmt) GetLine() uint                             { return s.Line }
func (s *ImportDirStmt) GetLine() uint                      { return s.Line }
func (s *ImportFileStmt) GetLine() uint                     { return s.Line }
func (s *ProveStmt) GetLine() uint                          { return s.Line }
func (s *UniFactWithIffStmt) GetLine() uint                 { return s.Line }
func (s *ClaimProveByContradictionStmt) GetLine() uint      { return s.Line }
func (s *EnumStmt) GetLine() uint                           { return s.Line }
func (s *IntensionalSetStmt) GetLine() uint                 { return s.Line }
func (s *ClaimPropStmt) GetLine() uint                      { return s.Line }
func (s *ClaimExistPropStmt) GetLine() uint                 { return s.Line }
func (s *ProveByEnumStmt) GetLine() uint                    { return s.Line }
func (s *HaveObjInNonEmptySetStmt) GetLine() uint           { return s.Line }
func (s *HaveEnumSetStmt) GetLine() uint                    { return s.Line }
func (s *HaveIntensionalSetStmt) GetLine() uint             { return s.Line }
func (s *HaveCartSetStmt) GetLine() uint                    { return s.Line }
func (s *HaveSetFnStmt) GetLine() uint                      { return s.Line }
func (s *HaveSetDefinedByReplacementStmt) GetLine() uint    { return s.Line }
func (s *NamedUniFactStmt) GetLine() uint                   { return s.Line }
func (s *EqualsFactStmt) GetLine() uint                     { return s.Line }
func (s *KnowExistPropStmt) GetLine() uint                  { return s.Line }
func (s *LatexStmt) GetLine() uint                          { return s.Line }
func (s *FnTemplateDefStmt) GetLine() uint                  { return s.Line }
func (s *ClearStmt) GetLine() uint                          { return s.Line }
func (s *InlineFactsStmt) GetLine() uint                    { return s.Line }
func (s *ProveByInductionStmt) GetLine() uint               { return s.Line }
func (s *HaveObjEqualStmt) GetLine() uint                   { return s.Line }
func (s *HaveFnEqualStmt) GetLine() uint                    { return s.Line }
func (s *HaveFnLiftStmt) GetLine() uint                     { return s.Line }
func (s *HaveFnStmt) GetLine() uint                         { return s.Line }
func (s *MarkdownStmt) GetLine() uint                       { return s.Line }
func (s *ProveInRangeSetStmt) GetLine() uint                { return s.Line }
func (s *ProveInRangeStmt) GetLine() uint                   { return s.Line }
func (s *ProveInRangeStmt) Param() string                   { return s.param }
func (s *ProveInRangeStmt) Start() Obj                      { return s.start }
func (s *ProveInRangeStmt) End() Obj                        { return s.end }
func (s *ProveInRangeStmt) GetDomFactsOrNil() FactStmtSlice { return s.DomFactsOrNil }
func (s *ProveInRangeStmt) GetThenFacts() FactStmtSlice     { return s.ThenFacts }
func (s *ProveInRangeStmt) GetProofsOrNil() StmtSlice       { return s.ProofsOrNil }
func (s *ClaimIffStmt) GetLine() uint                       { return s.Line }
func (s *ProveIsTransitivePropStmt) GetLine() uint          { return s.Line }
func (s *ProveIsCommutativePropStmt) GetLine() uint         { return s.Line }
func (s *DefAlgoStmt) GetLine() uint                        { return s.Line }
func (s *EvalStmt) GetLine() uint                           { return s.Line }
func (s *DefProveAlgoStmt) GetLine() uint                   { return s.Line }
func (s *ByStmt) GetLine() uint                             { return s.Line }
func (s *PrintStmt) GetLine() uint                          { return s.Line }
func (s *HelpStmt) GetLine() uint                           { return s.Line }
func (s *HaveFnEqualCaseByCaseStmt) GetLine() uint          { return s.Line }
func (s *HaveFnCaseByCaseStmt) GetLine() uint               { return s.Line }

type FactStmt interface {
	factStmt()
	stmt()
	String() string
	InstantiateFact(map[string]Obj) (FactStmt, error)
	GetAtoms() []AtomObj
	ToLatexString() string
	canBeKnown()
	InlineString() string
	// ReplaceObj(oldObj Obj, newObj Obj) FactStmt
	GetLine() uint
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
	proveAlgoReturnStmt()
}

func (p *SpecFactStmt) factStmt()       {}
func (l *UniFactStmt) factStmt()        {}
func (l *UniFactWithIffStmt) factStmt() {}
func (s *OrStmt) factStmt()             {}
func (s *EnumStmt) factStmt()           {}
func (s *IntensionalSetStmt) factStmt() {}
func (s *EqualsFactStmt) factStmt()     {}

type Spec_OrFact interface {
	reversibleFact()
	factStmt()
	stmt()
	String() string
	InstantiateFact(uniConMap map[string]Obj) (FactStmt, error)
	ReverseIsTrue() []*SpecFactStmt
	GetAtoms() []AtomObj
	ToLatexString() string
	canBeKnown()
	InlineString() string
	// ReplaceObj(oldObj Obj, newObj Obj) FactStmt
	GetLine() uint
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
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

type DefStmtInterface interface {
	defStmt()
	stmt()
	String() string
	ToLatexString() string
	InlineString() string
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
}

func (s *DefLetStmt) defStmt()       {}
func (s *DefPropStmt) defStmt()      {}
func (s *DefExistPropStmt) defStmt() {}
func (s *DefFnStmt) defStmt()        {}

type UniFactInterface interface {
	factStmt()
	stmt()
	String() string
	InstantiateFact(map[string]Obj) (FactStmt, error)
	GetAtoms() []AtomObj
	uniFact()
	ToLatexString() string
	canBeKnown()
	InlineString() string
	// ReplaceObj(oldObj Obj, newObj Obj) FactStmt
	GetLine() uint
	algoStmt()
	GetParams() StrSlice
	Instantiate(map[string]Obj) (Stmt, error)
}

func (stmt *UniFactStmt) uniFact()                   {}
func (stmt *UniFactWithIffStmt) uniFact()            {}
func (stmt *UniFactStmt) GetParams() StrSlice        { return stmt.Params }
func (stmt *UniFactWithIffStmt) GetParams() StrSlice { return stmt.UniFact.Params }

type ClaimInterface interface {
	claimStmt()
	String() string
	stmt()
	ToLatexString() string
	InlineString() string
	GetLine() uint
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
}

func (stmt *ClaimProveStmt) claimStmt()                {}
func (stmt *ClaimProveByContradictionStmt) claimStmt() {}
func (stmt *ClaimPropStmt) claimStmt()                 {}
func (stmt *ClaimExistPropStmt) claimStmt()            {}
func (stmt *ClaimIffStmt) claimStmt()                  {}

type ImportStmtInterface interface {
	importStmt()
	stmt()
	String() string
	ToLatexString() string
	InlineString() string
	GetLine() uint
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
}

func (stmt *ImportDirStmt) importStmt()  {}
func (stmt *ImportFileStmt) importStmt() {}

type FnTemplate_Or_DefObjStmtInterface interface {
	fnTemplate_Or_DefObjStmt()
	ToLatexString() string
	InlineString() string
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
}

func (stmt *DefLetStmt) fnTemplate_Or_DefObjStmt() {}

type CanBeKnownStmt interface {
	stmt()
	String() string
	ToLatexString() string
	canBeKnown()
	InlineString() string
	GetLine() uint
	Instantiate(map[string]Obj) (Stmt, error)
}

func (s *SpecFactStmt) canBeKnown()       {}
func (s *UniFactStmt) canBeKnown()        {}
func (s *UniFactWithIffStmt) canBeKnown() {}
func (s *OrStmt) canBeKnown()             {}
func (s *EnumStmt) canBeKnown()           {}
func (s *IntensionalSetStmt) canBeKnown() {}
func (s *EqualsFactStmt) canBeKnown()     {}
func (s *KnowPropStmt) canBeKnown()       {}

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
}

func (s *AlgoIfStmt) algoStmt()         {}
func (s *AlgoReturnStmt) algoStmt()     {}
func (s *AlgoIfStmt) GetLine() uint     { return s.Line }
func (s *AlgoReturnStmt) GetLine() uint { return s.Line }

type ProveAlgoStmt interface {
	proveAlgoStmt()
	String() string
	ToLatexString() string
	InlineString() string
	GetLine() uint
}

func (s *ProveAlgoIfStmt) proveAlgoStmt()     {}
func (s *ProveAlgoReturnStmt) proveAlgoStmt() {}
func (s *ProveAlgoIfStmt) GetLine() uint      { return s.Line }
func (s *ProveAlgoReturnStmt) GetLine() uint  { return s.Line }

type FactOrByStmt interface {
	proveAlgoReturnStmt()
	String() string
	Instantiate(map[string]Obj) (Stmt, error)
}

func (p *SpecFactStmt) proveAlgoReturnStmt()       {}
func (l *UniFactStmt) proveAlgoReturnStmt()        {}
func (l *UniFactWithIffStmt) proveAlgoReturnStmt() {}
func (s *OrStmt) proveAlgoReturnStmt()             {}
func (s *EnumStmt) proveAlgoReturnStmt()           {}
func (s *IntensionalSetStmt) proveAlgoReturnStmt() {}
func (s *EqualsFactStmt) proveAlgoReturnStmt()     {}
func (s *ByStmt) proveAlgoReturnStmt()             {}
