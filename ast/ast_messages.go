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

import (
	"fmt"
	glob "golitex/glob"
	"strings"
)

func (stmt *PubStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordPub)
	builder.WriteByte(':')
	builder.WriteByte('\n')
	for _, stmt := range stmt.Stmts {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.String(), 1))
		builder.WriteByte('\n')
	}
	return strings.TrimSuffix(builder.String(), "\n")
}

func (stmt *KnowFactStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordKnow)
	builder.WriteByte(':')
	builder.WriteByte('\n')
	if len(stmt.Facts) > 0 {
		for i := 0; i < len(stmt.Facts)-1; i++ {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Facts[i].String(), 1))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Facts[len(stmt.Facts)-1].String(), 1))
	}
	return builder.String()
}

func (stmt *SpecFactStmt) String() string {
	if stmt.IsExist_St_Fact() {
		return exist_st_FactString(stmt)
	} else {
		return pureFactString(stmt)
	}
}

func pureFactString(stmt *SpecFactStmt) string {
	var builder strings.Builder

	if stmt.TypeEnum == FalsePure {
		builder.WriteString(glob.KeywordNot)
		builder.WriteByte(' ')
	}
	if stmt.PropName.PkgName == glob.EmptyPkg && glob.IsKeySymbol(stmt.PropName.Name) {
		builder.WriteString(relaFactWithoutNotString(stmt))
	} else {
		builder.WriteString(glob.FuncFactPrefix)
		builder.WriteString(stmt.PropName.String())
		builder.WriteByte('(')
		builder.WriteString(FcSliceString(stmt.Params))
		builder.WriteByte(')')
	}
	return builder.String()
}

func relaFactWithoutNotString(stmt *SpecFactStmt) string {
	var builder strings.Builder

	builder.WriteString(stmt.Params[0].String())
	builder.WriteByte(' ')
	builder.WriteString(stmt.PropName.String())
	builder.WriteByte(' ')
	builder.WriteString(stmt.Params[1].String())

	return builder.String()
}

func exist_st_FactString(stmt *SpecFactStmt) string {
	var builder strings.Builder
	if stmt.TypeEnum == FalseExist_St {
		builder.WriteString(glob.KeywordNot)
		builder.WriteByte(' ')
	}

	builder.WriteString(glob.KeywordExist)
	builder.WriteByte(' ')

	sepIndex := stmt.Exist_St_SeparatorIndex()
	if sepIndex == -1 {
		return ""
	} else {
		for i := range sepIndex {
			builder.WriteString(stmt.Params[i].String())
			builder.WriteString(" ")
		}

		builder.WriteString(glob.KeywordSt)
		builder.WriteString(" ")

		builder.WriteString(glob.FuncFactPrefix)
		builder.WriteString(stmt.PropName.String())
		builder.WriteByte('(')
		builder.WriteString(FcSliceString(stmt.Params[sepIndex+1:]))
		builder.WriteByte(')')
		return builder.String()
	}
}

func (stmt *DefObjStmt) String() string {
	var builder strings.Builder

	builder.WriteString("obj ")
	if len(stmt.Objs) > 0 {
		for i := range len(stmt.Objs) - 1 {
			builder.WriteString(stmt.Objs[i])
			builder.WriteString(" ")
			builder.WriteString(stmt.ObjSets[i].String())
			builder.WriteString(", ")
		}
		builder.WriteString(stmt.Objs[len(stmt.Objs)-1])
		builder.WriteString(" ")
		builder.WriteString(stmt.ObjSets[len(stmt.Objs)-1].String())
	}

	if len(stmt.Facts) > 0 {
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteByte('\n')
		builder.WriteString(strOfNonEmptyFactStmtSlice(stmt.Facts, 1))
	}

	return builder.String()
}

func (fact *DefPropStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordProp)
	builder.WriteByte(' ')
	builder.WriteString(fact.DefHeader.String())

	if len(fact.DomFacts) == 0 && len(fact.IffFacts) == 0 {
		return strings.TrimSuffix(builder.String(), glob.KeySymbolColon)
	}

	builder.WriteByte('\n')
	if len(fact.DomFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordDom, 1))
		builder.WriteByte(':')
		builder.WriteByte('\n')
		for i := 0; i < len(fact.DomFacts)-1; i++ {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.DomFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.DomFacts[len(fact.DomFacts)-1].String(), 2))
		builder.WriteByte('\n')
	}

	if len(fact.IffFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordIff, 1))
		builder.WriteByte(':')
		builder.WriteByte('\n')
		for i := 0; i < len(fact.IffFacts)-1; i++ {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.IffFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.IffFacts[len(fact.IffFacts)-1].String(), 2))
	}

	return builder.String()

}

func (f *DefFnStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordFn)
	builder.WriteString(" ")

	builder.WriteString(f.DefHeader.StringWithoutColonAtEnd())
	builder.WriteString(" ")
	builder.WriteString(f.RetSet.String())

	if len(f.DomFacts) == 0 && len(f.ThenFacts) == 0 {
		return builder.String()
	}
	builder.WriteByte('\n')

	if len(f.DomFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordDom, 1))
		builder.WriteByte(':')
		builder.WriteByte('\n')
		for i := 0; i < len(f.DomFacts)-1; i++ {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(f.DomFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(f.DomFacts[len(f.DomFacts)-1].String(), 2))
		builder.WriteByte('\n')
	}
	if len(f.ThenFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordThen, 1))
		builder.WriteByte(':')
		builder.WriteByte('\n')

		for i := 0; i < len(f.ThenFacts)-1; i++ {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(f.ThenFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(f.ThenFacts[len(f.ThenFacts)-1].String(), 2))
	}

	return builder.String()
}

func (f *ClaimProveByContradictionStmt) String() string {
	return ClaimProve_ClaimProveByContradiction(glob.KeywordProveByContradiction, f.Claim.ToCheckFact, f.Claim.Proofs)
}

func (f *ClaimProveStmt) String() string {
	return ClaimProve_ClaimProveByContradiction(glob.KeywordProve, f.ToCheckFact, f.Proofs)
}

func ClaimProve_ClaimProveByContradiction(kw string, toCheckFact FactStmt, proofs []Stmt) string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordClaim)
	builder.WriteByte(':')
	builder.WriteByte('\n')

	builder.WriteString(glob.SplitLinesAndAdd4NIndents(toCheckFact.String(), 1))
	builder.WriteByte('\n')

	builder.WriteString(glob.SplitLinesAndAdd4NIndents(kw, 1))
	builder.WriteByte(':')
	builder.WriteByte('\n')
	for _, fact := range proofs {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.String(), 2))
		builder.WriteByte('\n')
	}
	return strings.TrimSpace(builder.String())
}

func (s *DefExistPropStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordExistProp)
	builder.WriteByte(' ')
	if len(s.ExistParams) > 0 {
		for i := 0; i < len(s.ExistParams)-1; i++ {
			builder.WriteString(s.ExistParams[i])
			builder.WriteString(" ")
			builder.WriteString(s.ExistParamSets[i].String())
			builder.WriteString(", ")
		}
		builder.WriteString(s.ExistParams[len(s.ExistParams)-1])
	}
	builder.WriteString(" ")
	builder.WriteString(glob.KeywordSt)
	builder.WriteString(" ")
	builder.WriteString(s.DefBody.DefHeader.String())

	if len(s.DefBody.DomFacts) == 0 && len(s.DefBody.IffFacts) == 0 {
		return strings.TrimSuffix(builder.String(), glob.KeySymbolColon)
	}

	builder.WriteByte('\n')
	for _, domFact := range s.DefBody.DomFacts {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(domFact.String(), 1))
		builder.WriteString("\n")
	}

	if len(s.DefBody.IffFacts) > 0 {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents("iff:", 1))
		builder.WriteString("\n")

		for _, iffFact := range s.DefBody.IffFacts {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(iffFact.String(), 2))
			builder.WriteString("\n")
		}
	}

	return builder.String()
}

func (l *UniFactStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordForall)
	builder.WriteString(" ")

	if len(l.Params) > 0 {
		for i := range len(l.Params) - 1 {
			builder.WriteString(l.Params[i])
			builder.WriteString(" ")
			builder.WriteString(l.ParamSets[i].String())
			builder.WriteString(", ")
		}
		builder.WriteString(l.Params[len(l.Params)-1])
		builder.WriteString(" ")
		builder.WriteString(l.ParamSets[len(l.Params)-1].String())
	}
	builder.WriteString(":\n")
	for _, condFact := range l.DomFacts {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(condFact.String(), 1))
		builder.WriteByte('\n')
	}
	builder.WriteString(glob.SplitLinesAndAdd4NIndents("then:", 1))
	builder.WriteByte('\n')
	if len(l.ThenFacts) > 0 {
		for i := 0; i < len(l.ThenFacts)-1; i++ {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(l.ThenFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(l.ThenFacts[len(l.ThenFacts)-1].String(), 2))
	}

	return builder.String()
}

func (l *UniFactWithIffStmt) String() string {
	var builder strings.Builder

	builder.WriteString(strings.TrimSuffix(l.UniFact.String(), "\n"))

	if l.IffFacts != nil && len(l.IffFacts) > 0 {
		builder.WriteByte('\n')
		builder.WriteString(glob.SplitLinesAndAdd4NIndents("iff:", 1))
		builder.WriteByte('\n')
		for i := 0; i < len(l.IffFacts)-1; i++ {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(l.IffFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(l.IffFacts[len(l.IffFacts)-1].String(), 2))
	}
	return builder.String()
}

func (head DefHeader) StringWithoutColonAtEnd() string {
	var builder strings.Builder
	builder.WriteString(head.Name)
	builder.WriteString("(")

	if len(head.Params) > 0 {
		for i := 0; i < len(head.Params)-1; i++ {
			builder.WriteString(head.Params[i])
			builder.WriteString(" ")
			builder.WriteString(head.SetParams[i].String())
			builder.WriteString(",")
		}
		builder.WriteString(head.Params[len(head.Params)-1])
		builder.WriteString(" ")
		builder.WriteString(head.SetParams[len(head.Params)-1].String())
	}

	builder.WriteString(")")
	return builder.String()
}

func (head DefHeader) String() string {
	var builder strings.Builder
	builder.WriteString(head.StringWithoutColonAtEnd())
	builder.WriteString(glob.KeySymbolColon)
	return builder.String()
}

// Stringer 是标准库的接口，要求实现 String() string
type Stringer interface {
	String() string
}

// 如果不用Generics,直接用 stmtSlice []Stringer，那即使 []T的T对应了Stringer，也不通过，因为golang只能对应 Stringer 和 T，而不能 []Stringer 对应 []T
// Generics 的另外一个作用是编译时确定，而不是运行时。所以节约了运行开销
func strOfNonEmptyFactStmtSlice[T Stringer](stmtSlice []T, indent uint32) string {
	var builder strings.Builder

	if len(stmtSlice) == 0 {
		return ""
	}

	for i := 0; i < len(stmtSlice)-1; i++ {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmtSlice[i].String(), indent))
		builder.WriteByte('\n')
	}
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmtSlice[len(stmtSlice)-1].String(), indent))
	builder.WriteByte('\n')

	return builder.String()
}

func (stmt *HaveStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordHave)
	builder.WriteString(" ")
	if len(stmt.ObjNames) > 0 {
		for i := range len(stmt.ObjNames) - 1 {
			builder.WriteString(stmt.ObjNames[i])
			builder.WriteString(", ")
		}
		builder.WriteString(stmt.ObjNames[len(stmt.ObjNames)-1])
	}
	builder.WriteByte(' ')
	builder.WriteString(glob.KeywordSt)
	builder.WriteString(" ")

	builder.WriteString(stmt.Fact.String())
	return builder.String()
}

func (f *FcAtom) String() string {
	if f.PkgName == glob.EmptyPkg {
		return string(f.Name)
	} else {
		return fmt.Sprintf("%s::%s", f.PkgName, string(f.Name))
	}
}

func (f *FcFn) String() string {
	if IsFnSet(f) {
		return fnSetString(f)
	}

	if IsFcAtomWithNameAndEmptyPkg(f.FnHead, glob.KeySymbolDot) {
		return fmt.Sprintf("%s.%s", f.Params[0].String(), f.Params[1].String())
	}

	if ok, str := hasBuiltinOptAndToString(f); ok {
		return str
	}

	var builder strings.Builder
	builder.WriteString(f.FnHead.String())
	builder.WriteString("(")
	if len(f.Params) > 0 {
		for i := range len(f.Params) - 1 {
			builder.WriteString(f.Params[i].String())
			builder.WriteString(", ")
		}
		builder.WriteString(f.Params[len(f.Params)-1].String())
	}
	builder.WriteString(")")

	return builder.String()
}

func (stmt *SupposeStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordSuppose)
	builder.WriteString(" ")
	builder.WriteString(stmt.Fact.String())
	builder.WriteString(":\n")
	if len(stmt.Body) > 0 {
		for i := range len(stmt.Body) - 1 {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Body[i].String(), 1))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Body[len(stmt.Body)-1].String(), 1))
	}
	return builder.String()
}

func (stmt *WithStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordWith)
	builder.WriteString(" ")
	builder.WriteString(stmt.Fact.String())
	builder.WriteString(":\n")
	if len(stmt.Body) > 0 {
		for i := range len(stmt.Body) - 1 {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Body[i].String(), 1))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Body[len(stmt.Body)-1].String(), 1))
	}
	return builder.String()
}

func (stmt *ProveInEachCaseStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProveInEachCase)
	builder.WriteString(":\n")
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.OrFact.String(), 1))
	builder.WriteByte('\n')
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordThen, 1))
	builder.WriteByte(':')
	builder.WriteByte('\n')
	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.ThenFacts[0].String(), 2))
	builder.WriteByte('\n')
	// Handle last proof block
	if len(stmt.Proofs) > 0 {
		for i := range len(stmt.Proofs) {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordProve, 1))
			builder.WriteByte(':')
			builder.WriteByte('\n')

			if len(stmt.Proofs[i]) > 0 {
				for j := range len(stmt.Proofs[i]) - 1 {
					builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Proofs[i][j].String(), 2))
					builder.WriteByte('\n')
				}
				builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Proofs[i][len(stmt.Proofs[i])-1].String(), 2))
			}
			builder.WriteByte('\n')
		}
	}
	return strings.TrimSuffix(builder.String(), "\n")
}

func (stmt *KnowPropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(" ")
	builder.WriteString(stmt.Prop.String())
	return builder.String()
}

// func (stmt *ProveOrStmt) String() string {
// 	var builder strings.Builder
// 	builder.WriteString(glob.KeywordProveOr)
// 	builder.WriteString(" ")
// 	for index := range stmt.Indexes {
// 		builder.WriteString(strconv.Itoa(index))
// 		builder.WriteString(", ")
// 	}
// 	builder.WriteString(":\n")
// 	builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.OrFact.String(), 1))
// 	builder.WriteByte('\n')
// 	builder.WriteString(glob.SplitLinesAndAdd4NIndents(glob.KeywordProve, 1))
// 	builder.WriteByte(':')
// 	builder.WriteByte('\n')
// 	for i := range len(stmt.Proofs) - 1 {
// 		builder.WriteString(glob.SplitLinesAndAdd4NIndents(stmt.Proofs[i].String(), 2))
// 		builder.WriteByte('\n')
// 	}
// 	return strings.TrimSuffix(builder.String(), "\n")
// }

func (stmt *KnowExistPropStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordKnow)
	builder.WriteString(" ")
	builder.WriteString(stmt.ExistProp.String())
	return builder.String()
}

func fnSetString(f *FcFn) string {
	var builder strings.Builder
	builder.WriteString(f.FnHead.String())
	builder.WriteString(" ")
	builder.WriteString(f.Params[0].String())
	return builder.String()
}

func SupposeNewFactsMsg(stmt *SupposeStmt, messages []string) string {
	builder := strings.Builder{}
	builder.WriteString(fmt.Sprintf("know from true %s fact:\n", glob.KeywordSuppose))
	builder.WriteString(fmt.Sprintf("%s %s:\n", glob.KeywordSuppose, stmt.Fact.String()))
	for _, message := range messages {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(message, 1))
		builder.WriteByte('\n')
	}
	return builder.String()
}

func (stmt *OrStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordOr)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, orFact := range stmt.Facts {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(orFact.String(), 1))
		builder.WriteByte('\n')
	}
	return strings.TrimSuffix(builder.String(), "\n")
}

func (stmt *ImportStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordImport)
	builder.WriteString(" ")
	if stmt.AsPkgName != "" {
		builder.WriteString(stmt.AsPkgName)
		builder.WriteString(" ")
	}
	builder.WriteString(glob.KeySymbolDoubleQuote)
	builder.WriteString(stmt.Path)
	builder.WriteString(glob.KeySymbolDoubleQuote)
	return builder.String()
}

func (stmt *ProveStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProve)
	builder.WriteString(glob.KeySymbolColon)
	builder.WriteByte('\n')
	for _, proof := range stmt.Proof {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(proof.String(), 1))
		builder.WriteByte('\n')
	}
	return builder.String()
}
