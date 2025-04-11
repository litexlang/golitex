package litex_ast

import (
	glob "golitex/litex_global"
	"strings"
)

func (stmt *KnowStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordKnow)
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
	var builder strings.Builder

	if !stmt.IsTrue {
		builder.WriteString(glob.KeywordNot)
		builder.WriteByte(' ')
	}

	if stmt.PropName.PkgName == "" && glob.IsKeySymbol(stmt.PropName.Value) {
		builder.WriteString(stmt.Params[0].String())
		builder.WriteByte(' ')
		builder.WriteString(stmt.PropName.String())
		builder.WriteByte(' ')
		builder.WriteString(stmt.Params[1].String())
		return builder.String()
	}

	builder.WriteByte('$')
	builder.WriteString(stmt.PropName.String())
	builder.WriteByte('(')
	builder.WriteString(FcSliceString(stmt.Params))
	builder.WriteByte(')')

	return builder.String()
}

func (stmt *DefObjStmt) String() string {
	var builder strings.Builder

	builder.WriteString("obj ")
	for i, objName := range stmt.Objs {
		builder.WriteString(objName)
		builder.WriteByte(' ')
		builder.WriteString(stmt.ObjSets[i].String())
	}

	if len(stmt.Facts) > 0 {
		builder.WriteString(" :")
		builder.WriteByte('\n')
		builder.WriteString(strOfNonEmptyFactStmtSlice(stmt.Facts, 1))
	}

	return builder.String()
}

func (c *DefInterfaceStmt) String() string { panic("") }
func (f *DefTypeStmt) String() string      { panic("") }
func (fact *DefConPropStmt) String() string {
	var builder strings.Builder

	builder.WriteString(fact.DefHeader.String())
	builder.WriteByte('\n')

	if len(fact.DomFacts) > 0 {
		builder.WriteString(strOfNonEmptyFactStmtSlice(fact.DomFacts, 1))
	}

	builder.WriteString(glob.SplitLinesAndAdd4NIndents("iff:", 1))
	builder.WriteByte('\n')

	if len(fact.IffFacts) > 0 {
		for i := 0; i < len(fact.IffFacts)-1; i++ {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.IffFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.IffFacts[len(fact.IffFacts)-1].String(), 2))
	}

	return builder.String()
}
func (f *DefConFnStmt) String() string {
	return ""
}
func (f *ClaimProveStmt) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordProve)
	builder.WriteString(":\n")
	if len(f.ToCheckFacts) != 0 {
		panic("TODO")
	} else {
		for _, fact := range f.Proofs {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.String(), 1))
			builder.WriteByte('\n')
		}
	}
	return strings.TrimSpace(builder.String())
}
func (s *DefConExistPropStmt) String() string        { panic("") }
func (s *HaveStmt) String() string                   { panic("") }
func (s *ClaimProveByContradictStmt) String() string { panic("") }
func (s *AxiomStmt) String() string                  { panic("") }
func (s *ThmStmt) String() string                    { panic("") }
func (fact *CondFactStmt) String() string {
	var builder strings.Builder

	builder.WriteString(glob.KeywordWhen)
	builder.WriteString(":\n")
	for _, condFact := range fact.CondFacts {
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(condFact.String(), 1))
		builder.WriteByte('\n')
	}

	builder.WriteString(glob.SplitLinesAndAdd4NIndents("then:", 1))
	builder.WriteByte('\n')
	if len(fact.ThenFacts) > 0 {
		for i := 0; i < len(fact.ThenFacts)-1; i++ {
			builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.ThenFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.SplitLinesAndAdd4NIndents(fact.ThenFacts[len(fact.ThenFacts)-1].String(), 2))
	}
	return builder.String()
}
func (s *GenUniStmt) String() string { panic("") }

func (l *ConUniFactStmt) String() string {
	var builder strings.Builder

	builder.WriteString("forall ")
	if len(l.Params) > 0 {
		for i := 0; i < len(l.Params)-1; i++ {
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

func (head ConDefHeader) String() string {
	var builder strings.Builder
	builder.WriteString("prop ")
	builder.WriteString(head.Name)
	builder.WriteString(" (")

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

	builder.WriteString("):")
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
