package litexparser

import (
	glob "golitex/litex_global"
	"strings"
)

func (stmt *KnowStmt) String() string {
	var builder strings.Builder

	builder.WriteString("know:\n")
	if len(stmt.Facts) > 0 {
		for i := 0; i < len(stmt.Facts)-1; i++ {
			builder.WriteString(glob.LineHead4Indents(stmt.Facts[i].String(), 1))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.LineHead4Indents(stmt.Facts[len(stmt.Facts)-1].String(), 1))
	}
	return builder.String()
}

func (stmt *SpecFactStmt) String() string {
	var builder strings.Builder

	if !stmt.IsTrue {
		builder.WriteString("not ")
	}

	if stmt.PropName.PkgName == "" && glob.IsBuiltinSymbol(stmt.PropName.Value) {
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

// func (stmt *RelaFactStmt) String() string {
// 	return fmt.Sprintf("%v %v %v", stmt.Params[0].String(), stmt.Opt.String(), stmt.Params[1].String())
// }

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
		// // 遍历前 n-1 个元素，每个后面加换行
		// for i := 0; i < len(fact.DomFacts)-1; i++ {
		// 	builder.WriteString(glob.LineHead4Indents(fact.DomFacts[i].String(), 1))
		// 	builder.WriteByte('\n')
		// }
		// // 单独处理最后一个元素，不加换行
		// builder.WriteString(glob.LineHead4Indents(fact.DomFacts[len(fact.DomFacts)-1].String(), 1))
		// builder.WriteByte('\n')
	}

	builder.WriteString(glob.LineHead4Indents("iff:", 1))
	builder.WriteByte('\n') // 把 \n 单独拿出来，否则会让下面一行多空几格子

	if len(fact.IffFacts) > 0 {
		// builder.WriteStr 2))
		// // 遍历前 n-1 个元素，每个后面加换行
		for i := 0; i < len(fact.IffFacts)-1; i++ {
			builder.WriteString(glob.LineHead4Indents(fact.IffFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		// 单独处理最后一个元素，不加换行
		builder.WriteString(glob.LineHead4Indents(fact.IffFacts[len(fact.IffFacts)-1].String(), 2))
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
			builder.WriteString(glob.LineHead4Indents(fact.String(), 1))
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
		builder.WriteString(glob.LineHead4Indents(condFact.String(), 1))
		builder.WriteByte('\n')
	}

	builder.WriteString(glob.LineHead4Indents("then:", 1))
	builder.WriteByte('\n')
	if len(fact.ThenFacts) > 0 {
		// builder.WriteString(strOfNonEmptyFactStmtSlice(fact.ThenFacts, 2))
		// 遍历前 n-1 个元素，每个后面加换行
		for i := 0; i < len(fact.ThenFacts)-1; i++ {
			builder.WriteString(glob.LineHead4Indents(fact.ThenFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		// 单独处理最后一个元素，不加换行
		builder.WriteString(glob.LineHead4Indents(fact.ThenFacts[len(fact.ThenFacts)-1].String(), 2))
	}
	return builder.String()
}
func (s *GenericUniStmt) String() string { panic("") }

func (l *UniFactStmt) String() string {
	var builder strings.Builder

	builder.WriteString("forall ")
	if len(l.Params) > 0 {
		for i := 0; i < len(l.Params)-1; i++ {
			builder.WriteString(l.Params[i])
			builder.WriteString(" ")
			builder.WriteString(l.ParamTypes[i].String())
			builder.WriteString(", ")
		}
		builder.WriteString(l.Params[len(l.Params)-1])
		builder.WriteString(" ")
		builder.WriteString(l.ParamTypes[len(l.Params)-1].String())
	}
	builder.WriteString(":\n")
	for _, condFact := range l.DomFacts {
		builder.WriteString(glob.LineHead4Indents(condFact.String(), 1))
		builder.WriteByte('\n')
	}
	builder.WriteString(glob.LineHead4Indents("then:", 1))
	builder.WriteByte('\n')
	if len(l.ThenFacts) > 0 {
		for i := 0; i < len(l.ThenFacts)-1; i++ {
			builder.WriteString(glob.LineHead4Indents(l.ThenFacts[i].String(), 2))
			builder.WriteByte('\n')
		}
		builder.WriteString(glob.LineHead4Indents(l.ThenFacts[len(l.ThenFacts)-1].String(), 2))
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
			builder.WriteString(head.TypeParams[i].String())
			builder.WriteString(",")
		}
		builder.WriteString(head.Params[len(head.Params)-1])
		builder.WriteString(" ")
		builder.WriteString(head.TypeParams[len(head.Params)-1].String())
	}

	builder.WriteString("):")
	return builder.String()
}

// Stringer 是标准库的接口，要求实现 String() string
type Stringer interface {
	String() string
}

// 修改后的泛型函数，支持 T 或 *T 只要它们实现 String()
func strOfNonEmptyFactStmtSlice[T Stringer](stmtSlice []T, indent uint32) string {
	var builder strings.Builder

	if len(stmtSlice) == 0 {
		return ""
	}

	// 前 n-1 个元素加换行
	for i := 0; i < len(stmtSlice)-1; i++ {
		builder.WriteString(glob.LineHead4Indents(stmtSlice[i].String(), indent))
		builder.WriteByte('\n')
	}
	// 最后一个元素不加换行（但你的代码里仍然加了 \n？）
	builder.WriteString(glob.LineHead4Indents(stmtSlice[len(stmtSlice)-1].String(), indent))
	builder.WriteByte('\n')

	return builder.String()
}
