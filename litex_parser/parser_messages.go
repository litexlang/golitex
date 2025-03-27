package litexparser

import (
	"fmt"
	msg "golitex/litex_messages"
	"strings"
)

func (stmt *KnowStmt) String() string {
	var builder strings.Builder

	builder.WriteString("know:\n")
	if len(stmt.Facts) > 0 {
		for i := 0; i < len(stmt.Facts)-1; i++ {
			builder.WriteString(msg.LineHead4Indents(stmt.Facts[i].String(), 1))
			builder.WriteByte('\n')
		}
		builder.WriteString(msg.LineHead4Indents(stmt.Facts[len(stmt.Facts)-1].String(), 1))
	}
	return builder.String()
}

func (stmt *FuncFactStmt) String() string {
	if stmt.IsTrue {
		return fmt.Sprintf("$%v(%v)", stmt.Opt.String(), FcSliceString(&stmt.Params))
	} else {
		return fmt.Sprintf("not $%v(%v)", stmt.Opt.String(), FcSliceString(&stmt.Params))
	}
}

func (stmt *RelaFactStmt) String() string {
	return fmt.Sprintf("%v %v %v", stmt.Params[0].String(), stmt.Opt.String(), stmt.Params[1].String())
}

func (stmt *DefObjStmt) String() string { panic("") }

func (c *DefInterfaceStmt) String() string           { panic("") }
func (f *DefTypeStmt) String() string                { panic("") }
func (c *DefConcreteNormalPropStmt) String() string  { panic("") }
func (f *DefConcreteFnStmt) String() string          { panic("") }
func (l *UniFactStmt) String() string                { panic("") }
func (f *ClaimProveStmt) String() string             { panic("") }
func (s *DefConcreteExistPropStmt) String() string   { panic("") }
func (s *HaveStmt) String() string                   { panic("") }
func (s *ClaimProveByContradictStmt) String() string { panic("") }
func (s *AxiomStmt) String() string                  { panic("") }
func (s *ThmStmt) String() string                    { panic("") }
func (fact *CondFactStmt) String() string {
	var builder strings.Builder

	builder.WriteString("when:\n")
	for _, condFact := range fact.CondFacts {
		builder.WriteString(msg.LineHead4Indents(condFact.String(), 1))
		builder.WriteByte('\n')
	}

	builder.WriteString(msg.LineHead4Indents("then:\n", 1))
	if len(fact.ThenFacts) > 0 {
		// 遍历前 n-1 个元素，每个后面加换行
		for i := 0; i < len(fact.ThenFacts)-1; i++ {
			builder.WriteString(msg.LineHead4Indents(fact.ThenFacts[i].String(), 1))
			builder.WriteByte('\n')
		}
		// 单独处理最后一个元素，不加换行
		builder.WriteString(msg.LineHead4Indents(fact.ThenFacts[len(fact.ThenFacts)-1].String(), 1))
	}
	return builder.String()
}
func (s *GenericUniStmt) String() string { panic("") }
