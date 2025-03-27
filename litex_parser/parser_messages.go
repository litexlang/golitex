package litexparser

import (
	"fmt"
	msg "golitex/litex_messages"
	"strings"
)

func (stmt *KnowStmt) String() string {
	ret := "know:\n"
	for _, fact := range stmt.Facts {
		ret += fmt.Sprintf("    %s\n", fact.String())
	}
	return ret
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
func (l *ConcreteForallStmt) String() string         { panic("") }
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

	builder.WriteString("    then:\n")
	for _, thenFact := range fact.ThenFacts {
		builder.WriteString(msg.LineHead4Indents(thenFact.String(), 2))
		builder.WriteByte('\n')
	}

	return builder.String()
}
func (s *GenericForallStmt) String() string { panic("") }
