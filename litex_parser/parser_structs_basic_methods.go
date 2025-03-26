package litexparser

import (
	"fmt"
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

func (stmt *RelationFactStmt) String() string {
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
func (s *ConditionalFactStmt) String() string        { panic("") }
func (s *GenericForallStmt) String() string          { panic("") }
