package litexparser

import (
	"fmt"
	"strings"
)

func (stmt *KnowStmt) String() string {
	return fmt.Sprintf("know %s", stmt.Facts)
}

func (stmt *FuncFactStmt) String() string {
	paramStrList := []string{}
	for _, param := range stmt.Params {
		paramStrList = append(paramStrList, param.String())
	}
	paramStr := strings.Join(paramStrList, ", ")

	if stmt.IsTrue {
		return fmt.Sprintf("$%v(%v)", stmt.Opt.String(), paramStr)
	} else {
		return fmt.Sprintf("not $%v(%v)", stmt.Opt.String(), paramStr)
	}
}

func (stmt *RelationFactStmt) String() string {
	return fmt.Sprintf("%v %v %v", stmt.Params[0].String(), stmt.Opt, stmt.Params[1].String())
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
