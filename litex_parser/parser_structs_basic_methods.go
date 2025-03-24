package litexparser

import "fmt"

func (stmt *KnowStmt) String() string {
	return fmt.Sprintf("know %s", stmt.Facts)
}

func (stmt *FuncFactStmt) String() string {
	if stmt.IsTrue {
		return fmt.Sprintf("$%v", stmt.Opt)
	} else {
		return fmt.Sprintf("not $%v", stmt.Opt)
	}
}

func (stmt *RelationFactStmt) String() string {
	return fmt.Sprintf("%v %v %v", stmt.Params[0], stmt.Opt, stmt.Params[1])
}

func (stmt *DefObjStmt) String() string { panic("") }

func (c *DefInterfaceStmt) String() string   { panic("") }
func (f *DefTypeStmt) String() string        { panic("") }
func (c *DefPropStmt) String() string        { panic("") }
func (f *DefFnStmt) String() string          { panic("") }
func (l *ConcreteForallStmt) String() string { panic("") }
func (f *ClaimProveStmt) String() string     { panic("") }

// func (f *DefAliasStmt) String() string               { panic("") }
func (s *DefExistStmt) String() string               { panic("") }
func (s *HaveStmt) String() string                   { panic("") }
func (s *ClaimProveByContradictStmt) String() string { panic("") }
func (s *AxiomStmt) String() string                  { panic("") }
func (s *ThmStmt) String() string                    { panic("") }
func (s *ConditionalFactStmt) String() string        { panic("") }
func (s *GenericForallStmt) String() string          { panic("") }
