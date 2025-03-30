package litexparser

type Stmt interface {
	stmt()
	String() string
}

func (stmt *DefObjStmt) stmt() {}

func (c *DefInterfaceStmt) stmt()          {}
func (f *DefTypeStmt) stmt()               {}
func (c *DefConcreteNormalPropStmt) stmt() {}
func (f *DefConcreteFnStmt) stmt()         {}
func (l *UniFactStmt) stmt()               {}

// func (r *RelaFactStmt) stmt()               {}
func (p *FuncFactStmt) stmt()               {}
func (f *ClaimProveStmt) stmt()             {}
func (f *KnowStmt) stmt()                   {}
func (s *DefConcreteExistPropStmt) stmt()   {}
func (s *HaveStmt) stmt()                   {}
func (s *ClaimProveByContradictStmt) stmt() {}
func (s *AxiomStmt) stmt()                  {}
func (s *ThmStmt) stmt()                    {}
func (s *CondFactStmt) stmt()               {}
func (s *GenericUniStmt) stmt()             {}

// 主要有3个执行时要考虑的事情：1. know fact 2. check fact3. use known facts to check current fact
type FactStmt interface {
	factStmt()
	stmt()
	String() string
}

// func (r *RelaFactStmt) factStmt()   {}
func (p *FuncFactStmt) factStmt()   {}
func (p *CondFactStmt) factStmt()   {}
func (l *UniFactStmt) factStmt()    {}
func (p *GenericUniStmt) factStmt() {}

type SpecFactParams struct {
	ObjParams []Fc
}

// type SpecFactStmt interface {
// 	specFactStmtSetT(b bool)
// 	factStmt()
// 	stmt()
// 	String() string
// }

// func (r *RelaFactStmt) specFactStmtSetT(b bool) { r.IsTrue = b }
// func (f *FuncFactStmt) specFactStmtSetT(b bool) { f.IsTrue = b }

type ClaimStmt interface {
	claimStmt()
	stmt()
	String() string
}

func (s *ClaimProveStmt) claimStmt()             {}
func (s *ClaimProveByContradictStmt) claimStmt() {}

type DefPropStmt interface {
	defPropStmt()
	stmt()
}

func (s *DefConcreteExistPropStmt) defPropStmt()  {}
func (s *DefConcreteNormalPropStmt) defPropStmt() {}

type DefMember interface {
	defMember()
}

func (s *DefObjStmt) defMember()                {}
func (s *DefConcreteFnStmt) defMember()         {}
func (s *DefConcreteNormalPropStmt) defMember() {}
func (s *DefConcreteExistPropStmt) defMember()  {}

type ForallStmt interface {
	factStmt()
	stmt()
	String() string
	forallStmt()
}

func (s *UniFactStmt) forallStmt()    {}
func (s *GenericUniStmt) forallStmt() {}
