package litexparser

type Stmt interface {
	stmt()
	String() string
}

func (stmt *DefObjStmt) stmt() {}

func (c *DefInterfaceStmt) stmt()           {}
func (f *DefTypeStmt) stmt()                {}
func (c *DefConcreteNormalPropStmt) stmt()  {}
func (f *DefConcreteFnStmt) stmt()          {}
func (l *ConcreteForallStmt) stmt()         {}
func (r *RelationFactStmt) stmt()           {}
func (p *FuncFactStmt) stmt()               {}
func (f *ClaimProveStmt) stmt()             {}
func (f *KnowStmt) stmt()                   {}
func (s *DefConcreteExistPropStmt) stmt()   {}
func (s *HaveStmt) stmt()                   {}
func (s *ClaimProveByContradictStmt) stmt() {}
func (s *AxiomStmt) stmt()                  {}
func (s *ThmStmt) stmt()                    {}
func (s *ConditionalFactStmt) stmt()        {}
func (s *GenericForallStmt) stmt()          {}

type FactStmt interface {
	factStmt()
	stmt()
	String() string
}

func (r *RelationFactStmt) factStmt()    {}
func (p *FuncFactStmt) factStmt()        {}
func (p *ConditionalFactStmt) factStmt() {}
func (l *ConcreteForallStmt) factStmt()  {}
func (p *GenericForallStmt) factStmt()   {}

type SpecFactParams struct {
	ObjParams []Fc
}

type SpecFactStmt interface {
	specFactStmtSetT(b bool)
	factStmt()
	stmt()
	String() string
}

func (r *RelationFactStmt) specFactStmtSetT(b bool) { r.IsTrue = b }
func (f *FuncFactStmt) specFactStmtSetT(b bool)     { f.IsTrue = b }

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

func (s *ConcreteForallStmt) forallStmt() {}
func (s *GenericForallStmt) forallStmt()  {}
