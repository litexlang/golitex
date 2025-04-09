package litex_ast

type Stmt interface {
	stmt()
	String() string
}

func (stmt *DefObjStmt) stmt()              {}
func (c *DefInterfaceStmt) stmt()           {}
func (f *DefTypeStmt) stmt()                {}
func (c *DefConPropStmt) stmt()             {}
func (f *DefConFnStmt) stmt()               {}
func (l *ConUniFactStmt) stmt()             {}
func (p *SpecFactStmt) stmt()               {}
func (f *ClaimProveStmt) stmt()             {}
func (f *KnowStmt) stmt()                   {}
func (s *DefConExistPropStmt) stmt()        {}
func (s *HaveStmt) stmt()                   {}
func (s *ClaimProveByContradictStmt) stmt() {}
func (s *AxiomStmt) stmt()                  {}
func (s *ThmStmt) stmt()                    {}
func (s *CondFactStmt) stmt()               {}
func (s *GenUniStmt) stmt()                 {}

// 主要有3个执行时要考虑的事情：1. know fact 2. check fact3. use known facts to check current fact
type FactStmt interface {
	factStmt()
	stmt()
	String() string
	Instantiate(map[string]Fc) (FactStmt, error)
}

// func (r *RelaFactStmt) factStmt()   {}
func (p *SpecFactStmt) factStmt()   {}
func (p *CondFactStmt) factStmt()   {}
func (l *ConUniFactStmt) factStmt() {}
func (p *GenUniStmt) factStmt()     {}

type SpecFactParams struct {
	ObjParams []Fc
}

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

func (s *DefConExistPropStmt) defPropStmt() {}
func (s *DefConPropStmt) defPropStmt()      {}

type DefMember interface {
	defMember()
}

func (s *DefObjStmt) defMember()          {}
func (s *DefConFnStmt) defMember()        {}
func (s *DefConPropStmt) defMember()      {}
func (s *DefConExistPropStmt) defMember() {}

type UniFactStmt interface {
	factStmt()
	stmt()
	String() string
	forallStmt()
	Instantiate(map[string]Fc) (FactStmt, error)
}

func (s *ConUniFactStmt) forallStmt() {}
func (s *GenUniStmt) forallStmt()     {}
