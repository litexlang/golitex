package litexparser

type Stmt interface {
	stmt()
	String() string
}

func (stmt *DefObjStmt) stmt() {}

func (c *DefInterfaceStmt) stmt()   {}
func (f *DefTypeStmt) stmt()        {}
func (c *DefSpecPropStmt) stmt()    {}
func (f *DefFnStmt) stmt()          {}
func (l *ConcreteForallStmt) stmt() {}
func (r *RelationFactStmt) stmt()   {}
func (p *FuncFactStmt) stmt()       {}
func (f *ClaimProveStmt) stmt()     {}

// func (f *DefAliasStmt) stmt()               {}
func (f *KnowStmt) stmt()                   {}
func (s *DefExistPropStmt) stmt()           {}
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
	notFactStmtSetT(b bool)
	factStmt()
	stmt()
	GetTypeParamsAndParams() *SpecFactParams
	String() string
}

func (r *RelationFactStmt) notFactStmtSetT(b bool) { r.IsTrue = b }
func (f *FuncFactStmt) notFactStmtSetT(b bool)     { f.IsTrue = b }
func (f *RelationFactStmt) GetTypeParamsAndParams() *SpecFactParams {
	panic("TODO: Implement type specific operator overloading first")
}

func (f *FuncFactStmt) GetTypeParamsAndParams() *SpecFactParams {
	return &SpecFactParams{[]Fc{}}
}

// type FcObjTypeValue interface {
// 	fcObjTypeValue()
// }

// func (f FcObjTypeStrValue) fcObjTypeValue()   {}
// func (f *FcObjTypeFuncValue) fcObjTypeValue() {}

type ClaimStmt interface {
	claimStmt()
	stmt()
	String() string
}

func (s *ClaimProveStmt) claimStmt()             {}
func (s *ClaimProveByContradictStmt) claimStmt() {}

type DefPropStmt interface {
	defPropExistDeclStmt()
	stmt()
}

func (s *DefExistPropStmt) defPropExistDeclStmt() {}
func (s *DefSpecPropStmt) defPropExistDeclStmt()  {}

type InlineFactStmt interface {
	inlineFactStmt()
	factStmt()
	stmt()
}

func (r *RelationFactStmt) inlineFactStmt()    {}
func (p *FuncFactStmt) inlineFactStmt()        {}
func (p *ConditionalFactStmt) inlineFactStmt() {}

type TypeMember interface {
	typeMember()
}

func (s *DefObjStmt) typeMember()      {}
func (s *DefFnStmt) typeMember()       {}
func (s *DefSpecPropStmt) typeMember() {}
func (s *DefTypeStmt) typeMember()     {}

type InstanceMember interface {
	instanceMember()
}

func (s *DefObjStmt) instanceMember()       {}
func (s *DefFnStmt) instanceMember()        {}
func (s *DefSpecPropStmt) instanceMember()  {}
func (s *DefExistPropStmt) instanceMember() {}

type ForallStmt interface {
	factStmt()
	stmt()
	String() string
	forallStmt()
}

func (s *ConcreteForallStmt) forallStmt() {}
func (s *GenericForallStmt) forallStmt()  {}
