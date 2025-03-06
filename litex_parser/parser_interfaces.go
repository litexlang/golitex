package litexparser

type Stmt interface {
	stmt()
}

func (stmt *DefVarStmt) stmt()              {}
func (c *DefConceptStmt) stmt()             {}
func (f *DefTypeStmt) stmt()                {}
func (c *DefPropStmt) stmt()                {}
func (f *DefFnStmt) stmt()                  {}
func (l *BlockForallStmt) stmt()            {}
func (r *RelationFactStmt) stmt()           {}
func (p *FuncFactStmt) stmt()               {}
func (f *ClaimProveStmt) stmt()             {}
func (f *DefAliasStmt) stmt()               {}
func (f *KnowStmt) stmt()                   {}
func (s *DefExistStmt) stmt()               {}
func (s *HaveStmt) stmt()                   {}
func (s *DefMemberStmt) stmt()              {}
func (s *DefTypeMemberStmt) stmt()          {}
func (s *ClaimProveByContradictStmt) stmt() {}
func (s *AxiomStmt) stmt()                  {}
func (s *ThmStmt) stmt()                    {}
func (s *CondFactStmt) stmt()               {}

// func (s *InlineForallStmt) stmt()           {}

type FactStmt interface {
	factStmt()
	stmt()
}

func (l *BlockForallStmt) factStmt()  {}
func (r *RelationFactStmt) factStmt() {}
func (p *FuncFactStmt) factStmt()     {}
func (p *CondFactStmt) factStmt()     {}

// func (p *InlineForallStmt) factStmt() {}

type SpecFactParams struct {
	TypeParams []TypeVarStr
	VarParams  []Fc
}

type SpecFactStmt interface {
	notFactStmtSetT(b bool)
	factStmt()
	stmt()
	GetTypeParamsAndParams() *SpecFactParams
}

func (r *RelationFactStmt) notFactStmtSetT(b bool) { r.IsTrue = b }
func (f *FuncFactStmt) notFactStmtSetT(b bool)     { f.IsTrue = b }
func (f *RelationFactStmt) GetTypeParamsAndParams() *SpecFactParams {
	panic("TODO: Implement type specific operator overloading first")
}
func (f *FuncFactStmt) GetTypeParamsAndParams() *SpecFactParams {
	return &SpecFactParams{[]TypeVarStr{}, []Fc{}}
}

type fcType interface {
	fcType()
}

func (f FcVarType) fcType()          {}
func (f *FcFnType) fcType()          {}
func (f *FcPropType) fcType()        {}
func (f *UndefinedFnType) fcType()   {}
func (f *UndefinedVarType) fcType()  {}
func (f *UndefinedPropType) fcType() {}

type fcDecl interface {
	fcDecl()
}

func (f *FcVarDecl) fcDecl() {}
func (f *FcFnDecl) fcDecl()  {}
func (f *PropDecl) fcDecl()  {}

type FcVarTypeValue interface {
	fcVarTypeValue()
}

func (f FcVarTypeStrValue) fcVarTypeValue()   {}
func (f *FcVarTypeFuncValue) fcVarTypeValue() {}

type ClaimStmt interface {
	claimStmt()
	stmt()
}

func (s *ClaimProveStmt) claimStmt()             {}
func (s *ClaimProveByContradictStmt) claimStmt() {}

// syntax sugar for prop exist decl followed by forall such prop is valid.

type DefPropExistDeclStmt interface {
	defPropExistDeclStmt()
	stmt()
}

func (s *DefExistStmt) defPropExistDeclStmt() {}
func (s *DefPropStmt) defPropExistDeclStmt()  {}

type InlineFactStmt interface {
	inlineFactStmt()
	factStmt()
	stmt()
}

func (r *RelationFactStmt) inlineFactStmt() {}
func (p *FuncFactStmt) inlineFactStmt()     {}
func (p *CondFactStmt) inlineFactStmt()     {}

// func (p *InlineForallStmt) inlineFactStmt() {}
