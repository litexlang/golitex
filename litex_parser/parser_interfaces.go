package litexparser

type Fc interface {
	fc()
	String() string
}

func (fc *TypedFc) fc()           {}
func (f *CalledFcFnRetValue) fc() {}
func (f FcStr) fc()               {}
func (f *FcFnCallChain) fc()      {}

type Stmt interface {
	stmt()
}

func (stmt *DefVarStmt) stmt()              {}
func (c *DefConceptStmt) stmt()             {}
func (f *DefTypeStmt) stmt()                {}
func (c *DefPropStmt) stmt()                {}
func (f *DefFnStmt) stmt()                  {}
func (l *ForallStmt) stmt()                 {}
func (r *RelationFactStmt) stmt()           {}
func (p *FuncPropStmt) stmt()               {}
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
func (s *InlineIfFactStmt) stmt()           {}
func (s *InlineForallSubStmt) stmt()        {}

type FactStmt interface {
	factStmt()
	stmt()
}

func (l *ForallStmt) factStmt()          {}
func (r *RelationFactStmt) factStmt()    {}
func (p *FuncPropStmt) factStmt()        {}
func (p *InlineIfFactStmt) factStmt()    {}
func (p *InlineForallSubStmt) factStmt() {}

type BaseFactStmt interface {
	notFactStmtSetT(b bool)
	factStmt()
	stmt()
	inlineFactStmt()
}

func (r *RelationFactStmt) notFactStmtSetT(b bool) { r.isTrue = b }
func (f *FuncPropStmt) notFactStmtSetT(b bool)     { f.IsTrue = b }

type typeVar interface {
	typeVar()
}

func (f TypeVarStr) typeVar()    {}
func (f *TypedTypeVar) typeVar() {}

type fcType interface {
	fcType()
}

func (f FcVarType) fcType()              {}
func (f *FcFnType) fcType()              {}
func (f *FcPropertyType) fcType()        {}
func (f *UndefinedFnType) fcType()       {}
func (f *UndefinedVarType) fcType()      {}
func (f *UndefinedPropertyType) fcType() {}

type fcUndefinedType interface {
	fcUndefinedType()
	fcType()
}

func (f *UndefinedFnType) fcUndefinedType()       {}
func (f *UndefinedVarType) fcUndefinedType()      {}
func (f *UndefinedPropertyType) fcUndefinedType() {}

// type fnRetType interface {
// 	fnRetType()
// }

// func (f fcVarType) fnRetType() {}
// func (f *fcFnType) fnRetType() {}

// type fnRetTypeMemberDecl interface {
// 	fnRetTypeMemberDecl()
// }

// func (f *fcVarDecl) fnRetTypeMemberDecl() {}
// func (f *fcFnDecl) fnRetTypeMemberDecl()  {}

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

func (r *RelationFactStmt) inlineFactStmt()    {}
func (p *FuncPropStmt) inlineFactStmt()        {}
func (p *InlineIfFactStmt) inlineFactStmt()    {}
func (p *InlineForallSubStmt) inlineFactStmt() {}
