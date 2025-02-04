package parser

type Fc interface {
	fc()
	String() string
}

func (fc *typedFc) fc()           {}
func (f *calledFcFnRetValue) fc() {}
func (f FcStr) fc()               {}
func (f *FcExpr) fc()             {}

type Stmt interface {
	stmt()
}

func (stmt *defVarStmt) stmt()     {}
func (c *defConceptStmt) stmt()    {}
func (f *defTypeStmt) stmt()       {}
func (c *defPropertyStmt) stmt()   {}
func (f *defFnStmt) stmt()         {}
func (l *localStmt) stmt()         {}
func (l *forallStmt) stmt()        {}
func (r *relationFactStmt) stmt()  {}
func (p *funcPtyStmt) stmt()       {}
func (f *claimStmt) stmt()         {}
func (f *defuseStmt) stmt()        {}
func (f *knowStmt) stmt()          {}
func (s *defExistStmt) stmt()      {}
func (s *haveStmt) stmt()          {}
func (s *defMemberStmt) stmt()     {}
func (s *defTypeMemberStmt) stmt() {}

type factStmt interface {
	factStmt()
	stmt()
}

func (l *forallStmt) factStmt()       {}
func (r *relationFactStmt) factStmt() {}
func (p *funcPtyStmt) factStmt()      {}

type notFactStmt interface {
	notFactStmtSetT(b bool)
	factStmt()
	stmt()
}

func (r *relationFactStmt) notFactStmtSetT(b bool) { r.isTrue = b }
func (f *funcPtyStmt) notFactStmtSetT(b bool)      { f.isTrue = b }

type typeVar interface {
	typeVar()
}

func (f typeVarStr) typeVar()    {}
func (f *typedTypeVar) typeVar() {}

type fcType interface {
	fcType()
}

func (f fcVarType) fcType()     {}
func (f *fcFnType) fcType()     {}
func (f *propertyType) fcType() {}

type fnRetType interface {
	fnRetType()
}

func (f fcVarType) fnRetType() {}
func (f *fcFnType) fnRetType() {}

type fnRetTypeMemberDecl interface {
	fnRetTypeMemberDecl()
}

func (f *fcVarDecl) fnRetTypeMemberDecl() {}
func (f *fcFnDecl) fnRetTypeMemberDecl()  {}

type fcDecl interface {
	fcDecl()
}

func (f *fcVarDecl) fcDecl()    {}
func (f *fcFnDecl) fcDecl()     {}
func (f *propertyDecl) fcDecl() {}
