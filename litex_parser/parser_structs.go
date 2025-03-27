package litexparser

type TopStmt struct {
	Stmt  Stmt
	IsPub bool
}

type DefObjStmt struct {
	Objs  []string
	Facts []FactStmt
}

type DefInterfaceStmt struct {
}

type DefTypeStmt struct {
}

type DefConcreteNormalPropStmt struct {
	DefHeader      ConcreteDefHeader
	ParamCondFacts []FactStmt
	ThenFacts      []FactStmt
}

type DefConcreteExistPropStmt struct {
	DefHeader      ConcreteDefHeader
	ExistFc        []string // 只允许是存在函数和obj，不能是prop
	ExistFcTypes   []FcAtom
	ParamCondFacts []FactStmt
	ThenFacts      []FactStmt
}

type DefConcreteFnStmt struct {
	DefHeader      ConcreteDefHeader
	retType        FcAtom
	ParamCondFacts []FactStmt
	ThenFacts      []FactStmt
}

type ConcreteForallStmt struct {
	Params         []string
	ParamTypes     []Fc // 注意到函数的返回值也可以是集合，所以这里是Fc，而不是string
	ParamCondFacts []FactStmt
	ThenFacts      []SpecFactStmt
}

type GenericForallStmt struct {
	TypeParams     []string
	TypeInterfaces []FcAtom
	Params         []string
	ParamTypes     []Fc
	ParamCondFacts []FactStmt
	ThenFacts      []SpecFactStmt
}

// 这里不需要分Concrete FuncFact, Generic FuncFact. 因为FuncFact的基本form都是下面这个样子。你到底是Concrete还是Generic取决于外部条件而不是它自己：外部条件包括：forall里的Generic，fn或prop的Generic
type FuncFactStmt struct {
	IsTrue bool
	Opt    FcAtom
	Params []Fc
}

type RelaFactStmt struct {
	IsTrue bool
	Opt    FcAtom
	Params []Fc
}

type ClaimProveByContradictStmt struct {
	toCheck []FactStmt
	proof   []Stmt
}

type ClaimProveStmt struct {
	toCheck []FactStmt
	proof   []Stmt
}

type KnowStmt struct {
	Facts []FactStmt
}

type HaveStmt struct {
	propStmt SpecFactStmt
	member   []string
}

// syntax sugar for defining spec prop + claim forall true
type AxiomStmt struct {
	decl DefPropStmt
}

// syntax sugar for defining spec prop + claim forall true + prove it
type ThmStmt struct {
	decl  DefPropStmt
	proof []Stmt
}

type CondFactStmt struct {
	CondFacts []FactStmt
	ThenFacts []SpecFactStmt
}

/*
Data structures below are not statement nodes.
*/

// type TypeConceptStr string

type FcFnDecl struct {
	Name   string
	Params []string
}

type ConcreteDefHeader struct {
	Name       string
	Params     []string
	TypeParams []FcAtom
}

// type FcObjTypeStrValue string
// type FcObjTypeFuncValue struct {
// 	Name      string
// 	ObjParams []Fc
// }
