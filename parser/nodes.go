package parser

import (
	"fmt"
)

type Stmt interface {
	setPubTrue() error
}

type TypeVarPair struct {
	Var  string
	Type string
}

type Fact interface{}
type ExistFact struct{}

type DefConceptStmt struct {
	pub           bool
	ConceptVar    string
	ConceptName   string
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	ExistFacts    []ExistFact
	Facts         []Fact
}

func (stmt *DefConceptStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type DefPropertyStmt struct {
	pub           bool
	Name          string
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	Facts         []Fact
}

func (stmt *DefPropertyStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type IfFactStmt struct {
	pub bool
	IfFact
}

func (stmt *IfFactStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type IfFact struct {
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	Facts         []Fact
}

type FactTopStmt struct {
	pub bool
	FactStmt
}

func (stmt *FactTopStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type FactStmt struct {
	Name string
	Args []Var
}

type LocalStmt struct {
	Statements []Stmt
}

func (stmt *LocalStmt) setPubTrue() error {
	return fmt.Errorf(`local statement is by default private.\n`)
}

type DefFnStmt struct {
	pub           bool
	Name          string
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	Facts         []Fact
}

func (stmt *DefFnStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type Var interface {
}

type PureVar string

type FnReturnVar struct {
	CalledFn
}

type CalledFn struct {
	Name   string
	Params []Var
}
