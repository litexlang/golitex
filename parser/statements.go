package parser

import (
	"fmt"
	"golitex/symbol"
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

type OptFactStmt struct {
	pub bool
	OptFact
}

func (stmt *OptFactStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type OptFact struct {
	Name string
	Args []symbol.Symbol
}

type LocalStmt struct {
	Statements []Stmt
}

func (stmt *LocalStmt) setPubTrue() error {
	return fmt.Errorf(`Local statement is by default private.`)
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
