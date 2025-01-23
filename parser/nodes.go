package parser

import (
	"fmt"
)

type TopStmt interface {
	setPubTrue() error
}

type TypeVarPair struct {
	Var  string
	Type string
}

type Fact interface{}
type ExistFact struct{}

type DefConceptTopStmt struct {
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

func (stmt *DefConceptTopStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type DefPropertyTopStmt struct {
	pub           bool
	Name          string
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	Facts         []Fact
}

func (stmt *DefPropertyTopStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type IfFactTopStmt struct {
	pub bool
	IfStmt
}

func (stmt *IfFactTopStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type IfStmt struct {
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	Facts         []Fact
}

type CalledPropertyTopStmt struct {
	pub bool
	CalledPropertyStmt
}

func (stmt *CalledPropertyTopStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type CalledPropertyStmt struct {
	Name string
	Args []Var
}

type LocalTopStmt struct {
	LocalStmt
}

type LocalStmt struct {
	Statements []TopStmt
}

func (stmt *LocalTopStmt) setPubTrue() error {
	return fmt.Errorf(`local statement is by default private.\n`)
}

type DefFnTopStmt struct {
	pub           bool
	Name          string
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	Facts         []Fact
}

func (stmt *DefFnTopStmt) setPubTrue() error {
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
