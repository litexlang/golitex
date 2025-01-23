package parser

import "fmt"

type TopStmt interface {
	setPubTrue() error
}

type DefConceptTopStmt struct {
	pub bool
	DefConceptStmt
}

func (stmt *DefConceptTopStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type DefPropertyTopStmt struct {
	pub bool
	DefPropertyStmt
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

type CalledPropertyTopStmt struct {
	pub bool
	CalledPropertyStmt
}

func (stmt *CalledPropertyTopStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}

type LocalTopStmt struct {
	LocalStmt
}

func (stmt *LocalTopStmt) setPubTrue() error {
	return fmt.Errorf(`local statement is by default private.\n`)
}

type DefFnTopStmt struct {
	pub           bool
	Name          string
	ConceptParams []VarTypePair
	ConceptFacts  []Fact
	VarParams     []VarTypePair
	VarFacts      []Fact
	Facts         []Fact
}

func (stmt *DefFnTopStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}
