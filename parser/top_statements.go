package parser

import "fmt"

type TopStmt interface {
	Stmt
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
	PtyStmt
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
	ConceptFacts  []FactStmt
	VarParams     []VarTypePair
	VarFacts      []FactStmt
	Facts         []FactStmt
}

func (stmt *DefFnTopStmt) setPubTrue() error {
	stmt.pub = true
	return nil
}
