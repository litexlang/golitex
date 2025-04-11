package litex_ast

func (stmt *SpecFactStmt) GetReverseFact() *SpecFactStmt {
	return NewSpecFactStmt(!stmt.IsTrue, stmt.PropName, stmt.Params)
}
