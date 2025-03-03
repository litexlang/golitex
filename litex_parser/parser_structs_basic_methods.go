package litexparser

import "fmt"

func (stmt *KnowStmt) String() string {
	return fmt.Sprintf("know %s", stmt.Facts)
}

func (stmt *FuncFactStmt) String() string {
	return fmt.Sprintf("%s %s", stmt.IsTrue, stmt.Fc)
}
