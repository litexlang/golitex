package litexparser

import "fmt"

func (stmt *KnowStmt) String() string {
	return fmt.Sprintf("know %s", stmt.Facts)
}

func (stmt *FuncFactStmt) String() string {
	if stmt.IsTrue {
		return fmt.Sprintf("$%v", stmt.Fc)
	} else {
		return fmt.Sprintf("not $%v", stmt.Fc)
	}
}
