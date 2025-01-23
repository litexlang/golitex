package parser

import (
	"fmt"
)

func (t *PtyStmt) String() string {
	paramsStr := ""
	for _, p := range *t.params {
		paramsStr += fmt.Sprintf("%s", p)
	}

	return fmt.Sprintf("$%s(%s)", t.Name, paramsStr)
}
