package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

type VeriRet struct {
	ExecRet                *glob.StmtRetType
	ToCheck                ast.FactStmt
	VerifiedByKnownFact    ast.FactStmt
	VerifiedByBuiltinRules string
}
