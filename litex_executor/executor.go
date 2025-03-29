package litexexecutor

import (
	"fmt"
	parser "golitex/litex_parser"
	verifier "golitex/litex_verifier"
)

func (exec *Executor) TopLevelStmt(stmt *parser.TopStmt) error {
	exec.clear()
	return exec.stmt(stmt.Stmt)
}

func (exec *Executor) stmt(stmt parser.Stmt) error {
	switch stmt := (stmt).(type) {
	case parser.FactStmt:
		return exec.factStmt(stmt)
	case *parser.KnowStmt:
		return exec.knowStmt(stmt)

	default:
		return fmt.Errorf("unknown statement type: %T", stmt)
	}
}

func (exec *Executor) knowStmt(stmt *parser.KnowStmt) error {
	defer exec.newMessage(stmt.String())

	for _, fact := range stmt.Facts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}
	return nil
}

func (exec *Executor) factStmt(stmt parser.FactStmt) error {
	defer exec.newMessage(stmt.String())

	curVerifier := verifier.NewVerifier(exec.env)
	ok, err := curVerifier.FactStmt(stmt)
	if err != nil {
		return err
	}
	exec.readFromVerifier(curVerifier)

	if ok {
		err = exec.env.NewFact(stmt)
		if err != nil {
			return err
		}
	} else {
		if curVerifier.Output == verifier.VerifierUnknown {
			exec.newMessage("is unknown.")
		}
	}

	return nil
}
