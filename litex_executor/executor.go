package litexexecutor

import (
	"fmt"
	parser "golitex/litex_parser"
	verifier "golitex/litex_verifier"
	"slices"
	"strings"
)

func (exec *Executor) TopLevelStmt(stmt *parser.TopStmt) error {
	exec.clearMsgAndOutput()
	return exec.stmt(stmt.Stmt)
}

func (exec *Executor) stmt(stmt parser.Stmt) error {
	switch stmt := (stmt).(type) {
	case parser.FactStmt:
		return exec.factStmt(stmt)
	case *parser.KnowStmt:
		return exec.knowStmt(stmt)
	case *parser.ClaimProveStmt:
		return exec.claimProveStmt(stmt)

	default:
		return fmt.Errorf("unknown statement type: %T", stmt)
	}
}

func (exec *Executor) knowStmt(stmt *parser.KnowStmt) error {
	for _, fact := range stmt.Facts {
		err := exec.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	exec.newMsgEnd(stmt.String())
	return nil
}

func (exec *Executor) factStmt(stmt parser.FactStmt) error {
	ok, curVerifier, err := exec.checkFactStmt(stmt)

	if err != nil {
		return err
	}

	if ok {
		slices.Reverse(*curVerifier.Messages) // TODO 需要吗？
		exec.newMsgEnd(stmt.String() + "\n" + curVerifier.GetMsgAsStr())
		err = exec.env.NewFact(stmt)
		if err != nil {
			return err
		}
	} else {
		if !ok {
			exec.newMsgEnd(stmt.String() + "\nis unknown")
		}
	}

	return nil
}

func (exec *Executor) checkFactStmt(stmt parser.FactStmt) (bool, *verifier.Verifier, error) {
	curVerifier := verifier.NewVerifier(exec.env)
	ok, err := curVerifier.FactStmt(stmt)
	if err != nil {
		return false, curVerifier, err
	}
	return ok, curVerifier, err
}

func (exec *Executor) claimProveStmt(stmt *parser.ClaimProveStmt) error {
	exec.newEnv() // 在子环境中做所有操作，不影响外部世界

	defer exec.deleteEnv()

	for _, curStmt := range stmt.Proofs {
		err := exec.stmt(curStmt)
		if err != nil {
			return err
		}
	}

	// TODO 检查claim，并确保claim里的变量都是全局变量。确保了之后，在子环境里检查它后，如果确定对了，那就把这些这些claim释放到大环境里

	localMsgs := exec.getMsgs()
	exec.env.Parent.NewMsg(stmt.String() + "\n" + strings.Join(localMsgs, "\n"))

	return nil
}
