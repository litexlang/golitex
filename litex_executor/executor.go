package litexexecutor

import (
	"fmt"
	glob "golitex/litex_global"
	parser "golitex/litex_parser"
	verifier "golitex/litex_verifier"
	"strings"
)

func (exec *Executor) TopLevelStmt(stmt *parser.TopStmt) error {
	exec.clearMsgAndOutput()
	return exec.stmt(stmt.Stmt)
}

func (exec *Executor) stmt(stmt parser.Stmt) error {
	var err error = nil

	switch stmt := (stmt).(type) {
	case parser.FactStmt:
		err = exec.factStmt(stmt)
	case *parser.KnowStmt:
		err = exec.knowStmt(stmt)
	case *parser.ClaimProveStmt:
		err = exec.claimProveStmt(stmt)

	default:
		err = fmt.Errorf("unknown statement type: %T", stmt)
	}

	if err != nil {
		return glob.NewErrLink(err, "%s\nexecution error", stmt.String())
	} else {
		return nil
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
	ok, _, err := exec.checkFactStmt(stmt)

	if err != nil {
		return err
	}

	if !ok {
		exec.newMsgEnd(stmt.String() + "\nis unknown")
	} else {
		exec.env.NewFact(stmt)
	}

	return nil
}

func (exec *Executor) checkFactStmt(stmt parser.FactStmt) (bool, *verifier.Verifier, error) {
	curVerifier := verifier.NewVerifier(exec.env)
	ok, err := curVerifier.FactStmt(stmt, verifier.AnyMsg)
	if err != nil {
		return false, curVerifier, err
	}
	return ok, curVerifier, err
}

func (exec *Executor) claimProveStmt(stmt *parser.ClaimProveStmt) error {
	exec.newEnv() // 在子环境中做所有操作，不影响外部世界

	defer exec.deleteEnvAndRetainMsg()

	for _, curStmt := range stmt.Proofs {
		err := exec.stmt(curStmt)
		if err != nil {
			return err
		}
	}

	// TODO 检查claim，并确保claim里的变量都是全局变量。确保了之后，在子环境里检查它后，如果确定对了，那就把这些这些claim释放到大环境里

	localMsgs := exec.getMsgs()
	exec.newMsgAtParent(stmt.String() + "\n" + strings.Join(localMsgs, "\n"))

	return nil
}

func (exec *Executor) GetMsgAsStr0ToEnd() string {
	return strings.Join(exec.env.Msgs, "\n")
}

func (exec *Executor) newMsgAtParent(s string) error {
	if exec.env.Parent == nil {
		return fmt.Errorf("no parent env")
	} else {
		exec.env.Parent.NewMsg(s)
		return nil
	}
}
