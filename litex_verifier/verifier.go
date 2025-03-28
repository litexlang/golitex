// verifier 的方法的命名方式：factType+?UseWhatMemToVerify+?atEnv, 比如 RelaFactSpecAtEnv 就是说 证明 relaFact, 方法是用SpecFact，在当前环境里.
package litexverifier

import (
	"fmt"
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (ver *Verifier) FactStmt(stmt parser.FactStmt) (bool, error) {
	ver.addRound()
	defer ver.minusRound()

	switch stmt := stmt.(type) {
	case *parser.FuncFactStmt:
		return ver.FuncFact(stmt)
	case *parser.RelaFactStmt:
		return ver.RelaFact(stmt)
	case *parser.CondFactStmt:
		return ver.CondFact(stmt)
	default:
		return false, fmt.Errorf("unexpected")
	}
}

type VerifierOutput uint8

const (
	VerifierTrue VerifierOutput = iota
	VerifierUnknown
	VerifierError
)

type Verifier struct {
	env         *env.Env
	Message     *[]string
	Output      VerifierOutput
	searchRound uint8
}

func NewVerifier(curEnv *env.Env) *Verifier {
	if curEnv == nil {
		return &Verifier{env: env.NewEnv(nil), Message: &[]string{}, Output: VerifierUnknown, searchRound: 0}
	} else {
		return &Verifier{env: curEnv, Message: &[]string{}, Output: VerifierUnknown, searchRound: 0}
	}
}

func (ver *Verifier) addRound() {
	ver.searchRound++
}

func (ver *Verifier) minusRound() {
	ver.searchRound--
}

func (ver *Verifier) round1() bool {
	return ver.searchRound == 1
}

func (ver *Verifier) successWithMsg(stmtString, storedStmtString string) {
	ver.successMsg(stmtString, storedStmtString)
	ver.Output = VerifierTrue
}

func (ver *Verifier) successNoMsg() {
	ver.Output = VerifierTrue
}

func (ver *Verifier) newEnv() {
	newEnv := env.NewEnv(nil)
	newEnv.Parent = ver.env
	ver.env = newEnv
}

func (ver *Verifier) deleteEnv() {
	ver.env = ver.env.Parent
}

func (ver *Verifier) unknownWithMsg(format string, args ...any) {
	ver.unknownMsg(format, args...)
	ver.Output = VerifierUnknown
}

func (ver *Verifier) unknownNoMsg() {
	ver.Output = VerifierUnknown
}
