// verifier 的方法的命名方式：factType+?UseWhatMemToVerify+?atEnv, 比如 RelaFactSpecAtEnv 就是说 证明 relaFact, 方法是用SpecFact，在当前环境里.
package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) FactStmt(stmt parser.FactStmt) error {
	verifier.addRound()
	defer verifier.minusRound()

	switch stmt := stmt.(type) {
	case *parser.FuncFactStmt:
		return verifier.FuncFact(stmt)
	case *parser.RelaFactStmt:
		return verifier.RelaFact(stmt)
	case *parser.CondFactStmt:
		return verifier.CondFact(stmt)
	default:
		return nil
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

func (e *Verifier) addRound() {
	e.searchRound++
}

func (e *Verifier) minusRound() {
	e.searchRound--
}

func (e *Verifier) true() bool {
	return e.Output == VerifierTrue
}

func (e *Verifier) round1() bool {
	return e.searchRound == 1
}

func (e *Verifier) successWithMsg(stmtString, storedStmtString string) {
	e.successMsg(stmtString, storedStmtString)
	e.Output = VerifierTrue
}

func (e *Verifier) successNoMsg() {
	e.Output = VerifierTrue
}

func (e *Verifier) newEnv() {
	newEnv := env.NewEnv(nil)
	newEnv.Parent = e.env
	e.env = newEnv
}

func (e *Verifier) deleteEnv() {
	e.env = e.env.Parent
}

func (e *Verifier) unknownWithMsg(format string, args ...any) {
	e.unknownMsg(format, args...)
	e.Output = VerifierUnknown
}

func (e *Verifier) unknownNoMsg() {
	e.Output = VerifierUnknown
}
