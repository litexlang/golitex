// verifier 的方法的命名方式：factType+?UseWhatMemToVerify+?atEnv, 比如 RelaFactSpecAtEnv 就是说 证明 relaFact, 方法是用SpecFact，在当前环境里.
package litexverifier

import (
	"fmt"
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) FactStmt(stmt parser.FactStmt) error {
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

func (e *Verifier) newMessage(format string, args ...interface{}) {
	msg := fmt.Sprintf(format, args...)
	*e.Message = append(*e.Message, msg)
	// *e.Message = append([]string{msg}, *e.Message...) // 新消息插入到最前面
}

func (e *Verifier) roundAddOne() {
	e.searchRound++
}

func (e *Verifier) roundMinusOne() {
	e.searchRound--
}

func (e *Verifier) true() bool {
	return e.Output == VerifierTrue
}

func (e *Verifier) round1() bool {
	return e.searchRound == 1
}

func (e *Verifier) success(stmtString, storedStmtString string) {
	message := fmt.Sprintf("%v\nis true, verified by\n%v", stmtString, storedStmtString)
	*e.Message = append(*e.Message, message)
	e.Output = VerifierTrue
}

// func (e *Verifier) success(format string, args ...any) {
// 	message := fmt.Sprintf(format, args...) // 使用 fmt.Sprintf 格式化字符串
// 	// *e.Message = append([]string{message}, *e.Message...) // 新消息插入到最前面
// 	*e.Message = append(*e.Message, message)
// 	e.Output = VerifierTrue
// }

func (e *Verifier) newEnv() {
	newEnv := env.NewEnv(nil)
	newEnv.Parent = e.env
	e.env = newEnv
}

func (e *Verifier) deleteEnv() {
	e.env = e.env.Parent
}

func (e *Verifier) unknown(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	// *e.Message = append([]string{message}, *e.Message...) // 新消息插入到最前面
	*e.Message = append(*e.Message, message)
	e.Output = VerifierUnknown
}
