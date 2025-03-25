package litexverifier

import (
	"fmt"
	env "golitex/litex_env"
)

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

func (e *Verifier) success(format string, args ...any) {
	message := fmt.Sprintf(format, args...) // 使用 fmt.Sprintf 格式化字符串
	*e.Message = append(*e.Message, message)
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

func (e *Verifier) unknown(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	*e.Message = append(*e.Message, message)
	e.Output = VerifierUnknown
}
