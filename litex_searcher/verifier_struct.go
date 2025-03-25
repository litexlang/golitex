package litexsearcher

import (
	"fmt"
	env "golitex/litex_env"
)

type VerifierOutput uint8

const (
	verifierTrue VerifierOutput = iota
	verifierUnknown
	verifierError
)

type Verifier struct {
	env         *env.Env
	message     []string
	output      VerifierOutput
	searchRound uint8
}

func (e *Verifier) roundAddOne() {
	e.searchRound++
}

func (e *Verifier) roundMinusOne() {
	e.searchRound--
}

func (e *Verifier) true() bool {
	return e.output == verifierTrue
}

func (e *Verifier) round1() bool {
	return e.searchRound == 1
}

func (e *Verifier) success(format string, args ...any) {
	message := fmt.Sprintf(format, args...) // 使用 fmt.Sprintf 格式化字符串
	e.message = append(e.message, message)
	e.output = verifierTrue
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
	e.message = append(e.message, message)
	e.output = verifierUnknown
}
