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
	case *parser.SpecFactStmt:
		return ver.SpecFact(stmt)
	case *parser.CondFactStmt:
		return ver.CondFact(stmt)
	case *parser.UniFactStmt:
		return ver.UniFact(stmt)
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
	env *env.Env
	// Messages    *[]string
	Output      VerifierOutput
	searchRound uint8
}

func NewVerifier(curEnv *env.Env) *Verifier {
	if curEnv == nil {
		return &Verifier{env: env.NewEnv(nil, nil), Output: VerifierUnknown, searchRound: 0}
	} else {
		return &Verifier{env: curEnv, Output: VerifierUnknown, searchRound: 0}
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
	ver.successMsgEnd(stmtString, storedStmtString)
	ver.Output = VerifierTrue
}

func (ver *Verifier) successNoMsg() {
	ver.Output = VerifierTrue
}

func (ver *Verifier) newEnv(parent *env.Env, uniParamsMap *map[string]parser.Fc) {
	newEnv := env.NewEnv(parent, uniParamsMap)
	newEnv.Parent = ver.env
	ver.env = newEnv
}

func (ver *Verifier) parentEnv() error {
	if ver.env.Parent != nil {
		ver.env = ver.env.Parent
		return nil
	} else {
		return fmt.Errorf("parent env does not exist")
	}
}

func (ver *Verifier) unknownWithMsg(format string, args ...any) {
	ver.unknownMsgEnd(format, args...)
	ver.Output = VerifierUnknown
}

func (ver *Verifier) unknownNoMsg() {
	ver.Output = VerifierUnknown
}

func (ver *Verifier) asConFc(fc parser.Fc) parser.Fc {
	// Safe type assertion
	fcAsAtom, ok := fc.(*parser.FcAtom)
	if !ok {
		return nil
	}

	// Early return if it's a package-qualified name
	if fcAsAtom.PkgName != "" {
		return nil
	}

	// Look up in the universal parameter map
	return ver.env.UniParamMap[fcAsAtom.OptName]
}

func (ver *Verifier) isDeclared(fc string) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		ok, err := ver.env.IsDeclared(fc)
		if err != nil {
			return false, err
		}
		if ok {
			return ok, nil
		}
	}
	return false, nil
}
