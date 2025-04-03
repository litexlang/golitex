// verifier 的方法的命名方式：factType+?UseWhatMemToVerify+?atEnv, 比如 RelaFactSpecAtEnv 就是说 证明 relaFact, 方法是用SpecFact，在当前环境里.
package litexverifier

import (
	"fmt"
	env "golitex/litex_env"
	glob "golitex/litex_global"
	parser "golitex/litex_parser"
)

// 所有verifier的方法里，只有它和switch里的三大函数可能读入anyState
func (ver *Verifier) FactStmt(stmt parser.FactStmt, state VerState) (bool, error) {
	ver.addRound()
	defer ver.minusRound()

	switch stmt := stmt.(type) {
	// 只有这里的三大函数+FcEqual+propProp验证，可能读入anyState；也只有这三个函数，用得到 state,isSpec()，其他函数貌似都用不到？
	case *parser.SpecFactStmt:
		return ver.SpecFact(stmt, state)
	case *parser.CondFactStmt:
		return ver.CondFact(stmt, state)
	case *parser.UniFactStmt:
		return ver.UniFact(stmt, state)
	default:
		return false, fmt.Errorf("unexpected")
	}
}

type Verifier struct {
	env         *env.Env
	searchRound uint8
}

func NewVerifier(curEnv *env.Env) *Verifier {
	if curEnv == nil {
		return &Verifier{env: env.NewEnv(nil, nil), searchRound: 0}
	} else {
		return &Verifier{env: curEnv, searchRound: 0}
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
}

func (ver *Verifier) successNoMsg() {
}

func (ver *Verifier) newEnv(uniParamsMap map[string]parser.Fc) {
	newEnv := env.NewEnv(ver.env, uniParamsMap)
	// newEnv.Parent = ver.env
	ver.env = newEnv
}

func (ver *Verifier) deleteEnv() error {
	if ver.env.Parent != nil {
		ver.env = ver.env.Parent
		return nil
	} else {
		return fmt.Errorf("parent env does not exist")
	}
}

func (ver *Verifier) unknownWithMsg(format string, args ...any) {
	ver.unknownMsgEnd(format, args...)
	// ver.Output = VerifierUnknown
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

func (ver *Verifier) newMsgAtParent(s string) error {
	if ver.env.Parent == nil {
		return fmt.Errorf("no parent env")
	} else {
		ver.env.Parent.NewMsg(s)
		return nil
	}
}

func verifyStageStmtErr(next error, stmt parser.Stmt) *glob.ErrLink {
	return glob.NewErrLink(next, "%s\nverify-stage error", stmt.String())
}
