// verifier 的方法的命名方式：factType+?UseWhatMemToVerify+?atEnv, 比如 RelaFactSpecAtEnv 就是说 证明 relaFact, 方法是用SpecFact，在当前环境里.
package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	env "golitex/litex_env"
	glob "golitex/litex_global"
)

// 所有verifier的方法里，只有它和switch里的三大函数可能读入anyState
func (ver *Verifier) FactStmt(stmt ast.FactStmt, state VerState) (bool, error) {
	switch stmt := stmt.(type) {
	// 只有这里的三大函数+FcEqual+propProp验证，可能读入anyState；也只有这三个函数，用得到 state,isSpec()，其他函数貌似都用不到？
	case *ast.SpecFactStmt:
		return ver.SpecFact(stmt, state)
	case *ast.CondFactStmt:
		return ver.CondFact(stmt, state)
	case *ast.ConUniFactStmt:
		return ver.UniFact(stmt, state)
	default:
		return false, fmt.Errorf("unexpected")
	}
}

type Verifier struct {
	env *env.Env
}

func NewVerifier(curEnv *env.Env, pkgName string) *Verifier {
	if curEnv == nil {
		return &Verifier{env: env.NewEnv(nil, nil, pkgName)}
	} else {
		return &Verifier{env: curEnv}
	}
}

func (ver *Verifier) successWithMsg(stmtString, storedStmtString string) {
	ver.successMsgEnd(stmtString, storedStmtString)
}

func (ver *Verifier) successNoMsg() {
}

func (ver *Verifier) newEnv(uniParamsMap map[string]ast.Fc) {
	newEnv := env.NewEnv(ver.env, uniParamsMap, ver.env.CurPkg)
	ver.env = newEnv
}

func (ver *Verifier) deleteEnvAndRetainMsg() error {
	if ver.env.Parent != nil {
		for _, msg := range ver.env.Msgs {
			ver.env.Parent.NewMsg(msg)
		}
		ver.env = ver.env.Parent
		return nil
	} else {
		return fmt.Errorf("parent env does not exist")
	}
}

// func (ver *Verifier) unknownWithMsg(format string, args ...any) {
// 	ver.unknownMsgEnd(format, args...)
// }

func (ver *Verifier) asConFc(fc ast.Fc) ast.Fc {
	fcAsAtom, ok := fc.(*ast.FcAtom)
	if !ok {
		return nil
	}

	if fcAsAtom.PkgName != "" {
		return nil
	}

	return ver.env.UniParamMap[fcAsAtom.Value]
}

func (ver *Verifier) newMsgAtParent(s string) error {
	if ver.env.Parent == nil {
		return fmt.Errorf("no parent env")
	} else {
		ver.env.Parent.NewMsg(s)
		return nil
	}
}

func verifyStageStmtErr(next error, stmt ast.Stmt) *glob.ErrLink {
	return glob.NewErrLink(next, "%s\nverify-stage error", stmt.String())
}
