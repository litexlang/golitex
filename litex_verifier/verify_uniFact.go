package litexverifier

import (
	parser "golitex/litex_parser"
)

func (ver *Verifier) UniFact(stmt *parser.UniFactStmt) (bool, error) {
	// 默认不允许局部的变量名和外部的变量名冲突了。如果你冲突了，那我报错
	for _, param := range stmt.Params {
		ok, err := ver.isDeclared(param)
		if err != nil {
			return false, err
		}
		if ok {
			ver.unknownWithMsg("%s is already declared", param)
			return false, nil
		}
	}

	// 在局部环境声明新变量
	ver.newEnv(ver.env)
	for _, param := range stmt.Params {
		ver.env.Declare(nil, param)
	}

	return false, nil
}
