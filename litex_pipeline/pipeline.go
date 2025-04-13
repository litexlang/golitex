package litex_pipeline

import (
	env "golitex/litex_env"
	exe "golitex/litex_executor"
	glob "golitex/litex_global"
	parser "golitex/litex_parser"
	"strings"
)

func ExecuteCodeAndReturnMessage(code string) (string, error) {
	msgOfTopStatements, err := executeCodeAndReturnMessageSlice(code)
	if err != nil {
		return "", err
	}
	ret := strings.Join(msgOfTopStatements, "\n\n\n")
	return ret, nil
}

func executeCodeAndReturnMessageSlice(code string) ([]string, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return nil, err
	}
	curEnv := env.NewEnv(nil, nil, "")
	executor := *exe.NewExecutor(curEnv)

	msgOfTopStatements := []string{}

	if glob.EnvCreationInterval == 0 {
		curEnv := env.NewEnv(nil, nil, "")
		executor := *exe.NewExecutor(curEnv)

		for _, topStmt := range topStmtSlice {
			err := executor.TopLevelStmt(&topStmt)
			if err != nil {
				return nil, err
			}
			msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
		}
	} else {
		envSwitchThreshold := glob.EnvCreationInterval - 1

		for i, topStmt := range topStmtSlice {
			// 意义：如果某一个stmt执行错误，那只污染当前环境，能回到上一个环境，这样用户repl的时候会节约时间
			if i%glob.EnvCreationInterval == envSwitchThreshold {
				curEnv = env.NewEnv(curEnv, curEnv.UniParamMap, curEnv.CurPkg)
				executor = *exe.NewExecutor(curEnv)
			}

			err := executor.TopLevelStmt(&topStmt)
			if err != nil {
				return nil, err
			}
			msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
		}
	}

	return msgOfTopStatements, nil
}
