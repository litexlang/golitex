package litexpipeline

import (
	env "golitex/litex_env"
	exe "golitex/litex_executor"
	parser "golitex/litex_parser"
	"strings"
)

func ExecuteCodeAndReturnMessage(code string) (string, error) {
	msgOfTopStatements, err := ExecuteCodeAndReturnMessageSlice(code)
	if err != nil {
		return "", err
	}
	ret := strings.Join(msgOfTopStatements, "\n\n\n")
	return ret, nil
}

func ExecuteCodeAndReturnMessageSlice(code string) ([]string, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return nil, err
	}
	env := env.NewEnv(nil, nil, "")
	executor := *exe.NewExecutor(env)

	msgOfTopStatements := []string{}
	for _, topStmt := range topStmtSlice {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			return nil, err
		}
		msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
	}
	// slices.Reverse(msgOfTopStatements)

	return msgOfTopStatements, nil
}
