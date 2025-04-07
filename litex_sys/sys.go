package litex_sys

import (
	pipeline "golitex/litex_pipeline"
	"os"
)

func ExecFileReturnString(path string) (string, error) {
	content, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	return pipeline.ExecuteCodeAndReturnMessage(string(content))
}

func ExecString(code string) (string, error) {
	return pipeline.ExecuteCodeAndReturnMessage(code)
}
