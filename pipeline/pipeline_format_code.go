package litex_pipeline

import (
	"fmt"
	glob "golitex/glob"
	parser "golitex/parser"
	"os"
	"strings"
)

func FormatCode(path string) (string, glob.SysSignal, error) {
	content, err := os.ReadFile(path)
	if err != nil {
		return fmt.Sprintf("failed to read file %s: %s", path, err.Error()), glob.SysSignalSystemError, err
	}

	topStmtSlice, err := parser.ParseSourceCode(string(content))
	if err != nil {
		return "", glob.SysSignalParseError, err
	}

	stmtStrSlice := []string{}
	for _, stmt := range topStmtSlice {
		stmtStrSlice = append(stmtStrSlice, stmt.String())
	}

	// 把 code 写到 path 里
	err = os.WriteFile(path, []byte(glob.AddWindowsCarriageReturn(strings.Join(stmtStrSlice, "\n\n"))), 0644)
	if err != nil {
		return fmt.Sprintf("failed to write file %s: %s", path, err.Error()), glob.SysSignalSystemError, err
	}
	return fmt.Sprintf("formatted code written to %s", path), glob.SysSignalTrue, nil
}
