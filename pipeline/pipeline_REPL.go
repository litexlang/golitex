package litex_pipeline

import (
	"bufio"
	"fmt"
	exe "golitex/executor"
	glob "golitex/glob"
	"io"
	"os"
	"strconv"
	"strings"
	"time"
)

func RunREPL(version string) {
	// where current dir is
	currDir, err := os.Getwd()
	if err != nil {
		fmt.Println("Error getting current directory:", err)
		return
	}

	envMgr, err := GetBuiltinEnvMgr(currDir)
	if err != nil {
		fmt.Println("Error initializing pipeline env:", err)
		return
	}
	executor := exe.NewExecutor(envMgr.NewEnv())

	reader := bufio.NewReader(os.Stdin)
	writer := os.Stdout

	year := time.Now().Year()

	fmt.Fprintf(writer, "Litex %s (Beta)\nCopyright (C) 2024-%s\nOfficial Website: litexlang.com\nGithub: https://github.com/litexlang/golitex\nEmail: litexlang@outlook.com\nType 'help' for help\n\nNote: This is a beta version. We welcome your testing and feedback!\nHowever, please note that this version is NOT READY FOR PRODUCTION USE.\n\n", version, strconv.Itoa(year))

	for {
		code, err := listenOneStatementFromREPL(reader, writer)
		if err != nil {
			fmt.Fprintf(writer, "[Error] %s\n", err)
			continue
		}

		// Have to trim space because there is \n at the end of code
		if strings.TrimSpace(code) == glob.KeywordExit {
			fmt.Fprintf(writer, "---\nGoodbye! :)\n")
			return
		}

		// ret := ExecuteCodeAndReturnMessageSliceGivenSettings(code, executor)
		ret := RunSourceCodeInExecutor(executor, code, "REPL")
		if ret.IsNotTrue() {
			msgStr := ret.String()
			if msgStr != "" {
				fmt.Fprint(writer, msgStr)
			}
			continue
		}

		msgStr := ret.String()
		if msgStr != "" {
			fmt.Fprint(writer, msgStr)
		}
	}
}

func listenOneStatementFromREPL(reader *bufio.Reader, writer io.Writer) (string, error) {
	var input strings.Builder
	fmt.Fprint(writer, ">>> ")
	currentScopeDepth := 0

	for {
		currentLineStr, err := reader.ReadString('\n')
		if err != nil {
			return "", fmt.Errorf("error reading input: %s", err)
		}

		currentLineStr = glob.RemoveWindowsCarriage(currentLineStr)
		trimmedLine := strings.TrimRight(currentLineStr, " \t\n")

		if currentScopeDepth > 0 {
			if trimmedLine == "" {
				break
			}

			input.WriteString("    ")
			input.WriteString(currentLineStr)

			fmt.Fprint(writer, "... ") // 为下一行准备提示符

		} else {
			input.WriteString(currentLineStr)

			// input 的非空白的最后一位 不是 :
			if trimmedLine == "" || !strings.HasSuffix(trimmedLine, ":") {
				break
			} else {
				currentScopeDepth = 1
				fmt.Fprint(writer, "... ") // 为下一行准备提示符
			}
		}
	}
	return input.String(), nil
}
