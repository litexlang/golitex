package litex_pipeline

import (
	"bufio"
	"fmt"
	glob "golitex/glob"
	"io"
	"os"
	"strconv"
	"strings"
	"time"
)

func RunREPL(version string) {
	executor, err := InitPipelineExecutor()
	if err != nil {
		fmt.Println("Error initializing pipeline:", err)
		return
	}

	reader := bufio.NewReader(os.Stdin)
	writer := os.Stdout

	year := time.Now().Year()

	fmt.Fprintf(writer, "Litex %s Copyright (C) 2024-%s Official Website: litexlang.com Github: https://github.com/litexlang/golitex Type 'help' for help\nNOT READY FOR PRODUCTION USE\n", version, strconv.Itoa(year))

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
		ret := RunSourceCodeInExecutor(executor, code)
		if ret.IsNotTrue() {
			msgStr := ret.String()
			if msgStr != "" {
				fmt.Fprint(writer, msgStr)
			}
			fmt.Fprintf(writer, glob.REPLFailedMessage)
			continue
		}

		msgStr := ret.String()
		if msgStr != "" {
			fmt.Fprint(writer, msgStr)
		}
		fmt.Fprintf(writer, glob.REPLSuccessMessage)
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
