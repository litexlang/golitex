// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_pipeline

import (
	"bufio"
	"fmt"
	ast "golitex/ast"
	env "golitex/env"
	exe "golitex/exe"
	glob "golitex/glob"
	parser "golitex/parser"
	"os"
	"strings"
)

type REPL struct {
	env           *env.Env
	executor      *exe.Executor
	currentInput  strings.Builder
	inMultiLine   bool
	lastEnvSwitch int
	// history       []string
}

const envCreationIntervalForRepl = 5

func NewREPL() *REPL {
	initialEnv := env.NewEnv(nil)
	return &REPL{
		env:      initialEnv,
		executor: exe.NewExecutor(initialEnv),
	}
}

func (r *REPL) Run() {
	scanner := bufio.NewScanner(os.Stdin)
	fmt.Println("REPL started. Type your commands (exit to quit):")

	for {
		fmt.Print(r.getPrompt())
		if !scanner.Scan() {
			break
		}

		line := scanner.Text()
		if err := r.processLine(line); err != nil {
			fmt.Printf("Error: %v\n", err)
		}
	}

	if err := scanner.Err(); err != nil {
		fmt.Fprintf(os.Stderr, "Error reading input: %v\n", err)
	}
}

func (r *REPL) getPrompt() string {
	if r.inMultiLine {
		return "... "
	}
	return ">>> "
}

func (r *REPL) processLine(line string) error {
	// Handle special commands
	if strings.ToLower(strings.TrimSpace(line)) == "exit" {
		os.Exit(0)
	}

	// Handle multi-line input
	if strings.HasSuffix(line, "\\") {
		r.inMultiLine = true
		r.currentInput.WriteString(strings.TrimSuffix(line, "\\") + "\n")
		return nil
	}

	if r.inMultiLine {
		r.currentInput.WriteString(line + "\n")
		code := r.currentInput.String()
		r.currentInput.Reset()
		r.inMultiLine = false
		return r.executeCode(code)
	}

	return r.executeCode(line)
}

func (r *REPL) executeCode(code string) error {
	code = strings.TrimSpace(code)
	if code == "" {
		return nil
	}

	// Parse and execute the code
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return fmt.Errorf("parse error: %w", err)
	}

	// Execute with environment isolation
	messages, err := r.executeStatements(topStmtSlice)
	if err != nil {
		return err
	}

	// Print results
	for _, msg := range messages {
		fmt.Println(msg)
	}

	return nil
}

func (r *REPL) executeStatements(topStmtSlice []ast.TopStmt) ([]string, error) {
	msgOfTopStatements := []string{}
	curEnv := r.env
	executor := r.executor

	if envCreationIntervalForRepl == 0 {
		// Single environment mode
		for _, topStmt := range topStmtSlice {
			execState, err := executor.TopLevelStmt(&topStmt)
			if err != nil {
				return nil, err
			}
			if execState != glob.ExecState_True {
				return nil, fmt.Errorf("execution failed")
			}
			msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
		}
	} else {
		// Environment isolation mode
		envSwitchThreshold := envCreationIntervalForRepl - 1

		for i, topStmt := range topStmtSlice {
			if i%envCreationIntervalForRepl == envSwitchThreshold {
				curEnv = env.NewEnv(curEnv)
				executor = exe.NewExecutor(curEnv)
				r.lastEnvSwitch = i
			}

			execState, err := executor.TopLevelStmt(&topStmt)
			if err != nil {
				// Rollback to last environment checkpoint
				r.env = env.NewEnv(r.env)
				r.executor = exe.NewExecutor(r.env)
				return nil, fmt.Errorf("at statement %d: %w", i+1, err)
			}
			if execState != glob.ExecState_True {
				return nil, fmt.Errorf("execution failed")
			}
			msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
		}

		// Update the main environment reference
		r.env = curEnv
		r.executor = executor
	}

	return msgOfTopStatements, nil
}

func RunREPL() {
	repl := NewREPL()
	repl.Run()
}
