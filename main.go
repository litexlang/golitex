// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package main

import (
	"flag"
	"fmt"
	glob "golitex/glob"
	sys "golitex/sys"
	"os"
	"strings"
)

// 可以改变version的value，但是不要该VERSION这个名字，因为其他文件的grep依赖它
const VERSION = "0.1.11-beta"

func main() {
	// Define flags
	helpFlag := flag.Bool("help", false, "Show help message")
	versionFlag := flag.Bool("version", false, "Show version information")
	executeFlag := flag.String("e", "", "Execute the given code")
	fileFlag := flag.String("f", "", "Execute the given file")
	repoFlag := flag.String("r", "", "Execute the given repo")
	latexFlag := flag.String("latex", "", "Compile the given file to latex")

	flag.Parse()

	// Handle flags
	if *helpFlag {
		fmt.Println("Usage: golitex [options]")
		fmt.Println("Options:")
		flag.PrintDefaults()
		fmt.Printf("\nIf no options provided, defaults to: REPL mode\n")
		return
	}

	if *versionFlag {
		fmt.Println("Litex Kernel: golitex " + VERSION)
		return
	}

	// Handle execution flags
	if *executeFlag != "" {
		msg, signal, err := sys.ExecuteCodeAndReturnMessage(*executeFlag)
		msg = strings.TrimSpace(msg)
		fmt.Println(msg)
		if err != nil {
			fmt.Printf("Error: %s\n", err)
		} else {
			msg := sys.RunMainMsg(signal)
			fmt.Println(msg)
		}
		return
	}

	if *fileFlag != "" {
		// Verify file exists
		if _, err := os.Stat(*fileFlag); os.IsNotExist(err) {
			fmt.Printf("Error: File '%s' does not exist\n", *fileFlag)
			os.Exit(1)
		}

		// Process file
		msg, signal, err := sys.RunFile(*fileFlag)
		fmt.Println(msg)
		if err != nil {
			fmt.Printf("Error: %s\n", err)
		} else {
			msg := sys.RunMainMsg(signal)
			fmt.Println(msg)
		}
		return
	}

	if *repoFlag != "" {
		// verify the repo exists
		if _, err := os.Stat(*repoFlag); os.IsNotExist(err) {
			fmt.Printf("Error: Repo '%s' does not exist\n", *repoFlag)
			os.Exit(1)
		}
		// run the repo
		msg, signal, err := sys.RunRepo(*repoFlag)
		fmt.Println(msg)
		if err != nil {
			fmt.Printf("Error: %s\n", err)
			os.Exit(1)
		} else {
			msg := sys.RunMainMsg(signal)
			fmt.Println(msg)
		}
		return
	}

	if *latexFlag != "" {
		msg, signal, err := sys.CompileFileToLatex(*latexFlag)
		if err != nil || signal != glob.SysSignalTrue {
			fmt.Printf("Error: %s\n", err)
			os.Exit(1)
		}
		fmt.Println(msg)
		return
	}

	// If no flags are provided, run REPL
	sys.RunREPLInTerminal()

}
