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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package main

import (
	"flag"
	"fmt"
	glob "golitex/glob"
	pipeline "golitex/pipeline"
	"os"
	"path/filepath"
	"strings"
)

// 可以改变version的value，但是不要该VERSION这个名字，因为其他文件的grep依赖它
const VERSION = "0.2.01-beta"

func main() {
	// Define flags
	helpFlag := flag.Bool("help", false, "Show help message")
	versionFlag := flag.Bool("version", false, "Show version information")
	executeFlag := flag.String("e", "", "Execute the given code")
	fileFlag := flag.String("f", "", "Execute the given file")
	repoFlag := flag.String("r", "", "Execute the given repo")
	latexFlag := flag.String("latex", "", "Compile the given file to latex")
	elatexFlag := flag.String("elatex", "", "Compile the given file to latex")
	fmtCodeFlag := flag.String("fmt", "", "Format the given code")
	installFlag := flag.String("install", "", "Install the given package")
	uninstallFlag := flag.String("uninstall", "", "Uninstall the given package")
	listFlag := flag.Bool("list", false, "List all installed packages")
	updateFlag := flag.String("update", "", "Update the given package")

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

	// Handle combined -latex and -e
	if *elatexFlag != "" {
		// 处理转义序列
		ret, err := pipeline.CompileCodeToLatex(glob.RemoveWindowsCarriage(*elatexFlag))
		if err != nil || ret.IsNotTrue() {
			fmt.Printf("Error: %s\n", err)
			os.Exit(1)
		}
		fmt.Println(ret.String())
		return
	}

	// Handle execution flags
	if *executeFlag != "" {
		// Normal execution
		ret := pipeline.RunSourceCode(glob.RemoveWindowsCarriage(*executeFlag), "-e")
		msg := strings.TrimSpace(ret.String())
		fmt.Println(msg)
		return
	}

	if *fileFlag != "" {
		MainFlagFile(*fileFlag)
		return
	}

	if *repoFlag != "" {
		MainFlagFile(filepath.Join(*repoFlag, glob.MainDotLit))
		return
	}

	if *latexFlag != "" {
		ret, err := pipeline.CompileFileToLatex(glob.RemoveWindowsCarriage(*latexFlag))
		if err != nil || ret.IsNotTrue() {
			fmt.Printf("Error: %s\n", err)
			os.Exit(1)
		}
		fmt.Println(ret.String())
		return
	}

	if *fmtCodeFlag != "" {
		ret, err := pipeline.FormatCode(glob.RemoveWindowsCarriage(*fmtCodeFlag))
		if err != nil || ret.IsNotTrue() {
			fmt.Printf("Error: %s\n", err)
			os.Exit(1)
		}
		fmt.Println(ret.String())
		return
	}

	if *installFlag != "" {
		fmt.Printf("Installing package: %s\n", *installFlag)
		return
	}

	if *uninstallFlag != "" {
		fmt.Printf("Uninstalling package: %s\n", *uninstallFlag)
		return
	}

	if *listFlag {
		fmt.Println("Listing all installed packages")
		return
	}

	if *updateFlag != "" {
		fmt.Printf("Updating package: %s\n", *updateFlag)
		return
	}

	// If no flags are provided, run REPL
	pipeline.RunREPL(VERSION)
}

func MainFlagFile(fileFlag string) {
	ret := pipeline.RunFile(glob.RemoveWindowsCarriage(fileFlag))
	fmt.Println(ret.StringWithOptimizedNewline())
}
