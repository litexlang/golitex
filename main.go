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
	"bufio"
	"flag"
	"fmt"
	glob "golitex/glob"
	package_manager "golitex/package_manager"
	pipeline "golitex/pipeline"
	"os"
	"path/filepath"
	"sort"
	"strconv"
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
	tutorialFlag := flag.Bool("tutorial", false, "Start interactive tutorial for keywords")

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
		pkgMgr := package_manager.NewEmptyPkgMgr()

		// ret := pipeline.RunSourceCode(glob.RemoveWindowsCarriage(*executeFlag), "-e")
		_, ret := pipeline.RunCodeInPkgMgr(glob.RemoveWindowsCarriage(*executeFlag), pkgMgr, false)
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

	if *tutorialFlag {
		RunTutorial()
		return
	}

	// If no flags are provided, run REPL
	pipeline.RunREPL(VERSION)
}

func MainFlagFile(fileFlag string) {
	relativeFilePath := glob.RemoveWindowsCarriage(fileFlag)

	// 获取当前工作目录
	workingDir, err := os.Getwd()
	if err != nil {
		fmt.Printf("Error: failed to get current working directory: %v\n", err)
		return
	}

	// 获取相对于当前工作目录的相对路径
	absFilePath := filepath.Join(workingDir, relativeFilePath)

	pkgMgr := package_manager.NewEmptyPkgMgr()

	_, ret := pipeline.RunFileInPkgMgr(absFilePath, "", pkgMgr, false)
	fmt.Println(ret.StringWithOptimizedNewline())
}

func RunTutorial() {
	reader := bufio.NewReader(os.Stdin)

	// Get all keywords from KeywordHelpMap and sort them
	keywords := make([]string, 0, len(glob.KeywordHelpMap))
	for keyword := range glob.KeywordHelpMap {
		keywords = append(keywords, keyword)
	}
	sort.Strings(keywords)

	for {
		fmt.Println("\n=== Litex Keyword Tutorial ===")
		fmt.Println("Available keywords:")
		fmt.Println()

		// Display keywords in a numbered list
		for i, keyword := range keywords {
			helpMsg := glob.KeywordHelpMap[keyword]
			displayMsg := keyword
			if helpMsg != "" {
				displayMsg = fmt.Sprintf("%s - %s", keyword, helpMsg)
			}
			fmt.Printf("%3d. %s\n", i+1, displayMsg)
		}

		fmt.Println()
		fmt.Print("Enter keyword number (or 'q' to quit): ")

		input, err := reader.ReadString('\n')
		if err != nil {
			fmt.Printf("Error reading input: %s\n", err)
			return
		}

		input = strings.TrimSpace(input)

		// Check if user wants to quit
		if input == "exit" {
			fmt.Println("\nGoodbye!")
			return
		}

		// Parse number
		num, err := strconv.Atoi(input)
		if err != nil {
			fmt.Printf("Invalid input. Please enter a number between 1 and %d, or 'q' to quit.\n", len(keywords))
			continue
		}

		if num < 1 || num > len(keywords) {
			fmt.Printf("Number out of range. Please enter a number between 1 and %d.\n", len(keywords))
			continue
		}

		// Display detailed information about the selected keyword
		selectedKeyword := keywords[num-1]
		helpMsg := glob.KeywordHelpMap[selectedKeyword]

		fmt.Println()
		fmt.Println("=" + strings.Repeat("=", 50))
		fmt.Printf("Keyword: %s\n", selectedKeyword)
		fmt.Println("=" + strings.Repeat("=", 50))

		if helpMsg == "" {
			fmt.Println("No detailed explanation available for this keyword yet.")
			fmt.Println("(Help message is empty in KeywordHelpMap)")
		} else {
			fmt.Println(helpMsg)
		}

		fmt.Println()
		fmt.Print("Press Enter to continue...")
		reader.ReadString('\n')
	}
}
