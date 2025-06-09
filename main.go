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
// Litex discord server: https://discord.gg/uvrHM7eS

package main

import (
	"flag"
	"fmt"
	glob "golitex/glob"
	sys "golitex/sys"
	"os"
)

func main() {
	// Define flags
	helpFlag := flag.Bool("help", false, "Show help message")
	versionFlag := flag.Bool("version", false, "Show version information")
	executeFlag := flag.String("e", "", "Execute the given code")
	fileFlag := flag.String("f", "", "Execute the given file")

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
		fmt.Println("Litex Processor version beta")
		return
	}

	// Handle execution flags
	if *executeFlag != "" {
		msg, signal, err := sys.ExecuteCodeAndReturnMessage(*executeFlag)
		if err != nil {
			fmt.Printf("Error: %v\n", err)
			// os.Exit(1)
		} else {
			// Output results
			fmt.Println(sys.BetterMsg(msg))
			if signal == glob.SysSignalTrue {
				fmt.Println(glob.REPLSuccessMessage)
			} else if signal == glob.SysSignalFalse {
				fmt.Println(glob.REPLFailedMessage)
			} else {
				fmt.Println(glob.REPLFailedMessage)
			}
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
		if err != nil {
			fmt.Printf("Error: %v\n", err)
			// os.Exit(1)
		} else {
			// Output results
			fmt.Println(sys.BetterMsg(msg))
			if signal == glob.SysSignalTrue {
				fmt.Println(glob.REPLSuccessMessage)
			} else if signal == glob.SysSignalUnknown {
				fmt.Println(glob.REPLFailedMessage)
			} else {
				fmt.Println(glob.REPLFailedMessage)
			}
		}
		return
	}

	// If no flags are provided, run REPL
	sys.RunREPLInTerminal()
}
