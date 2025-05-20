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

package main

import (
	"flag"
	"fmt"
	sys "golitex/sys"
	"os"
)

func main() {
	// Define flags
	helpFlag := flag.Bool("help", false, "Show help message")
	versionFlag := flag.Bool("version", false, "Show version information")
	defaultFile := "./examples/comprehensive_examples/syllogism(三段论).lix"

	flag.Parse()

	// Handle flags
	if *helpFlag {
		fmt.Println("Usage: program [options] [filename]")
		fmt.Println("Options:")
		flag.PrintDefaults()
		fmt.Printf("\nIf no filename provided, defaults to: %s\n", defaultFile)
		return
	}

	if *versionFlag {
		fmt.Println("Litex Processor version -1")
		return
	}

	// Get non-flag arguments
	args := flag.Args()
	var filePath string

	if len(args) == 0 {
		filePath = defaultFile
	} else {
		filePath = args[0]
	}

	// Verify file exists
	if _, err := os.Stat(filePath); os.IsNotExist(err) {
		fmt.Printf("Error: File '%s' does not exist\n", filePath)
		os.Exit(1)
	}

	// Process file
	msg, signal, err := sys.RunFile(filePath)
	if err != nil {
		fmt.Printf("Processing error: %v\n", err)
		os.Exit(1)
	}

	// Output results
	fmt.Println("Output:", sys.BetterMsg(msg))
	fmt.Println("Status:", signal)
}
