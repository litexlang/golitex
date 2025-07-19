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

package litex_to_latex_compiler

import (
	parser "golitex/parser"
	"os"
	"strings"
)

func CompileStmtToLatexString(litexCode string) (string, error) {
	var builder strings.Builder

	builder.WriteString(`\documentclass{article}

\usepackage{amsthm}
\usepackage{amssymb}

\theoremstyle{definition}
\newtheorem{definition}{Definition}
\newtheorem{assumption}{Assumption}

\begin{document}

`)

	stmtSlice, err := parser.ParseSourceCode(litexCode)
	if err != nil {
		return "", err
	}

	latexStr := []string{}
	for _, stmt := range stmtSlice {
		latexStr = append(latexStr, stmt.ToLatexString())
	}

	builder.WriteString(strings.Join(latexStr, "\n\n"))

	builder.WriteString(`

\end{document}`)

	return builder.String(), nil
}

func CompileStmtToLatexString_StoreToFile(litexCode string, fileName string) {
	latexStr, err := CompileStmtToLatexString(litexCode)
	if err != nil {
		panic(err)
	}
	os.WriteFile(fileName, []byte(latexStr), 0644)
}
