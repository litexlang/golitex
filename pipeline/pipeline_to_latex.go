// Copyright Jiachen Shen.
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

package litex_pipeline

import (
	"errors"
	glob "golitex/glob"
	litex_to_latex_compiler "golitex/to_latex"
	"os"
	"strings"
)

func CompileFileToLatex(path string) (*glob.GlobRet, error) {
	// 需要先确定这个path是以.lit结尾的
	if !strings.HasSuffix(path, glob.LitexFileSuffix) {
		return glob.ErrRet("the path is not a .lit file"), errors.New("the path is not a .lit file")
	}

	// repoName := filepath.Dir(path)
	// glob.CurrentTaskDirName = repoName
	content, err := os.ReadFile(path)
	if err != nil {
		return glob.ErrRet(err.Error()), err
	}

	return CompileCodeToLatex(string(content))
}

func CompileCodeToLatex(code string) (*glob.GlobRet, error) {
	latexStr, err := litex_to_latex_compiler.CompileStmtToLatexString(code)
	if err != nil {
		return glob.ErrRet(err.Error()), err
	}

	return glob.NewGlobTrueWithStmt(latexStr), nil
}
