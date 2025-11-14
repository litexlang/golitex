package litex_pipeline

import (
	"errors"
	glob "golitex/glob"
	litex_to_latex_compiler "golitex/to_latex"
	"os"
	"strings"
)

func CompileFileToLatex(path string) (glob.GlobRet, error) {
	// 需要先确定这个path是以.lit结尾的
	if !strings.HasSuffix(path, glob.LitexFileSuffix) {
		return glob.NewGlobErr("the path is not a .lit file"), errors.New("the path is not a .lit file")
	}

	// repoName := filepath.Dir(path)
	// glob.CurrentTaskDirName = repoName
	content, err := os.ReadFile(path)
	if err != nil {
		return glob.NewGlobErr(err.Error()), err
	}

	return CompileCodeToLatex(string(content))
}

func CompileCodeToLatex(code string) (glob.GlobRet, error) {
	latexStr, err := litex_to_latex_compiler.CompileStmtToLatexString(code)
	if err != nil {
		return glob.NewGlobErr(err.Error()), err
	}

	return glob.NewGlobTrue(latexStr), nil
}
