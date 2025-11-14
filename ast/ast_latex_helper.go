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

package litex_ast

import (
	"fmt"
	"strings"
)

func ShouldInSingleLineAsLatexString(strSlice []string) bool {
	totalLength := 0
	for _, s := range strSlice {
		totalLength += len(s)
	}
	return totalLength < 80
}

func toLatexString(s string) string {
	return fmt.Sprintf("$%s$", strings.ReplaceAll(s, "_", "\\_"))
}

func strFcSetPairsLatexString(objs []string, objSets []Obj) string {
	pairStrSlice := make([]string, len(objs))
	for i := range len(objs) {
		pairStrSlice[i] = fmt.Sprintf("%s $\\in$ %s", toLatexString(objs[i]), objSets[i].ToLatexString())
	}
	return strings.Join(pairStrSlice, ", ")
}

func (head DefHeader) ToLatexString() string {
	return fmt.Sprintf("$%s$", strings.ReplaceAll(head.String(), "_", "\\_"))
}

func (head DefHeader) NameWithParamsLatexString() string {
	var builder strings.Builder
	builder.WriteString(string(head.Name))
	builder.WriteString("(")
	builder.WriteString(strings.Join(head.Params, ", "))
	builder.WriteString(")")
	return fmt.Sprintf("$%s$", strings.ReplaceAll(builder.String(), "_", "\\_"))
}

func (s FactStmtSlice) factStmtSliceToLatexStringSlice() []string {
	factStrSlice := make([]string, len(s))
	for i := range len(s) {
		factStrSlice[i] = s[i].ToLatexString()
	}
	return factStrSlice
}

func paramInParamSetInFactLatexStringSlice(paramNames []string, paramSets []Obj) []string {
	strSlice := make([]string, len(paramSets))
	for i, paramSet := range paramSets {
		strSlice[i] = fmt.Sprintf("%s $\\in$ %s", toLatexString(paramNames[i]), paramSet.ToLatexString())
	}
	return strSlice
}

func propNameParamsLatexString(propName FcAtom, params []Obj) string {
	var builder strings.Builder
	builder.WriteString(propName.String())
	builder.WriteString("(")
	paramStrSlice := make([]string, len(params))
	for i := range len(params) {
		paramStrSlice[i] = params[i].ToLatexString()
	}
	builder.WriteString(strings.Join(paramStrSlice, ", "))
	builder.WriteString(")")
	return builder.String()
}

func fcParamsLatexString(params []Obj) string {
	paramStrSlice := make([]string, len(params))
	for i := range len(params) {
		paramStrSlice[i] = params[i].ToLatexString()
	}
	return strings.Join(paramStrSlice, ", ")
}

func (s ObjSlice) fcSliceToLatexStringSlice() []string {
	fcStrSlice := make([]string, len(s))
	for i := range len(s) {
		fcStrSlice[i] = s[i].ToLatexString()
	}
	return fcStrSlice
}
