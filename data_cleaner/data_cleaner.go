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

package data_cleaner

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	parser "golitex/parser"
	"strings"
)

type CleanData struct {
	Assumptions string
	ClaimData   CleanClaimData
}

func NewCleanData(assumptions string, claimData *CleanClaimData) *CleanData {
	return &CleanData{
		Assumptions: assumptions,
		ClaimData:   *claimData,
	}
}

type CleanClaimData struct {
	ClaimAssumption string
	ClaimResult     string
	Proofs          string
}

func NewCleanClaimData(claimAssumption string, claimResult string, proofs string) *CleanClaimData {
	return &CleanClaimData{
		ClaimAssumption: claimAssumption,
		ClaimResult:     claimResult,
		Proofs:          proofs,
	}
}

func CleanStmtSlice(code string) ([]*CleanData, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return nil, err
	}

	ret := make([]*CleanData, len(topStmtSlice))
	for i, stmt := range topStmtSlice {
		cleanData, err := CleanStmt(stmt)
		if err != nil {
			return nil, err
		}
		ret[i] = cleanData
	}
	return ret, nil
}

func CleanStmt(stmt ast.Stmt) (*CleanData, error) {
	switch topStmt := stmt.(type) {
	case *ast.ClaimProveStmt:
		cleanClaimData, err := cleanClaimProveStmt(topStmt)
		if err != nil {
			return nil, err
		}
		return NewCleanData("", cleanClaimData), nil
	case *ast.ProveStmt:
		return cleanProveStmt(topStmt)
	case *ast.ClaimPropStmt:
		return cleanClaimPropStmt(topStmt)
	default:
		return nil, fmt.Errorf("expect claim statement")
	}
}

func cleanClaimPropStmt(claimPropStmt *ast.ClaimPropStmt) (*CleanData, error) {
	uniFact := ast.NewUniFact(claimPropStmt.Prop.DefHeader.Params, claimPropStmt.Prop.DefHeader.ParamSets, claimPropStmt.Prop.IffFacts, claimPropStmt.Prop.ThenFacts)
	cleanClaimData, err := cleanClaimProveStmt(ast.NewClaimProveStmt(uniFact, claimPropStmt.Proofs))
	if err != nil {
		return nil, err
	}
	return NewCleanData("", cleanClaimData), nil
}

func cleanClaimProveStmt(claimProveStmt *ast.ClaimProveStmt) (*CleanClaimData, error) {
	claimAssumption := ""
	claimResult := ""

	switch asStmt := claimProveStmt.ToCheckFact.(type) {
	case *ast.SpecFactStmt:
		claimResult = asStmt.String()
	case *ast.UniFactStmt:
		claimAssumption = uniFactAssumptionToString(asStmt)
		claimResult = uniFactResultToString(asStmt)
	default:
		return nil, fmt.Errorf("expect spec fact or know fact")
	}

	proofs := make([]string, len(claimProveStmt.Proofs))
	for i := range len(claimProveStmt.Proofs) {
		proofs[i] = (claimProveStmt.Proofs[i].String())
	}
	proofsStr := strings.Join(proofs, "\n")

	return NewCleanClaimData(claimAssumption, claimResult, proofsStr), nil
}

func uniFactAssumptionToString(uniFact *ast.UniFactStmt) string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordForall)
	builder.WriteString(" ")
	builder.WriteString(ast.StrFcSetPairs(uniFact.Params, uniFact.ParamSets))
	if len(uniFact.DomFacts) > 0 {
		builder.WriteString(glob.KeySymbolColon)
		factStrSlice := make([]string, len(uniFact.DomFacts))
		for i := range len(uniFact.DomFacts) {
			factStrSlice[i] = glob.SplitLinesAndAdd4NIndents(uniFact.DomFacts[i].String(), 1)
		}
		builder.WriteString(strings.Join(factStrSlice, "\n"))
	}

	return builder.String()
}

func uniFactResultToString(uniFact *ast.UniFactStmt) string {
	var builder strings.Builder
	factStrSlice := make([]string, len(uniFact.ThenFacts))
	for i := range len(uniFact.ThenFacts) {
		factStrSlice[i] = glob.SplitLinesAndAdd4NIndents(uniFact.ThenFacts[i].String(), 1)
	}
	builder.WriteString(strings.Join(factStrSlice, "\n"))
	return builder.String()
}

func cleanProveStmt(proveStmt *ast.ProveStmt) (*CleanData, error) {
	// 最后一个必须是 claim 形式
	if _, ok := proveStmt.Proof[len(proveStmt.Proof)-1].(*ast.ClaimProveStmt); !ok {
		if _, ok := proveStmt.Proof[len(proveStmt.Proof)-1].(*ast.ClaimPropStmt); !ok {
			return nil, fmt.Errorf("expect claim statement or claim prop statement")
		}
	}

	proofs := make([]string, len(proveStmt.Proof)-1)
	for i := range len(proveStmt.Proof) - 1 {
		proofs[i] = proveStmt.Proof[i].String()
	}
	proofStr := strings.Join(proofs, "\n")

	if _, ok := proveStmt.Proof[len(proveStmt.Proof)-1].(*ast.ClaimProveStmt); ok {
		cleanClaimData, err := cleanClaimProveStmt(proveStmt.Proof[len(proveStmt.Proof)-1].(*ast.ClaimProveStmt))
		if err != nil {
			return nil, err
		}
		return NewCleanData(proofStr, cleanClaimData), nil
	} else {
		claimProp, ok := proveStmt.Proof[len(proveStmt.Proof)-1].(*ast.ClaimPropStmt)
		if !ok {
			return nil, fmt.Errorf("expect claim prop statement")
		}
		cleanClaimPropStmt, err := cleanClaimPropStmt(claimProp)
		if err != nil {
			return nil, err
		}
		return NewCleanData(proofStr, &cleanClaimPropStmt.ClaimData), nil
	}
}
