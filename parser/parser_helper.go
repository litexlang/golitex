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

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
)

func NoSelfReferenceInPropDef(propName string, facts []ast.FactStmt) error {
	for _, fact := range facts {
		switch asFactStmt := fact.(type) {
		case *ast.SpecFactStmt:
			if asFactStmt.PropName.String() == propName {
				return fmt.Errorf("self reference in prop definition: %s", propName)
			}
		case *ast.OrStmt:
			for _, fact := range asFactStmt.Facts {
				if fact.PropName.String() == propName {
					return fmt.Errorf("self reference in prop definition: %s", propName)
				}
			}
		case *ast.UniFactStmt:
			err := NoSelfReferenceInPropDef(propName, asFactStmt.DomFacts)
			if err != nil {
				return err
			}
			err = NoSelfReferenceInPropDef(propName, asFactStmt.ThenFacts)
			if err != nil {
				return err
			}
		case *ast.UniFactWithIffStmt:
			err := NoSelfReferenceInPropDef(propName, asFactStmt.UniFact.DomFacts)
			if err != nil {
				return err
			}
			err = NoSelfReferenceInPropDef(propName, asFactStmt.UniFact.ThenFacts)
			if err != nil {
				return err
			}
			err = NoSelfReferenceInPropDef(propName, asFactStmt.IffFacts)
			if err != nil {
				return err
			}
		// case *ast.IntensionalSetStmt:
		// 	facts := make([]ast.FactStmt, len(asFactStmt.Facts))
		// 	for i, fact := range asFactStmt.Facts {
		// 		facts[i] = fact
		// 	}

		// 	err := NoSelfReferenceInPropDef(propName, facts)
		// 	if err != nil {
		// 		return err
		// 	}
		default:
			continue
		}
	}

	return nil
}

func IsNumExprObj_SimplifyIt(obj ast.Obj) ast.Obj {
	numLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(obj)
	if err != nil || !ok {
		return nil
	}

	evaluatedStr, evaluated, err := numLitExpr.EvalNumLitExpr()
	if err != nil || !evaluated {
		return nil
	}

	newObj, err := ParseSourceCodeGetObj(evaluatedStr)
	if err != nil {
		return nil
	}

	return newObj
}

func ParseSourceCodeGetFact(sourceCode string) (ast.FactStmt, error) {
	blocks, err := makeTokenBlocks([]string{sourceCode})
	if err != nil {
		return nil, err
	}

	return blocks[0].fact()
}

// ParseSingleLineFact parses a single line fact statement from a string
// This function is similar to ParseSourceCodeGetObj but for facts
// It parses inline facts that can appear in a single line (like "x $in S", "x = y", etc.)
func ParseSingleLineFact(s string) (ast.FactStmt, error) {
	blocks, err := makeTokenBlocks([]string{s})
	if err != nil {
		return nil, err
	}

	fact, err := blocks[0].inline_spec_or_enum_intensional_Equals_fact_skip_terminator()
	if err != nil {
		return nil, err
	}

	return fact, nil
}

func GetParamParentSetFactsFromIntensionalSet(intensionalSet *ast.FnObj) (string, ast.Obj, []ast.FactStmt, error) {
	param, ok := intensionalSet.Params[0].(ast.Atom)
	if !ok {
		return "", nil, nil, fmt.Errorf("expected parameter as atom, got %T", intensionalSet.Params[0])
	}
	paramAsString := string(param)

	parentSet := intensionalSet.Params[1]

	facts := []ast.FactStmt{}
	for i := 2; i < len(intensionalSet.Params); i++ {
		fact, err := ParseSingleLineFact(intensionalSet.Params[i].String())
		if err != nil {
			return "", nil, nil, err
		}
		facts = append(facts, fact)
	}

	return paramAsString, parentSet, facts, nil
}
