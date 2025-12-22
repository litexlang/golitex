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
	pkgMgr "golitex/package_manager"
)

func NoSelfReferenceInPropDef(propName string, facts []FactStmt) error {
	for _, fact := range facts {
		switch asFactStmt := fact.(type) {
		case *SpecFactStmt:
			if asFactStmt.PropName.String() == propName {
				return fmt.Errorf("self reference in prop definition: %s", propName)
			}
		case *OrStmt:
			for _, fact := range asFactStmt.Facts {
				if fact.PropName.String() == propName {
					return fmt.Errorf("self reference in prop definition: %s", propName)
				}
			}
		case *UniFactStmt:
			err := NoSelfReferenceInPropDef(propName, asFactStmt.DomFacts)
			if err != nil {
				return err
			}
			err = NoSelfReferenceInPropDef(propName, asFactStmt.ThenFacts)
			if err != nil {
				return err
			}
		case *UniFactWithIffStmt:
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
		default:
			continue
		}
	}

	return nil
}

func IsNumExprObj_SimplifyIt(obj Obj) Obj {
	numLitExpr, ok, err := MakeObjIntoNumLitExpr(obj)
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

func ParseSourceCodeGetFact(sourceCode string) (FactStmt, error) {
	blocks, err := makeTokenBlocks([]string{sourceCode})
	if err != nil {
		return nil, err
	}

	pkgPathNameMgr := pkgMgr.NewPathNameMgr()
	p := NewTbParser("", pkgPathNameMgr, "")

	return p.factStmt(&blocks[0], UniFactDepth0)
}

// ParseSingleLineFact parses a single line fact statement from a string
// This function is similar to ParseSourceCodeGetObj but for facts
// It parses inline facts that can appear in a single line (like "x $in S", "x = y", etc.)
func ParseSingleLineFact(s string) (FactStmt, error) {
	blocks, err := makeTokenBlocks([]string{s})
	if err != nil {
		return nil, err
	}

	pkgPathNameMgr := pkgMgr.NewPathNameMgr()
	p := NewTbParser("", pkgPathNameMgr, "")

	fact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(&blocks[0], []string{})
	if err != nil {
		return nil, err
	}

	return fact, nil
}

func ParseSourceCodeGetObj(s string) (Obj, error) {
	blocks, err := makeTokenBlocks([]string{s})
	if err != nil {
		return nil, err
	}

	pkgPathNameMgr := pkgMgr.NewPathNameMgr()
	p := NewTbParser("", pkgPathNameMgr, "")

	obj, err := p.Obj(&blocks[0])
	if err != nil {
		return nil, err
	}

	return obj, nil
}
