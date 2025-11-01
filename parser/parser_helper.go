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
	glob "golitex/glob"
)

func addPkgNameToString(name string) string {
	if glob.CurrentPkg == "" {
		return name
	}
	return fmt.Sprintf("%s%s%s", glob.CurrentPkg, glob.KeySymbolColonColon, name)
}

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
		case *ast.IntensionalSetStmt:
			facts := make([]ast.FactStmt, len(asFactStmt.Facts))
			for i, fact := range asFactStmt.Facts {
				facts[i] = fact
			}

			err := NoSelfReferenceInPropDef(propName, facts)
			if err != nil {
				return err
			}
		default:
			continue
		}
	}

	return nil
}
