// // Copyright 2024 Jiachen Shen.
// //
// // Licensed under the Apache License, Version 2.0 (the "License");
// // you may not use this file except in compliance with the License.
// // You may obtain a copy of the License at
// //
// //     http://www.apache.org/licenses/LICENSE-2.0
// //
// // Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// // Litex email: <litexlang@outlook.com>
// // Litex website: https://litexlang.com
// // Litex github repository: https://github.com/litexlang/golitex
// // Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	"errors"
	ast "golitex/ast"
	glob "golitex/glob"
)

// import (
// 	"errors"
// 	"fmt"
// 	ast "golitex/ast"
// 	cmp "golitex/cmp"
// 	glob "golitex/glob"
// )

func (s SpecFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]ast.SpecFactStmt, glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.NewGlobTrue("")
	case ast.FalsePure:
		return s.NotPureFacts, glob.NewGlobTrue("")
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.NewGlobTrue("")
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.NewGlobTrue("")
	default:
		return nil, glob.ErrRet(errors.New("invalid spec fact type"))
	}
}

func (s SpecFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]ast.SpecFactStmt, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactMem) newFact(stmt *ast.SpecFactStmt) glob.GlobRet {
	// 要考虑pkgName和propName是否存在
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return ret
	}

	if _, ok := sameEnumFacts[string(stmt.PropName)]; !ok {
		sameEnumFacts[string(stmt.PropName)] = []ast.SpecFactStmt{}
	}
	sameEnumFacts[string(stmt.PropName)] = append(sameEnumFacts[string(stmt.PropName)], *stmt)
	return glob.NewGlobTrue("")
}

func (s SpecFactInLogicExprMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]KnownSpecFact_InLogicExpr, glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.NewGlobTrue("")
	case ast.FalsePure:
		return s.NotPureFacts, glob.NewGlobTrue("")
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.NewGlobTrue("")
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.NewGlobTrue("")
	default:
		return nil, glob.ErrRet(errors.New("invalid spec fact type"))
	}
}

func (s SpecFactInLogicExprMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact_InLogicExpr, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactInLogicExprMem) newFact(logicExpr *ast.OrStmt) glob.GlobRet {
	for i, fact := range logicExpr.Facts {
		sameEnumFacts, ret := s.getSameEnumFacts(fact)
		if ret.IsErr() {
			return ret
		}

		if _, ok := sameEnumFacts[string(fact.PropName)]; !ok {
			sameEnumFacts[string(fact.PropName)] = []KnownSpecFact_InLogicExpr{}
		}
		sameEnumFacts[string(fact.PropName)] = append(sameEnumFacts[string(fact.PropName)], *NewKnownSpecFact_InLogicExpr(fact, i, logicExpr))
	}

	return glob.NewGlobTrue("")
}

func (s SpecFactInUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]KnownSpecFact_InUniFact, glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.NewGlobTrue("")
	case ast.FalsePure:
		return s.NotPureFacts, glob.NewGlobTrue("")
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.NewGlobTrue("")
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.NewGlobTrue("")
	default:
		return nil, glob.ErrRet(errors.New("invalid spec fact type"))
	}
}

func (s SpecFactInUniFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact_InUniFact, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactInUniFactMem) newFact(stmtAsSpecFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) glob.GlobRet {
	sameEnumFacts, ret := s.getSameEnumFacts(stmtAsSpecFact)
	if ret.IsErr() {
		return ret
	}

	if _, ok := sameEnumFacts[string(stmtAsSpecFact.PropName)]; !ok {
		sameEnumFacts[string(stmtAsSpecFact.PropName)] = []KnownSpecFact_InUniFact{}
	}
	sameEnumFacts[string(stmtAsSpecFact.PropName)] = append(sameEnumFacts[string(stmtAsSpecFact.PropName)], KnownSpecFact_InUniFact{stmtAsSpecFact, uniFact})

	return glob.NewGlobTrue("")
}

func (s SpecFact_InLogicExpr_InUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]SpecFact_InLogicExpr_InUniFact, glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.NewGlobTrue("")
	case ast.FalsePure:
		return s.NotPureFacts, glob.NewGlobTrue("")
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.NewGlobTrue("")
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.NewGlobTrue("")
	default:
		return nil, glob.ErrRet(errors.New("invalid spec fact type"))
	}
}

func (s SpecFact_InLogicExpr_InUniFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]SpecFact_InLogicExpr_InUniFact, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFact_InLogicExpr_InUniFactMem) NewFact(uniStmt *ast.UniFactStmt, logicExpr *ast.OrStmt) glob.GlobRet {
	for i, fact := range logicExpr.Facts {
		sameEnumFacts, ret := s.getSameEnumFacts(fact)
		if ret.IsErr() {
			return ret
		}

		if _, ok := sameEnumFacts[string(fact.PropName)]; !ok {
			sameEnumFacts[string(fact.PropName)] = []SpecFact_InLogicExpr_InUniFact{}
		}
		sameEnumFacts[string(fact.PropName)] = append(sameEnumFacts[string(fact.PropName)], *NewSpecFact_InLogicExpr_InUniFact(fact, uniStmt, i, logicExpr))
	}

	return glob.NewGlobTrue("")
}

// func (e *Env) GetSpecFactMem() (*SpecFactMem, bool) {
// 	return &e.KnownFactsStruct.SpecFactMem, true
// }

// func (e *Env) GetSpecFactInLogicExprMem() (*SpecFactInLogicExprMem, bool) {
// 	return &e.KnownFactsStruct.SpecFactInLogicExprMem, true
// }

// func (e *Env) GetSpecFactInUniFactMem() (*SpecFactInUniFactMem, bool) {
// 	return &e.KnownFactsStruct.SpecFactInUniFactMem, true
// }

// func (e *Env) GetSpecFact_InLogicExpr_InUniFactMem() (*SpecFact_InLogicExpr_InUniFactMem, bool) {
// 	return &e.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem, true
// }

// func (e *Env) IsFnDeclared(obj ast.Atom) (*FnInFnTMemItem, bool) {
// 	// TODO 这里需要更严格检查一下是否是正常的函数名，但是目前没有
// 	if _, ok := glob.BuiltinKeywordsSet[string(obj)]; ok {
// 		return nil, true
// 	}

// 	// TODO 这里需要更严格检查一下是否是正常的函数名
// 	if glob.IsKeySymbol(string(obj)) {
// 		return nil, true
// 	}

// 	fnDef := e.GetLatestFnT_GivenNameIsIn(string(obj))
// 	if fnDef == nil {
// 		return nil, false
// 	}
// 	return fnDef, true
// }

// func (e *Env) StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fn ast.Obj, fnTemplateFnObj *ast.FnObj, fnTStruct *ast.FnTStruct) glob.GlobRet {
// 	if fnTemplateFnObj != nil {
// 		fnTStruct, ret := e.GetFnStructFromFnTName(fnTemplateFnObj)
// 		if ret.IsErr() {
// 			return ret
// 		}

// 		ret = e.InsertFnInFnTT(fn, fnTStruct)
// 		if ret.IsErr() {
// 			return ret
// 		}

// 		return glob.NewGlobTrue("")
// 	} else {
// 		ret := e.InsertFnInFnTT(fn, fnTStruct)
// 		if ret.IsErr() {
// 			return ret
// 		}

// 		return glob.NewGlobTrue("")
// 	}
// }

// func (e *Env) getInstantiatedFnTTOfFnObj(fnObj *ast.FnObj) (*ast.FnTStruct, bool, glob.GlobRet) {
// 	if ast.IsFnTemplate_ObjFn(fnObj) {
// 		fnTNoName, err := fnObj.FnTObj_ToFnTNoName()
// 		if err != nil {
// 			return nil, false, glob.ErrRet(err)
// 		}
// 		return fnTNoName, true, glob.NewGlobTrue("")
// 	}

// 	def := e.GetFnTemplateDef(fnObj.FnHead.(ast.Atom))
// 	if def == nil {
// 		return nil, false, glob.NewGlobTrue("")
// 	}

// 	fnTNoName, err := def.Instantiate_GetFnTemplateNoName(fnObj)
// 	if err != nil {
// 		return nil, false, glob.ErrRet(err)
// 	}

// 	return fnTNoName, true, glob.NewGlobTrue("")
// }

// func (env *Env) StoreTrueEqualValues(key, value ast.Obj) {
// 	// 如果已经知道它的值了，那不能存了；否则比如我在外部环境里知道了a = 3，内部环境在反证法证明 a != 1，那我 a = 1就把a = 3覆盖掉了，a = 3这个取值貌似就不work了。某种程度上就是弄了个const
// 	if v := env.GetSymbolSimplifiedValue(key); v != nil {
// 		return
// 	}
// 	env.SymbolSimplifiedValueMem[key.String()] = value
// }

// func (env *Env) storeSymbolSimplifiedValue(left, right ast.Obj) glob.GlobRet {
// 	_, newLeft := env.ReplaceSymbolWithValue(left)
// 	if cmp.IsNumExprLitObj(newLeft) {
// 		simplifiedNewLeft := cmp.IsNumExprObjThenSimplify(newLeft)
// 		env.StoreTrueEqualValues(right, simplifiedNewLeft)
// 	}

// 	_, newRight := env.ReplaceSymbolWithValue(right)
// 	if cmp.IsNumExprLitObj(newRight) {
// 		simplifiedNewRight := cmp.IsNumExprObjThenSimplify(newRight)
// 		env.StoreTrueEqualValues(left, simplifiedNewRight)
// 	}

// 	return glob.NewGlobTrue("")
// }

// func (env *Env) GetEqualObjs(obj ast.Obj) (*[]ast.Obj, bool) {
// 	objAsStr := obj.String()
// 	facts, ok := env.EqualMem[objAsStr]
// 	return facts, ok
// }

// func (env *Env) NewFnTemplateInEnvMem(stmt *ast.FnTemplateDefStmt) glob.GlobRet {
// 	// 确保template name 没有被声明过
// 	ret := env.IsNameDefinedOrBuiltin(string(stmt.TemplateDefHeader.Name), map[string]struct{}{})
// 	if ret.IsTrue() {
// 		return glob.ErrRet(fmt.Errorf("fn template name %s is already declared", stmt.TemplateDefHeader.Name))
// 	}

// 	ret = env.AtomsInFnTemplateFnTemplateDeclared(ast.Atom(stmt.TemplateDefHeader.Name), stmt)
// 	if ret.IsErr() {
// 		return ret
// 	}

// 	env.FnTemplateDefMem[string(stmt.TemplateDefHeader.Name)] = *stmt
// 	return glob.NewGlobTrue("")
// }

// func (env *Env) newUniFact_ThenFactIsSpecFact(stmt *ast.UniFactStmt, thenFact *ast.SpecFactStmt) glob.GlobRet {
// 	return env.storeUniFactInMem(thenFact, stmt)
// }

// func (env *Env) newUniFact_ThenFactIsOrStmt(stmt *ast.UniFactStmt, thenFact *ast.OrStmt) glob.GlobRet {
// 	return env.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.NewFact(stmt, thenFact)
// }

// func (env *Env) newUniFact_ThenFactIsIffStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactWithIffStmt) glob.GlobRet {
// 	thenToIff := thenFact.NewUniFactWithThenToIff()
// 	iffToThen := thenFact.NewUniFactWithIffToThen()

// 	mergedThenToIff := ast.MergeOuterInnerUniFacts(stmt, thenToIff)
// 	ret := env.newUniFact(mergedThenToIff)
// 	if ret.IsErr() {
// 		return ret
// 	}

// 	mergedIffToThen := ast.MergeOuterInnerUniFacts(stmt, iffToThen)
// 	ret = env.newUniFact(mergedIffToThen)
// 	if ret.IsErr() {
// 		return ret
// 	}

// 	return glob.NewGlobTrue("")
// }

// func (env *Env) newUniFact_ThenFactIsUniFactStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactStmt) glob.GlobRet {
// 	mergedUniFact := ast.MergeOuterInnerUniFacts(stmt, thenFact)
// 	return env.newUniFact(mergedUniFact)
// }

// func (env *Env) newUniFact_ThenFactIsEqualsFactStmt(stmt *ast.UniFactStmt, thenFact *ast.EqualsFactStmt) glob.GlobRet {
// 	equalFacts := thenFact.ToEqualFacts_PairwiseCombination()
// 	for _, equalFact := range equalFacts {
// 		ret := env.newUniFact_ThenFactIsSpecFact(stmt, equalFact)
// 		if ret.IsErr() {
// 			return ret
// 		}
// 	}
// 	return glob.NewGlobTrue("")
// }

// func (env *Env) storeSpecFactInMem(stmt *ast.SpecFactStmt) glob.GlobRet {
// 	return env.KnownFactsStruct.SpecFactMem.newFact(stmt)
// }

// func (env *Env) storeUniFactInMem(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) glob.GlobRet {
// 	return env.KnownFactsStruct.SpecFactInUniFactMem.newFact(specFact, uniFact)
// }
