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

// import ast "golitex/ast"

// // func (e *Env) GetEnumFact(enumName string) ([]ast.Obj, bool) {
// // 	for env := e; env != nil; env = env.Parent {
// // 		enumFacts, ok := env.EnumFacts[enumName]
// // 		if ok {
// // 			return enumFacts, true
// // 		}
// // 	}

// // 	return nil, false
// // }

// func (e *Env) GetLatestFnT_GivenNameIsIn(fnName string) *FnInFnTMemItem {
// 	for env := e; env != nil; env = env.Parent {
// 		fnInFnTemplateFacts, ok := env.FnInFnTemplateFactsMem[fnName]
// 		if ok {
// 			return &fnInFnTemplateFacts[len(fnInFnTemplateFacts)-1]
// 		}
// 	}

// 	return nil
// }

// func (e *Env) IsTransitiveProp(propName string) bool {
// 	for env := e; env != nil; env = env.Parent {
// 		_, ok := env.TransitivePropMem[propName]
// 		if ok {
// 			return true
// 		}
// 	}
// 	return false
// }

// func (e *Env) GetRelatedObjSliceOfTransitiveProp(propName string, obj ast.Obj) []ast.Obj {
// 	ret := []ast.Obj{}
// 	for env := e; env != nil; env = env.Parent {
// 		relatedObjSlice, ok := env.TransitivePropMem[propName]
// 		if ok {
// 			if relatedObjSlice, ok := relatedObjSlice[obj.String()]; ok {
// 				ret = append(ret, relatedObjSlice...)
// 			}
// 		}
// 	}
// 	if len(ret) == 0 {
// 		return nil
// 	}
// 	return ret
// }

// func (e *Env) GetAlgoDef(funcName string) *ast.DefAlgoStmt {
// 	for env := e; env != nil; env = env.Parent {
// 		algoDef, ok := env.AlgoDefMem[funcName]
// 		if ok {
// 			return algoDef
// 		}
// 	}
// 	return nil
// }

// // GetObjTuple 检查 obj 是否是 tuple
// // 通过获取所有环境中与 obj 相等的对象列表，检查其中是否有 tuple
// // 如果找到 tuple，返回该 tuple；否则返回 nil
// func (e *Env) GetObjTuple(obj ast.Obj) ast.Obj {
// 	// 遍历所有环境
// 	for env := e; env != nil; env = env.Parent {
// 		// 获取当前环境中与 obj 相等的所有对象
// 		equalObjs, ok := env.GetEqualObjs(obj)
// 		if ok && equalObjs != nil {
// 			// 检查其中是否有 tuple
// 			for _, equalObj := range *equalObjs {
// 				if fnObj, ok := equalObj.(*ast.FnObj); ok && ast.IsTupleFnObj(fnObj) {
// 					return fnObj
// 				}
// 			}
// 		}
// 	}
// 	return nil
// }

// // GetListSetEqualToObj 检查 obj 是否等于某个 list set
// // 通过获取所有环境中与 obj 相等的对象列表，检查其中是否有 list set
// // 如果找到 list set，返回该 list set；否则返回 nil
// func (e *Env) GetListSetEqualToObj(obj ast.Obj) ast.Obj {
// 	// 如果 obj 本身就是一个 list set，直接返回
// 	if ast.IsListSetObj(obj) {
// 		return obj
// 	}

// 	// 遍历所有环境
// 	for env := e; env != nil; env = env.Parent {
// 		// 获取当前环境中与 obj 相等的所有对象
// 		equalObjs, ok := env.GetEqualObjs(obj)
// 		if ok && equalObjs != nil {
// 			// 检查其中是否有 list set
// 			for _, equalObj := range *equalObjs {
// 				if ast.IsListSetObj(equalObj) {
// 					return equalObj
// 				}
// 			}
// 		}
// 	}
// 	return nil
// }

// // GetSetBuilderEqualToObj 检查 obj 是否等于某个 intensional set
// // 通过获取所有环境中与 obj 相等的对象列表，检查其中是否有 intensional set
// // 或者从 IntensionalSetMem 中查找（如果 obj 等于某个已定义的 intensional set 的 CurSet）
// // 如果找到 intensional set 对象，返回该对象；如果找到 IntensionalSetStmt，返回其 CurSet；否则返回 nil
// func (e *Env) GetSetBuilderEqualToObj(obj ast.Obj) *ast.FnObj {
// 	// 如果 obj 本身就是一个 intensional set 对象，直接返回
// 	if ast.IsSetBuilder(obj) {
// 		return obj.(*ast.FnObj)
// 	}

// 	// 遍历所有环境
// 	for env := e; env != nil; env = env.Parent {
// 		// 获取当前环境中与 obj 相等的所有对象
// 		equalObjs, ok := env.GetEqualObjs(obj)
// 		if ok && equalObjs != nil {
// 			// 检查其中是否有 intensional set 对象
// 			for _, equalObj := range *equalObjs {
// 				if ast.IsSetBuilder(equalObj) {
// 					return equalObj.(*ast.FnObj)
// 				}
// 			}
// 		}

// 	}
// 	return nil
// }
