package litex_env

import ast "golitex/ast"

type EnvDepthWhereNameIsUsed uint // where a prop or atom object is defined

type EnvMgr struct {
	AllDefinedAtomObjNames map[string]EnvDepthWhereNameIsUsed
	AllDefinedPropNames    map[string]EnvDepthWhereNameIsUsed
	PackageManager         *EnvPkgMgr
	EnvSlice               []EnvMemory
}

type EnvMemory struct {
	// facts memory
	EqualMem                 map[string]shared_ptr_to_slice_of_obj
	KnownFactsStruct         KnownFactsStruct
	SymbolSimplifiedValueMem map[string]ast.Obj

	// definition memory
	AtomObjDefMem    AtomObjDefMem
	PropDefMem       PropDefMem
	FnTemplateDefMem FnTemplateDefMem
	ExistPropDefMem  ExistPropDefMem

	// transitive prop
	TransitivePropMem  map[string]map[string][]ast.Obj
	CommutativePropMem map[string]*PropCommutativeCase

	// algo
	AlgoDefMem      map[string]*ast.DefAlgoStmt
	DefProveAlgoMem map[string]*ast.DefProveAlgoStmt
}
