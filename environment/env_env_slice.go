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

func NewEnvMemory() *EnvMemory {
	return &EnvMemory{
		EqualMem:                 make(map[string]shared_ptr_to_slice_of_obj),
		KnownFactsStruct:         makeKnownFactsStruct(),
		SymbolSimplifiedValueMem: make(map[string]ast.Obj),

		AtomObjDefMem:    make(AtomObjDefMem),
		PropDefMem:       make(PropDefMem),
		FnTemplateDefMem: make(FnTemplateDefMem),
		ExistPropDefMem:  make(ExistPropDefMem),

		TransitivePropMem:  make(map[string]map[string][]ast.Obj),
		CommutativePropMem: make(map[string]*PropCommutativeCase),

		AlgoDefMem:      make(map[string]*ast.DefAlgoStmt),
		DefProveAlgoMem: make(map[string]*ast.DefProveAlgoStmt),
	}
}

func (envMgr *EnvMgr) NewEnvMgr(pkgMgr *EnvPkgMgr) *EnvMgr {
	return &EnvMgr{
		AllDefinedAtomObjNames: make(map[string]EnvDepthWhereNameIsUsed),
		AllDefinedPropNames:    make(map[string]EnvDepthWhereNameIsUsed),
		PackageManager:         pkgMgr,
		EnvSlice:               []EnvMemory{*NewEnvMemory()},
	}
}

func (envMgr *EnvMgr) GetUpMostEnv() *EnvMemory {
	return &envMgr.EnvSlice[0]
}

func (envMgr *EnvMgr) GetSecondUpMostEnv() *EnvMemory {
	return &envMgr.EnvSlice[1]
}
