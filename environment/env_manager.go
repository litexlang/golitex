package litex_env

import ast "golitex/ast"

type EnvMgr struct {
	AllDefinedAtomObjNames    map[string]*ast.DefLetStmt
	AllDefinedPropNames       map[string]*ast.DefPropStmt
	AllDefinedExistPropNames  map[string]*ast.DefExistPropStmt
	AllDefinedFnTemplateNames map[string]*ast.FnTemplateDefStmt
	AllDefinedAlgoNames       map[string]*ast.DefAlgoStmt
	AllDefinedProveAlgoNames  map[string]*ast.DefProveAlgoStmt

	PkgMgr   *EnvPkgMgr
	EnvSlice []EnvMemory
}

type EnvMemory struct {
	// definition memory
	AtomObjDefMem    map[string]struct{}
	PropDefMem       map[string]struct{}
	FnTemplateDefMem map[string]struct{}
	ExistPropDefMem  map[string]struct{}
	AlgoDefMem       map[string]struct{}
	DefProveAlgoMem  map[string]struct{}

	// facts memory
	EqualMem                 map[string]shared_ptr_to_slice_of_obj
	KnownFactsStruct         KnownFactsStruct
	SymbolSimplifiedValueMem map[string]ast.Obj

	// transitive prop and commutative prop
	TransitivePropMem  map[string]map[string][]ast.Obj
	CommutativePropMem map[string]*PropCommutativeCase

	// function template facts
	FnInFnTemplateFactsMem FnInFnTMem
}

func NewEnvMemory() *EnvMemory {
	return &EnvMemory{
		EqualMem:                 make(map[string]shared_ptr_to_slice_of_obj),
		KnownFactsStruct:         makeKnownFactsStruct(),
		SymbolSimplifiedValueMem: make(map[string]ast.Obj),

		AtomObjDefMem:    make(map[string]struct{}),
		PropDefMem:       make(map[string]struct{}),
		FnTemplateDefMem: make(map[string]struct{}),
		ExistPropDefMem:  make(map[string]struct{}),

		TransitivePropMem:  make(map[string]map[string][]ast.Obj),
		CommutativePropMem: make(map[string]*PropCommutativeCase),

		AlgoDefMem:      make(map[string]struct{}),
		DefProveAlgoMem: make(map[string]struct{}),

		FnInFnTemplateFactsMem: make(FnInFnTMem),
	}
}

func NewEnvMgr(pkgMgr *EnvPkgMgr) *EnvMgr {
	return &EnvMgr{
		AllDefinedAtomObjNames:    make(map[string]*ast.DefLetStmt),
		AllDefinedPropNames:       make(map[string]*ast.DefPropStmt),
		AllDefinedExistPropNames:  make(map[string]*ast.DefExistPropStmt),
		AllDefinedFnTemplateNames: make(map[string]*ast.FnTemplateDefStmt),
		AllDefinedAlgoNames:       make(map[string]*ast.DefAlgoStmt),
		AllDefinedProveAlgoNames:  make(map[string]*ast.DefProveAlgoStmt),
		PkgMgr:                    pkgMgr,
		EnvSlice:                  []EnvMemory{*NewEnvMemory()},
	}
}

func (envMgr *EnvMgr) GetUpMostEnv() *EnvMemory {
	return &envMgr.EnvSlice[0]
}

func (envMgr *EnvMgr) GetSecondUpMostEnv() *EnvMemory {
	return &envMgr.EnvSlice[1]
}
