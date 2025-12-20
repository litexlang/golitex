package litex_env

import ast "golitex/ast"

type EnvMgr struct {
	AllDefinedAtomObjNames    map[string]int
	AllDefinedPropNames       map[string]int
	AllDefinedExistPropNames  map[string]int
	AllDefinedFnTemplateNames map[string]int
	AllDefinedAlgoNames       map[string]int
	AllDefinedProveAlgoNames  map[string]int

	PackageManager *EnvPkgMgr
	EnvSlice       []EnvMemory
}

type EnvMemory struct {
	// definition memory
	AtomObjDefMem    AtomObjDefMem
	PropDefMem       PropDefMem
	FnTemplateDefMem FnTemplateDefMem
	ExistPropDefMem  ExistPropDefMem

	// algo
	AlgoDefMem      map[string]*ast.DefAlgoStmt
	DefProveAlgoMem map[string]*ast.DefProveAlgoStmt

	// facts memory
	EqualMem                 map[string]shared_ptr_to_slice_of_obj
	KnownFactsStruct         KnownFactsStruct
	SymbolSimplifiedValueMem map[string]ast.Obj

	// transitive prop and commutative prop
	TransitivePropMem  map[string]map[string][]ast.Obj
	CommutativePropMem map[string]*PropCommutativeCase
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

func NewEnvMgr(pkgMgr *EnvPkgMgr) *EnvMgr {
	return &EnvMgr{
		AllDefinedAtomObjNames:    make(map[string]int),
		AllDefinedPropNames:       make(map[string]int),
		AllDefinedExistPropNames:  make(map[string]int),
		AllDefinedFnTemplateNames: make(map[string]int),
		AllDefinedAlgoNames:       make(map[string]int),
		AllDefinedProveAlgoNames:  make(map[string]int),
		PackageManager:            pkgMgr,
		EnvSlice:                  []EnvMemory{*NewEnvMemory()},
	}
}

func (envMgr *EnvMgr) GetUpMostEnv() *EnvMemory {
	return &envMgr.EnvSlice[0]
}

func (envMgr *EnvMgr) GetSecondUpMostEnv() *EnvMemory {
	return &envMgr.EnvSlice[1]
}
