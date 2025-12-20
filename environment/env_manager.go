package litex_env

import ast "golitex/ast"

type EnvMgr struct {
	AllDefinedAtomObjNames    map[string]*DepthAtomDefPair
	AllDefinedPropNames       map[string]*DepthPropDefPair
	AllDefinedExistPropNames  map[string]*DepthExistPropDefPair
	AllDefinedFnTemplateNames map[string]*DepthFnTemplateDefPair
	AllDefinedAlgoNames       map[string]*DepthAlgoDefPair
	AllDefinedProveAlgoNames  map[string]*DepthProveAlgoDefPair

	PkgMgr   *EnvPkgMgr
	EnvSlice []EnvMemory
}

type DepthAtomDefPair struct {
	depth   int
	defStmt *ast.DefLetStmt
}

func newDepthAtomDefPair(depth int, defStmt *ast.DefLetStmt) *DepthAtomDefPair {
	return &DepthAtomDefPair{depth, defStmt}
}

type DepthPropDefPair struct {
	depth   int
	defStmt *ast.DefPropStmt
}

func newDepthPropDefPair(depth int, defStmt *ast.DefPropStmt) *DepthPropDefPair {
	return &DepthPropDefPair{depth, defStmt}
}

type DepthExistPropDefPair struct {
	depth   int
	defStmt *ast.DefExistPropStmt
}

func newDepthExistPropDefPair(depth int, defStmt *ast.DefExistPropStmt) *DepthExistPropDefPair {
	return &DepthExistPropDefPair{depth, defStmt}
}

type DepthFnTemplateDefPair struct {
	depth   int
	defStmt *ast.FnTemplateDefStmt
}

func newDepthFnTemplateDefPair(depth int, defStmt *ast.FnTemplateDefStmt) *DepthFnTemplateDefPair {
	return &DepthFnTemplateDefPair{depth, defStmt}
}

type DepthAlgoDefPair struct {
	depth   int
	defStmt *ast.DefAlgoStmt
}

func newDepthAlgoDefPair(depth int, defStmt *ast.DefAlgoStmt) *DepthAlgoDefPair {
	return &DepthAlgoDefPair{depth, defStmt}
}

type DepthProveAlgoDefPair struct {
	depth   int
	defStmt *ast.DefProveAlgoStmt
}

func newDepthProveAlgoDefPair(depth int, defStmt *ast.DefProveAlgoStmt) *DepthProveAlgoDefPair {
	return &DepthProveAlgoDefPair{depth, defStmt}
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
	}
}

func NewEnvMgr(pkgMgr *EnvPkgMgr) *EnvMgr {
	return &EnvMgr{
		AllDefinedAtomObjNames:    make(map[string]*DepthAtomDefPair),
		AllDefinedPropNames:       make(map[string]*DepthPropDefPair),
		AllDefinedExistPropNames:  make(map[string]*DepthExistPropDefPair),
		AllDefinedFnTemplateNames: make(map[string]*DepthFnTemplateDefPair),
		AllDefinedAlgoNames:       make(map[string]*DepthAlgoDefPair),
		AllDefinedProveAlgoNames:  make(map[string]*DepthProveAlgoDefPair),
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
