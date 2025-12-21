package litex_env

import ast "golitex/ast"

type shared_ptr_to_slice_of_obj = *[]ast.Obj
type PropDefMem map[string]ast.DefPropStmt
type ExistPropDefMem map[string]ast.DefExistPropStmt
type FnTemplateDefMem map[string]ast.FnTemplateDefStmt
type AtomObjDefMem map[string]*ast.DefLetStmt // 因为很多的obj会共享一个def obj. 可能是 nil
type FnInFnTMem map[string][]FnInFnTMemItem
type PropCommutativeCase struct {
	TruePureIsCommutative  bool
	FalsePureIsCommutative bool
}

type FnInFnTMemItem struct {
	AsFnTStruct *ast.FnTStruct
}

type KnownFactsStruct struct {
	SpecFactMem                       SpecFactMem
	SpecFactInLogicExprMem            SpecFactInLogicExprMem
	SpecFactInUniFactMem              SpecFactInUniFactMem
	SpecFact_InLogicExpr_InUniFactMem SpecFact_InLogicExpr_InUniFactMem
}

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

func (envMgr *EnvMgr) NewEnv() *EnvMgr {
	envMgr.EnvSlice = append(envMgr.EnvSlice, *NewEnvMemory())
	return envMgr
}

func (envMgr *EnvMgr) DeleteEnvUntilBuiltin() {
	for len(envMgr.EnvSlice) > 1 {
		envMgr.DeleteEnv()
	}
}

func (envMgr *EnvMgr) DeleteEnv() {
	// 把 当前的 def 从 all defined 里删了，不删最后一个，因为最后一个是最顶层的
	for k, _ := range envMgr.CurEnv().AtomObjDefMem {
		delete(envMgr.AllDefinedAtomObjNames, k)
	}
	for k, _ := range envMgr.CurEnv().PropDefMem {
		delete(envMgr.AllDefinedPropNames, k)
	}
	for k, _ := range envMgr.CurEnv().ExistPropDefMem {
		delete(envMgr.AllDefinedExistPropNames, k)
	}
	for k, _ := range envMgr.CurEnv().FnTemplateDefMem {
		delete(envMgr.AllDefinedFnTemplateNames, k)
	}
	for k, _ := range envMgr.CurEnv().AlgoDefMem {
		delete(envMgr.AllDefinedAlgoNames, k)
	}
	for k, _ := range envMgr.CurEnv().DefProveAlgoMem {
		delete(envMgr.AllDefinedProveAlgoNames, k)
	}

	envMgr.EnvSlice = envMgr.EnvSlice[:len(envMgr.EnvSlice)-1]
}

func (envMgr *EnvMgr) ParentEnv() *EnvMemory {
	return &envMgr.EnvSlice[len(envMgr.EnvSlice)-1]
}

func makeKnownFactsStruct() KnownFactsStruct {
	return KnownFactsStruct{
		SpecFactMem:                       *newSpecFactMem(),
		SpecFactInLogicExprMem:            *newSpecFactInLogicExprMem(),
		SpecFactInUniFactMem:              *newSpecFactInUniFact(),
		SpecFact_InLogicExpr_InUniFactMem: *newSpecFact_InLogicExpr_InUniFactMem(),
	}
}

func newSpecFact_InLogicExpr_InUniFactMem() *SpecFact_InLogicExpr_InUniFactMem {
	return &SpecFact_InLogicExpr_InUniFactMem{
		PureFacts:         make(map[string][]SpecFact_InLogicExpr_InUniFact),
		NotPureFacts:      make(map[string][]SpecFact_InLogicExpr_InUniFact),
		Exist_St_Facts:    make(map[string][]SpecFact_InLogicExpr_InUniFact),
		NotExist_St_Facts: make(map[string][]SpecFact_InLogicExpr_InUniFact),
	}
}

func NewCommutativePropMemItemStruct() *PropCommutativeCase {
	return &PropCommutativeCase{
		TruePureIsCommutative:  false,
		FalsePureIsCommutative: false,
	}
}
