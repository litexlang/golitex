package kernel_lib_litex_code

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

var AddFn = ast.NewFnSetObjWithoutName([]ast.Obj{ast.Atom(glob.KeywordReal), ast.Atom(glob.KeywordReal)}, ast.Atom(glob.KeywordReal))

var SubtractFn = ast.NewFnSetObjWithoutName([]ast.Obj{ast.Atom(glob.KeywordReal), ast.Atom(glob.KeywordReal)}, ast.Atom(glob.KeywordReal))

var MultiplyFn = ast.NewFnSetObjWithoutName([]ast.Obj{ast.Atom(glob.KeywordReal), ast.Atom(glob.KeywordReal)}, ast.Atom(glob.KeywordReal))

var DivideFn = ast.NewFnSetObjWithName("divide", []string{"x", "y"}, []ast.Obj{ast.Atom(glob.KeywordReal), ast.Atom(glob.KeywordReal)}, []ast.Spec_OrFact{ast.NewPureSpecificFactStmt(false, glob.KeySymbolEqual, []ast.Obj{ast.Atom("y"), ast.Atom("0")}, glob.BuiltinLine0)}, ast.Atom(glob.KeywordReal), []ast.Spec_OrFact{})

var ModFn = ast.NewFnSetObjWithName("mod", []string{"x", "y"}, []ast.Obj{ast.Atom(glob.KeywordInteger), ast.Atom(glob.KeywordInteger)}, []ast.Spec_OrFact{ast.NewPureSpecificFactStmt(false, glob.KeySymbolEqual, []ast.Obj{ast.Atom("y"), ast.Atom("0")}, glob.BuiltinLine0)}, ast.Atom(glob.KeywordInteger), []ast.Spec_OrFact{})

var PowerFn = ast.NewFnSetObjWithName("power", []string{"x", "y"}, []ast.Obj{ast.Atom(glob.KeywordReal), ast.Atom(glob.KeywordInteger)}, []ast.Spec_OrFact{ast.NewOrStmt([]ast.SpecificFactStmt{ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{ast.Atom("x"), ast.Atom("0")}, glob.BuiltinLine0), ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{ast.Atom("y"), ast.Atom("0")}, glob.BuiltinLine0)}, glob.BuiltinLine0)}, ast.Atom(glob.KeywordReal), []ast.Spec_OrFact{})
