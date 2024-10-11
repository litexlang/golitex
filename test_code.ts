export const testCodes = {
  Basics:
    ":obj(x) :set(x) :set2(x,y) :F(x,y:set(x)) {$son(h:set(h)) {set2(y,h);}} :set3(x){:set2(x)} ;",
  // Nothing: "",
  // Comment: "\\ Comment",
  // BasicInfer:
  //   "def P(x) ; def Q(x) ; def Thm1(x,z) ; def Thm2(1,2); def Axiom(x,y: P(x), Q(y)) { Thm1(x,y); Thm2(x,y);} ",
  // BasicKnow: "know set(1); @ set2(1,2);",
  // BasicCheck: "set(1);",
  // ForAllKnow: "know set(#);",
  // ForAllCheck: "set(3);",
  // Bundle: ":bundle(x,y,z: F(x,y):son(z))", // call defOpt has 2 possible effects: either check requirement and emit opt, or check opt emit requirements
  // Redefine: "re_def set(x)",
  // ExistDecl: "exist SetExist(x: set(x));",
  // Have: "let S: SetExist(S);", //! This works improperly. Have should be inferred by knowing exist, not declaring exist.
  // ProveExist: "let o: obj(o); exist ObjExist(x: obj(x));  ObjExist(o);",
  // DefDecl:
  //   ":subC(x); : subD(x){:subE(y);};def concept(x,y: subC(x), subD(x):subE(y))",
  // DefCheckLeft: "let x,y: subC(x), subD(x):subE(y) ; concept(x,y);",
  // DefCheckRight: "let x1,y1: concept(x1,y1); subC(x1); subD(x1):subE(x2);",
  // DefDecl2: "def implies(x:set(x)) => {set(x);}",
  // DefDecl3: "def implies2(x:set(x)) => set(x);",
  // DefDecl4: "def implies3(x:set(x)) => {set(x);}",
  // DefDecl5: "def implies4(x:set(x)) => {:son(x); son(x);}",
  // DefDecl6: "def iff1(x:set(x)) <=> {set(x);}",
  // DefDecl7: "def iff2(x:set(x)) <=> set(x),set(x);",
  // DefDecl8: "def bundleIff(x,y:set(x), set1(x,y));",
  // ExistDecl1: "exist SomethingWithSomeProperties_E(x: set(x))",
  // Prove: "def implies(x:set(x)) {set(x);}; prove implies(x) {}",
  // CallDefRight: "def func(x:set(x)); : set(x); let x: set(x); func(x);",
  // inferRight:
  //   "def inf(x,y:set(x),set(y)) => {set2(x,y);} let x,y: set(x), set(y), inf(x,y);set2(x,y);",
  // KnowEverything: "let a,b; know_everything inf(a,b);",
  //! ideal: let x,y: know set(#x:..):set2(#y:..) => {...}
  // KnowImplies: "let x,y; know set(#x) => {set(#x);};",
  // ProveDef0: "& set3(x) {};",
  // ProveDef: ":f2(x); :set3(x){:set2(x){f2(x);}}; ",
  // ProveDef1: "prove set3(x):set2(x:f2(x)){}",
  // ProveDef2: "prove set3(y):set2(y){know f2(y);}",

  // ProveDef3: ":bun(x,y:sett(x),sett(y)) :sett(x)",
  // ProveDef4: "prove bun(x,y) {know sett(x), sett(y);}",
  // ProveHaveExist: "exist E(x:set(x)); let x: set(x); have E(x);",

  knowExtendedFact:
    ":fun(x,y){:fun2(z:set(z)) {}} ; let x,y,z; know fun(#x,y:set(x)):fun2(#z:set2(y,z));",
  checkExtendedFact: "know set(x), set2(y,z), set(z); fun(x,y):fun2(z);",
};

export const testErrorCode = {
  RepeatDeclaration: `def set(x); def set(x); `,
  Let: "let o:set3(o);",
};
