export const testCodes = {
  Basics:
    ":obj(x) :set(x) :set2(x,y) :F(x,y:set(x)) {$son(h:set(h)) {set2(y,h);}}",
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

  ExistDecl: "exist SetExist(x: set(x));",
  // Have: "let S: SetExist(S);", //! This works improperly. Have should be inferred by knowing exist, not declaring exist.
  ProveExist: "let o: obj(o); exist ObjExist(x: obj(x));  ObjExist(o);",

  // DefDecl:
  //   ":subC(x); : subD(x){:subE(y);};def concept(x,y: subC(x), subD(x):subE(y))",
  // DefCheckLeft: "let x,y: subC(x), subD(x):subE(y) ; concept(x,y);",
  // DefCheckRight: "let x1,y1: concept(x1,y1); subC(x1); subD(x1):subE(x2);",
};

export const testErrorCode = {
  RepeatDeclaration: `def set(x); def set(x); `,
  Let: "let o:set3(o);",
};
