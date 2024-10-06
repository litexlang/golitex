export const testCodes = {
  Nothing: "",
  Comment: "\\ Comment",
  BasicInfer:
    "def P(x) ; def Q(x) ; def Thm1(x,z) ; def Thm2(1,2); def Axiom(x,y: P(x), Q(y)) { Thm1(x,y); Thm2(x,y);}",
};

export const testErrorCode = {
  RepeatDeclaration: `def set(x); def set(x); `,
};
