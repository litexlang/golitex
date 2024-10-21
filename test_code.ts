export const testCodes = {
  // Basics: ":set x | ; ",
  // IfThen: ":deduce if x | set(x) => {};",
  // Opt: "let x; know set(#x);",
  // opt2: " know if x| set(x) => {set(x)} [g]; ",
};

export const testErrorCode = {
  // RepeatDeclaration: `def set(x); def set(x); `,
  // Let: "let o:set3(o);",
};

export const testList = ["def inf x |  set(x) => {} ;"];
