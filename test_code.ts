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

// Aristotle induction
export const testList = [
  "def obj if x | => {};",
  "def set x | obj(x);",
  "let y | set(y);",
  "def set2 z | set(z);",
  "set2(y);",
  "set2(y);",
];

export const testList1 = [
  "def obj if x | => {};",
  "def obj2 if x | => {};",
  "def p2 x | obj(x), obj2(x);",
  "let y | obj(y);",
  "if | obj2(y) => {p2(y)};",
  // "if | => {p2(y)};",
];

export const testList2 = [
  "def obj if x | => {};",
  "def obj2 x | obj(x) ;",
  "def obj3 if x | => {};",
  "def obj4 if x | => {obj3(x)};",
  "def inf if x | obj(x) => {obj3(x)}",
];

export const testCode = false;
