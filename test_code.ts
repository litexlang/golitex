import { testListOfCodes } from "./executor_test";
import { setTheory, testTao } from "./tao_analysis_one";

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
export const testList2 = [
  "def obj x | => {};",
  "def set x | obj(x);",
  "let y | set(y);",
  "def set2 z | set(z);",
  "set2(y);",
  "set2(y);",
];

export const testList = [
  "def obj x | => {};",
  "def obj2 x | => {};",
  "def p2 x | obj(x), obj2(x);",
  "let y | obj(y);",
  // "if | obj2(y) => {p2(y)};",
  "if | => {p2(y)};",
];

export const testCode = false;
