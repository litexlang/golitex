// Aristotle induction
export const testList0 = [
  "def obj if x | => {}",
  "def set x | obj(x);",
  "let y | set(y);",
  "def set2 z | set(z);",
  "set2(y);",
  "set2(y);",
];

export const testList1 = [
  "def obj if x | => {}",
  "def obj2 if x | => {}",
  "def p2 x | obj(x), obj2(x);",
  "let y | obj(y);",
  "if | obj2(y) => {p2(y)};",
  // "if | => {p2(y)};",
];

export const testList2 = [
  "def obj if x | => {}",
  "def obj2 x | obj(x) ;",
  "def obj3 if x | => {}",
  "def obj4 if x | => {obj3(x)}",
  "def inf if x | obj(x) => {obj3(x)}",
];

export const testList3 = [
  "def obj if x | => {}",
  "def obj2 x | obj(x) ;",
  "def obj3 if x | obj(x), obj2(x) => {} ",
  "prove if x | obj(x), obj3(x) => {obj2(x)} {}", // obj3 is useless
];

export const testList = [";"];

export const testCode = false;
