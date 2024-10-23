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
  "def obj if x | => {};",
  "def obj2 x | obj(x) ;",
  "def obj3 if x | obj(x), obj2(x) => {} ",
  "prove if x | obj(x), obj3(x) => {obj2(x)} {}", // obj3 is useless
];

export const testList4 = [";;;\n\n;;"];

export const testList5 = [
  "def p1 if x | => {}",
  "def p2 x | p1(x);",
  // "def p3 x | p2(x);",
];

export const testList6 = [
  "def p1 if x | => {}",
  "exist Ex x | p1(x);", // can be used as a "stronger" version of def.
  "let y | p1(y);",
  "have x | Ex(x);",
  "Ex(y);", // we declare and exe exist-fact by exactly using shortOpt code.
  "have z | Ex(z);",
];

export const testList = [
  "def p1 if x | => {}",
  "def p2 x | p1(x);",
  "def p3 x | p2(x);",
  "let y | p1(y);",
  "p3(y) by {p2(y)};",
];

export const testCode = false;
