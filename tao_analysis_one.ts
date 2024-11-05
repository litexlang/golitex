export const setTheory = [
  "def x is object => {};",
  "def x is set => {x is object};",
  "def element_of(A,B) => {} when A,B are object;",
  "def equal(A,B) => {if x | element_of(x,A) => {element_of(x,B)} [set_equal] , if x | element_of(x,B) => {element_of(x,A)}} when A,B are set;",
  "let A,B,x | A,B are set, equal(A,B), element_of(x,A);",
  "A,B are object;",
  "by set_equal(A,B,x);",
];

export const testTao = false;
