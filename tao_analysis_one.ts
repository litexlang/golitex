export const setTheory = [
  "def x is object => {};",
  "def x is set => {x is object};",
  "def element_of(A,B) => {} when A,B are object;",
  "def equal(A,B) <=> {if x : element_of(x,A) => {element_of(x,B)} [set_equal] , if x : element_of(x,B) => {element_of(x,A)}} when A,B are set;",
  "let A,B,x : A,B are set, equal(A,B), element_of(x,A);",
  "by set_equal(A,B,x) => {element_of(x,B)};",
  "def x is empty => {if z : => {not element_of(z,x)}} when x is set;",
  "know if x, y : x,y are empty => {equal(x,y)};",
  "let s1, s2 : s1,s2 are empty;",
  "equal(s1,s2);",
];
