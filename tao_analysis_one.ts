export const setTheory = [
  "def x is object => {};",
  "def x is set => {x is object};",
  "def =(x,y) => {};",
  "def element_of(A,B): A is object, B is object => {};",
  "def equal(A,B) : A is set, B is set <=> {if x : element_of(x,A) => {element_of(x,B)} [set_equal] , if x : element_of(x,B) => {element_of(x,A)}} ;",
  "def x is empty : x is set => {if z : => {not element_of(z,x)}} ;",
  "know exist x : x is empty => {}[Existence_of_empty_set];",
  "know if x : x is object => {exist A : A is set => {element_of(x, A) , if y : element_of(y, A) => { =(y,x) } } [inner-exist]  }[Singleton_sets_and_pair_sets];",
];

export const setTheoryTest1 = [
  "let A,B,x : A is set, B is set, equal(A,B), element_of(x,A);",
  "by set_equal(A,B,x) => {element_of(x,B)};",
  "know if x, y : x is empty, y is empty => {equal(x,y)};",
  "let s1, s2 : s1 is empty, s2 is empty;",
  "equal(s1,s2);",
];
