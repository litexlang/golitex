export const exampleDict = {
  三段论: {
    code: [
      // Introduce a concept "会死"
      "def something is 会死 => {};",
      // Introduce a concept "人", "人" has property that "人会死"
      "def something is 人 => {something is 会死};",
      // Introduce a variable "苏格拉底", "苏格拉底" has property that "苏格拉底 is 人"
      "let 苏格拉底 : 苏格拉底 is 人;",
      // Check: "苏格拉底 is 会死"
      "苏格拉底 is 会死;",
      // Introduce a variable "神仙", "神仙" has property that "神仙 is not 会死"
      "let 神仙 : 神仙 is not 会死;",
      // prove by contradiction: to show "神仙 is not 人", we assume "神仙 is 人"
      // then we get {神仙 is 会死;} which leads to contradiction:
      // "神仙 is 会死" "神仙 is not 会死" is valid at the same time.
      "prove_by_contradiction 神仙 is not 人 {神仙 is 会死;} contradiction 神仙 is 会死;",
    ],
    debug: false,
    print: false,
  },
  defs: {
    code: [
      "def x is p => {};",
      "def x is p1 => {x is p};",
      "def x is p2 => {x is p1};",
      "def x is p3 <=> {x is p};",
      "def x is p4 <= {x is p};",
      "def pair_wise(x,y) => {};",
      "def multi_wise(x,y,z) => {};",
      "def q0(x) => {};",
      "def x is q <=> {x is q0} when x is p;",
    ],
    debug: true,
    print: false,
  },
  let: {
    code: [
      "let x , y ,z: x is p;",
      "let a,b,c : a,b,c are p;",
      "let 1,0, 12343124, 314_garbage_-code_159, _garbage, 你好world;",
    ],
    debug: true,
    print: false,
  },
  facts: {
    code: [
      "x is p;",
      "x is q0;", // unknown
      "if x : x is p2 => {x is p1};",
      "if x : x is p2 => {x is p2};",
      "if x : x is p2, y is p1 => {}",
      "if : y is p1 => {y is p};",
      "if y is p1 => {y is p};",
      "if x : y is p1 => {y is p};",
      "if a: => {if : a is p1 => {if : => {a is p}}};",
    ],
    debug: true,
    print: false,
  },
  knows: {
    code: [
      "know y is p, z is q;",
      "y is p, q(z);",
      "x,y are p;",
      "def pq(y,z) => {};",
      "know if x,y : x is p, y is q => {pq(x,y)};",
      "pq(y,z);",
    ],
    debug: true,
    print: false,
  },
  exist_have: {
    code: [
      "exist something is p;",
      "exist pq(y,z);",
      "have d: d is p1;",
      "have e,f: pq(e,f);",
    ],
    debug: true,
    print: false,
  },
  prove: {
    code: [
      "prove if x | x is p2 => {x is p} {x is p1;}",
      "know z is p3;",
      "prove z is p {z is p2; z is p1;}",
    ],
    debug: true,
    print: false,
  },
  prove_by_contradiction: {
    code: [
      "let n | n is not p",
      "prove_by_contradiction n is not p3 {n is p2; n is p1;} contradiction n is p;",
    ],
    debug: true,
    print: false,
  },
  by: {
    code: [
      "def x is object => {};",
      "def x is set => {x is object};",
      "def element_of(A,B) => {} when A,B are object;",
      "def equal(A,B) <=> {if x : element_of(x,A) => {element_of(x,B)} [set_equal] , if x : element_of(x,B) => {element_of(x,A)}} when A,B are set;",
      "let A,B,x : A,B are set, equal(A,B), element_of(x,A);",
      "A,B are object;",
      "by set_equal(A,B,x) => {element_of(x,B)};",
    ],
    debug: true,
    print: false,
  },
  block: {
    code: [
      "let x1, x2 ,x3 | x2 is object;",
      `  {
      def x is object => {};
      know x1 is object;
      x1,x2 are object; 
      }`,
      "x1 is object;",
      "x2 is object;",
    ],
    debug: true,
    print: false,
  },
};
