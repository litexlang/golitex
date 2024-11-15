import { L_Env } from "./L_Env.ts";
import { runStrings } from "./L_Runner.ts";

type ExampleItem = {
  name: string;
  code: string[];
  debug: boolean;
  print: boolean;
};

const exampleList: ExampleItem[] = [
  {
    name: "syllogism(三段论)",
    code: [
      // Introduce a concept "mortal"
      "def 某物 is 生命有限;",
      // Introduce a concept "human", "human" has property that "human is 生命有限"
      "def 某物 is human => {某物 is 生命有限};",
      // Introduce a variable "Socrates", "Socrates" has property that "Socrates is human"
      "let Socrates : Socrates is human;",
      // Check: a specific human called Socrates is 生命有限."
      "Socrates is 生命有限;",
      // Check: for all human, human is 生命有限.
      "if x : x is human => {x is 生命有限};",
      // Introduce a variable "god", "god" has property that "god is not 生命有限"
      "let god : god is not 生命有限;",
      // prove by contradiction: to show "god is not human", we assume "god is human"
      // then we get {god is 生命有限;} which leads to contradiction:
      // "god is 生命有限" "god is not 生命有限" is valid at the same time.
      "prove_by_contradiction god is not human {god is 生命有限;} contradiction god is 生命有限;",
      "def 某物 is immortal => {某物 is not 生命有限};",
      "if somebody: somebody is immortal => {somebody is not 生命有限, somebody is not human};",
    ],
    debug: false,
    print: true,
  },
  {
    name: "defs",
    code: [
      // Define new concepts
      // Define a new concept called p. if something is p, then nothing happens
      "def q0(x);",
      "def x is q1;",
      "def x is p => {};",
      // if x is p1, then x is p
      "def x is p1 => {x is p};",
      "def x is p2 => {x is p1};",
      "def x is p3 => {x is p2};",
      // x is p4 is equivalent to x is p
      "def x is p4 <=> {x is p};",
      // x is p4 then x is p5
      "def x is p5 <= {x is p4};",
      // There are 2 ways of defining a concept, use functional notation or relational notation
      "def pair_wise(x,y) => {};",
      "def multi_wise(x,y,z) => {};",
      "def q0(x) => {};",
      // When is used to add conditions for both left and right hand side.
      "def x is q <=> {x is q0} when x is p;",
      // Example:
      "def <(x,y) => {};",
      "def >=(x,y) <= {not <(x,y)};",
      "let n1,n2,n3 : <(n1,n2), <(n2,n3);",
      "<(n1,n3);",
    ],
    debug: false,
    print: false,
  },
  {
    name: "let",
    code: [
      // let means introducing a new variable into current environment
      // introduce new variables x,y,z. Assume x is p
      "let x , y ,z: x is p, p(y);",
      // are is syntax sugar.
      "let a,b,c : a,b,c are p;",
      "let 1,0, 12343124, 314_garbage_-code_159, _garbage, 你好world;",
    ],
    debug: false,
    print: false,
  },
  {
    name: "facts",
    code: [
      // MAIN functionality of LiTeX: checking
      // check whether x is p. Since previously we assumed x is p, so this is true
      "x is p;",
      // Whether x is q0 is unknown
      "x is q0;", // unknown
    ],
    debug: false,
    print: false,
  },
  {
    name: "if_for_all",
    code: [
      // `if .. : .. => {..}` makes "for all" expressions possible
      // Check: for all x is p2, x is p1. By definition, it's true.
      "if x : x is p2 => {x is p1};",
      "if x : x is p2 => {x is q0};", // unknown
      "if x : x is p2 => {x is p1, x is q0};", // unknown
      // Check: if x is p2, then x is p2. In natural language it's a waste of words, but
      // actually it's hard to implement in a programming language.
      "if x : x is p2 => {x is p2};",
      // Check: for all x is p2, y (defined above) is p1, then nothing happens
      "if x : x is p2, y is p1 => {};",
      // If a called variable is not introduced in `if-then` expression, then
      // my interpreter searches the parent environment for the variable
      "if : y is p1 => {y is p};",
      "if y is p1 => {y is p};",
      "if x : y is p1 => {y is p};",
      // `if-then` in `if-then` inherits declared variables and their properties
      "if a: => {if : a is p1 => {if : => {a is p}}};",
      // know for all x which has properties `x is p1, x is p2, x is p3`, then x is p5.
      // know "sort of" works in the same way as how axioms and assume works.
      "know if x: x is p1, x is p2, x is p3 => {x is p5};",
      // you can add new properties at any level of `if-then`
      "if x : x is p1 => {if x is p2 => {if x is p3 => {x is p5}}};",
    ],
    debug: false,
    print: false,
  },
  {
    name: "not",
    code: ["if x : x is not q0 => {x is not q0};"],
    debug: false,
    print: false,
  },
  {
    name: "knows",
    code: [
      // know can be used in many cases:
      // 1. add new properties to a declared operator
      // 2. assume something
      // 3. declare something first, then add properties to it by 'knowing' them
      "know y is p, z is q;",
      "y is p, q(z);",
      "x,y are p;",
      "def pq(y,z) => {};",
      "know if x,y : x is p, y is q => {pq(x,y)};",
      "pq(y,z);",
      // `know` also works for `if-then`s (for all)
      "know if x,y,z: <(x,y), <(y,z) => {<(x,z)};",
    ],
    debug: false,
    print: false,
  },
  {
    name: "exist_have",
    code: [
      "exist something is p;",
      "exist pq(y,z);",
      // difference between let and have: If you let something and bind properties
      // to them, then my interpreter won't check whether actually such
      // variables with those properties actually exists.
      // If you want to `have` something, you should first prove its existence
      "have d: d is p1;",
      "have e,f: pq(e,f);",
    ],
    debug: false,
    print: false,
  },
  {
    name: "prove",
    code: [
      // prove syntax1 : prove if-then-type-fact => {your reasoning}
      "prove if x : x is p2 => {x is p} {x is p1;}",
      "know z is p3;",
      // prove syntax2: prove an operator-type-fact {your reasoning}
      "prove z is p {z is p2; z is p1;}",
    ],
    debug: false,
    print: false,
  },
  {
    name: "prove_by_contradiction",
    code: [
      "let n : n is not p;",
      // syntax: prove fact {reasoning} contradiction something-true-and-false;
      "prove_by_contradiction n is not p3 {n is p2; n is p1;} contradiction n is p;",
    ],
    debug: false,
    print: false,
  },
  {
    name: "postfix_prove",
    // allow user to 'first speaks the final result, then prove it.
    code: ["z is p2 prove {z is p3;};"],
    debug: false,
    print: false,
  },
  {
    name: "by",
    code: [
      "def x is object => {};",
      "def set(x) => {object(x)};",
      // "def x is set => {x is object};",
      "def element_of(A,B) => {} when A,B are object;",
      "def equal(A,B) <=> {if x : element_of(x,A) => {element_of(x,B)} [set_equal] , if x : element_of(x,B) => {element_of(x,A)}} when A,B are set;",
      "let A,B : A,B are set, equal(A,B), element_of(x,A);",
      "A is object;",
      // use a specific stored fact to prove, instead of letting my interpreter to
      // loop over all possibilities (in this case, my interpreter can not
      // prove element(x,B) because it is only given with x and B but
      // the related reasoning actually requires the third variable A.
      "by set_equal(A,B,x) => {element_of(x,B)};",
      "by set_equal(A,B,x);",
      "def x is empty => {if z : => {not element_of(z,x)}} when x is set;",
      "know if x, y : x,y are empty => {equal(x,y)};",
      "let s1, s2 : s1,s2 are empty;",
      "equal(s1,s2);",
    ],
    debug: false,
    print: false,
  },
  {
    name: "block",
    // Anything that happens in the local block environment does not affect block outside.
    code: ["let u,v : u,v are p3;", "{u is p2; return u is p1;}"],
    debug: false,
    print: false,
  },
  {
    name: "block2",
    code: [
      "let x1, x2 ,x3 : x2 is object; def x is object2 => {x is set};",
      `  {
      def x is object => {};
      know x1 is object;
      x1,x2 are object;
        {
          x1 is object;
          x2 is object;
          {
            def x is object => {x is object2};
            x1 is object;
            if x : x is object => {x is object2, x is set};
          }
        }
      }`,
      "x1 is object;",
      "x2 is object;",
      "if x : x is object2 => {x is set};",
    ],
    debug: false,
    print: false,
  },
  {
    name: "define_exist_1",
    code: [
      "def p(x);",
      "def q(x,y);",
      "def E(x): p(x) exist y {q(x,y)};",
      "let x;",
      "have E(x): y;", // Error: p(x) is unknown
      "know p(x);",
      "have E(x): y;", // Error: E(x) itself is unknown
      "q(x,y);",
      "know E(x);",
      "have E(x): y;", // OK
      "q(x,y);", // OK
      "E(x);", // OK
    ],
    debug: true,
    print: true,
  },
];

function runExamples() {
  for (const example of exampleList) {
    const env = new L_Env();
    if (example.debug) {
      console.log(example.name);
      runStrings(env, example.code, example.print);
    }
  }
}

runExamples();
