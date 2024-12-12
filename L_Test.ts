import { ExampleItem } from "./L_Structs";
import { L_Env } from "./L_Env";
import { runStrings } from "./L_Runner";
import * as fs from "fs";

const exampleList: ExampleItem[] = [
  {
    name: "define subset",
    code: [
      "def set(x); def subset(A,B); def in(x,A);",
      "know if A,B: subset(A,B) => {if x: in(x,A) => {in(x,B)} };",
      "know if A,B: if x: in(x,A) => {in(x,B)} => {subset(A,B)};",
      "let A,B,C,D,E,F;",
      "know subset(A,B);",
      "let x: in(x,A);",
      "in(x,B);", // Unknown
      "in(x,B)[A,B;x];", // True
      "in(x,B);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "macro",
    code: ["def p(x); def q(x,y);", "macro x v p(v);", "let x;", "p(x);"],
    debug: false,
    print: true,
  },
  {
    name: "opt_with_checkVars",
    code: [
      "def subset(x,y); def in (x,A); ",
      "know if x,A,B: subset(A,B), in(x,A) => {in(x,B)}; ",
      "let y,C,D, z: in(y,C), subset(C,D); ",
      // "in(x,A);",
      "in(y,D)[y,C,D];",
      "in(z,C);",
      "in(y,C);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "test_known",
    code: ["def p(x);", "let y: p(y);", "know if x : => {p(x)};"],
    debug: false,
    print: true,
  },
  {
    name: "continuous",
    code: [
      "def point_wise_continuous(f,x);",
      "def continuous(f);",
      "def in_domain(x);",
      "know if f: if x : in_domain(x) => {point_wise_continuous(f,x)} => {continuous(f)};",
      "let f;",
      "know if x : in_domain(x) => {point_wise_continuous(f,x)};",
      "continuous(f);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "known if req => opt must satisfy: req does not contain if-then-type fact that has opt as onlyIf",
    code: [
      "def p(x);",
      "def q(x);",
      "know if y: if x : => {p(y)} => {p(y)};",
      "know if y: if x: => {if z: => {p(y)}} => {p(y)};",
    ],
    debug: false,
    print: true,
  },
  {
    name: "prove 1",
    code: [
      "def p(x); def p2(x); def p3(x);",
      "know if x: p(x) => {p2(x)}; know if x: p2(x) => {p3(x)};",
      "prove if x: p(x) => {p3(x)} {p2(x);};",
      "let x: p(x);",
      "p3(x);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "三段论",
    code: [
      "def something is mortal;",
      "def something is human; know if x: x is human  {x is mortal};",
      "let Socrates : Socrates is human;",
      "Socrates is  mortal;",
      "let god :  not mortal(god);",
      "not human(god);",
      "prove_by_contradiction  not  human(god) {god is mortal;}  god is mortal;",
      "not human(god);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "cond",
    code: [
      "def p(x); def q(x): p(x);",
      "let a: q(a);",
      "q(a);", // still not true, because p(x) is not satisfied.
      "know p(a);",
      "q(a);", // true
    ],
    debug: false,
    print: true,
  },
  {
    name: "def block",
    code: [
      "def p(x); def q(x) {if x: q(x) => {p(x)}};",
      "let a: q(a);",
      "p(a);",
      // "q(a);", // still not true, because p(x) is not satisfied.
      // "know p(a);",
      // "q(a);", // true
    ],
    debug: false,
    print: true,
  },
  {
    name: "namedKnownToCheck",
    code: [
      "def p(x); def q(x); def t(x);",
      "let a: p(a);",
      "know [_1] if x: p(x) => {q(x)};",
      "by _1(a);",
      "q(a);", // 理论上即使没有 by _1(a), q(a) 也是true
      "let [_2] b: if x : x is p => {t(b)};", // 这里起到了“如果存在...，则..."的作用
      "t(b);", // unknown
      "by _2(a);",
      "t(b);", // 如果没有 by _2(a), 那就没有 t(b)
      "t(b)[a];", // 也能证明t(b)
      "[_3] if x: p(x) => {q(x)};",
      "by _3(a);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "check if-then using literally-the-same if-then",
    code: [
      "def p(x); def q(x); def t(x,y);",
      "know if x,y: t(x,y) => {q(x)};",
      "if x,y: t(x,y) => {q(x)};",
      "know if x,y: t(x,y) => {q(x)} ;",
      "if : => {if x,y: t(x,y) => {q(x)} };",
    ],
    debug: false,
    print: true,
  },
  {
    // outdated.
    name: "exist",
    code: [
      // 如果要加语法糖的话，在这里把一个var fix住，然后进行后续的证明，是个好语法糖
      "def p(x); def q(x); def t(x,y); def t_y(x); know if x :t(x,y) => {t_y(x)};",
      "let x, y: t(x,y);",
      "t_y(x);",
      "exist(t_y)[x];",
      "know if exist(t_y) => {q(y)};",
      "q(y);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "know exist",
    code: [
      "def p(x); def q(x); def t(x,y); def t_y(x); know if x :t(x,y) => {t_y(x)};",
      "know exist(p);",
      "exist(p);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "have",
    code: ["def p(x); know exist(p); have x: p(x);"],
    debug: false,
    print: true,
  },
  {
    name: "prove exist",
    code: ["def p(x); prove exist(p) {let x: p(x); exist(p)[x];}"],
    debug: false,
    print: true,
  },
  {
    name: "different defs",
    code: [
      `def p(x); def x is p1; def q(x,y);`,
      `def p2(x) {if x: x is p1 => {x is p2} }`,
      "let x: p1(x);",
      "p2(x);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "check",
    code: [
      "def p(x); def q(x); def t(x,y);",
      "let y; know if a: p(a) => {t(y,a)};",
      "let x: p(x);",
      "t(y,x);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "know not exist",
    code: [
      "def p(x); def q(x);",
      "know not exist(p);",
      "exist(p);",
      "not exist(p);",
      "if x: => {not p(x)};",
    ],
    debug: false,
    print: true,
  },
  {
    name: "test \\ parser",
    code: [
      "def p(x);",
      `let \\f{i}[i is p]: \\f{i}[i is p] is p;`,
      "\\f{i}[i is p] is p;",
    ],
    debug: false,
    print: true,
  },
  {
    name: "test \\ checker",
    code: [
      "def p(x); def >(i,j);",
      `let \\f{i}: \\f{i}[>(i,0)] is p;`,
      "let i,0: >(i,0);",
      "\\f{i} is p;",
      "\\f{2} is p;",
    ],
    debug: false,
    print: true,
  },
  {
    name: "test let#",
    code: [
      "def p(x); def >(i,j);",
      "let# #i: p(#i);",
      "know \\f{#i} is p;",
      "let i;",
      "\\f{i} is p;",
      "know p(i);",
      "\\f{i} is p;",
      "let #i, #j: #i > 0, #j > 0;",
      "\\A{#i,#j} is_element_of A;",
      // `let \\f{#i}: \\f{#i} is p;`,
      // "let i: p(i);",
      // "\\f{i} is p;",
    ],
    debug: false,
    print: true,
  },
  {
    name: "define element of matrix",
    code: [
      "def element_of(e,A); def <(i,j); let A,0;",
      "let# #i, #j: <(0,#i), <(0,#j);",
      "know element_of(\\A{#i,#j} ,A );",
      "let i,j: <(0,i), <(0,j);",
      "element_of(\\A{i,j}, A );",
    ],
    debug: false,
    print: true,
  },
  {
    name: "union",
    code: [
      "def set(A); def element_of(x,A);",
      "let# #A, #B: set(#A), set(#B);",
      "know if x: element_of(x,A) => {element_of(x, \\union{A,B})};",
      "know if x: element_of(x,B) => {element_of(x, \\union{A,B})};",
      "let x,A,B: set(A), set(B), element_of(x,A);",
      "element_of(x,\\union{A,B});",
    ],
    debug: false,
    print: true,
  },
  {
    name: "{}",
    code: ["def p(x); {let a: p(a); p(a);}"],
    debug: false,
    print: true,
  },
  {
    name: "def singleton set",
    code: [
      "def set(x); def in(x, A); def equal(x, y);",
      "let a;",
      "know \\singleton{a} is set, if x: in(x, \\singleton{a}) => {equal(a, x)};",
      // "know if x: x is set, \\(x, \\sing)",
      "let A: in(A, \\singleton{b});",
      "equal(A,a)[A];",
      "know in (A, \\singleton{a});",
      "equal(A,a)[A];",
    ],
    debug: false,
    print: true,
  },
  {
    name: "def singleton set 2",
    code: [
      "def set(x); def in(x, A); def equal(x, y);",
      "know if _x, _a: in(_x, \\singleton{_a}) => {equal(_x,_a)};",
      "let a,x: in(x, \\singleton{a});",
      "equal(x,a);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "\\union{x,y}",
    code: [
      "def set(x); def in(x, A); def equal(x, y);",
      // "composite \\union{x,y}: x is set, y is set;",
      "let a,b: a is set, b is set;",
      "know if _x, _y: set(_x), set(_y) => {if _z: in(_z, _x) => { in(_z , \\union{_x, _y})}, if _z : in(_z, _y) => {in(_z, \\union{_x,_y})} };",
      "let x: in(x,a); ",
      "in(x, \\union{a,b}) [a,b;x];",
    ],
    debug: false,
    print: true,
  },
  {
    name: "composite",
    code: [
      "def set(x); def in(x, A); def equal(x, y);",
      // "def_composite \\union{x,y}: x is set, y is set;",
      "let a,b: a is set, b is set;",
      "know if _x, _y: set(_x), set(_y) => {if _z: in(_z, _x) => { in(_z , \\union{_x, _y})}, if _z : in(_z, _y) => {in(_z, \\union{_x,_y})} };",
      "let x: in(x,a); ",
      "in(x, \\union{a,b})[a,b;x];",
    ],
    debug: false,
    print: true,
  },
  {
    name: "exist",
    code: [
      "def set(x); def in(x, A); def equal(x, y);",
      "let x: set(x);",
      "know exist set(x);",
      "exist set(x);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "composite symbol",
    code: ["def p(x); ", "let x;", " know p(x);", " p(x);"],
    debug: false,
    print: true,
  },
  {
    name: "test L_Symbol",
    code: [
      "def set(x); let x: set(x);",
      // "know set(x);",
      "set(x);",
      "know set(\\frac{1,2});",
      "set(\\frac{1,2});",
    ],
    debug: false,
    print: true,
  },
  {
    name: "test if",
    code: [
      "def set(x); let x: set(x);",
      "know if x, \\frac{a,b}[a,b] : set(x) {set(x)};",
      "def set2(x); know if x: set(x) {set2(x)};",
      "let y: set(y);",
      "set2(y);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "define basic concepts: object, set",
    code: ["def object(x); def set(x);", "know if x: set(x) {object(x)};"],
    test: ["{let a: set(a); object(a);}"],
    debug: false,
    print: true,
    runTest: false,
  },
  {
    name: "test if2",
    code: [
      "def set(x); def set2(x); let x: set(x);",
      "know if x,y: set(x), set(y) {set2(x), set2(y)};",
      "let a,b: set(a), set(b);",
      "set2(a);",
      "set2(a)[a,b];",
    ],
    debug: false,
    print: true,
  },
  {
    name: "equality of sets",
    code: [
      "def equal(a,b); def in(x,a);",
      "know if a,b: set(a), set(b), equal(a,b)  {if x: in(x,a) {in(x,b)}, if x: in(x,b) {in(x,a)}};",
      "know if a,b: set(a), set(b), if x: in(x,a) {in(x,b)}, if x: in(x,b) {in(x,a)} {equal(a,b)};",
    ],
    test: [
      "{let a, b: set(a), set(b), equal(a,b); if x: in(x,a)  {in(x,b)[a,b;x]} , if x: in(x,b)  {in(x,a)[a,b;x]}; let x: in(x,a); in(x,b); }",
    ],
    debug: false,
    print: false,
    runTest: false,
  },
  {
    name: "singleton",
    code: [
      "know if x, a: in(x, \\singleton{a})  {equal(x, a)};",
      "know if x, a: equal(x,a)  {in(x, \\singleton{a})};",
    ],
    test: [
      "let a, b;",
      "know set(\\singleton{a});",
      "let x;",
      "know in (x, \\singleton{a});",
      "equal(x,a);",
      "in(x, \\singleton{a})[x,a]; ",
      "if _x, _a: equal(_x,_a)  {in(_x, \\singleton{_a})[_x,_a] };",
    ],
    debug: false,
    print: true,
    runTest: false,
  },
  {
    name: "pair",
    code: [
      "know if x, a, b: in(x, \\pair{a}{b}) { if not equal(x, b) {equal(x, a)} , if not equal(x, a) {equal(x, b)} } ;",
      "know if x, a, b : in(x,a) {in(x, \\pair{a,b})};",
      "know if x, a, b : in(x,b) {in(x, \\pair{a,b})};",
    ],
    test: ["let x, a, b : in(x,a); in(x, \\pair{a,b})[x,a,b]; "],
    debug: false,
    runTest: false,
    print: false,
  },
  {
    name: "opt",
    code: ["def set(x); def <(x,y); let x,y: x is set, x < y;"],
    debug: false,
    print: true,
  },
  {
    name: "test not",
    code: ["def p(x); let x: not p(x); p(x); not p(x); "],
    debug: false,
    print: true,
  },
  {
    name: "pair",
    code: [
      "def in(x,y); def equal(a,b);",
      "know if x, a, b: in(x, \\pair{a,b}) { if :  not equal(x, b) {equal(x, a)} , if : not equal(x, a) {equal(x, b)} } ;",
      "know if x, a, b : in(x,a) {in(x, \\pair{a,b})};",
      "know if x, a, b : in(x,b) {in(x, \\pair{a,b})};",
      "{let x, a, b : in(x,a); in(x, \\pair{a,b})[x,a,b]; let y,c,d : in(y, \\pair{c,d}), not equal(y,c); equal(y,d)[y,c,d;]; }",
    ],
    debug: false,
    print: true,
  },
  {
    name: "def_composite",
    code: [
      "def set(x); ",
      "def_composite \\set_prop{a,p}: set(a);",
      "is_property(set);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "/**/",
    code: [
      ` let x; /* asdf */ def p(x); /*df
      
*/ know p(x); p(x);
`,
    ],
    debug: false,
    print: true,
  },
  {
    name: "prove",
    code: [`def p(x); if x: p(x) {p(x)};`],
    debug: false,
    print: true,
  },
  {
    name: "prove",
    code: [
      `
// Define a less-than relation with transitivity
def <(x,y);
know if x,y,z: <(x,y), <(y,z)  {<(x,z)};

// Example of transitive property
let a,b,c: <(a,b), <(b,c);
<(a,c)[a,b,c];  // Proving transitivity
`,
    ],
    debug: false,
    print: true,
  },
  {
    name: "prove",
    code: [`def p(x); let x; know if x: {p(x)}; p(x);`],
    debug: false,
    print: true,
  },
  {
    name: "is_form",
    code: [
      `def p(x); def_composite \\frac{x,y}; know if x: is_form(x, \\frac{b,c}) {x is p};`,
      // "\\frac{1,2} is p;",
      "let 1,2: 1 is p;",
      "is_form(\\frac{\\frac{1,2}, 1}, \\frac{a,b}, {a is p, b is p});",
    ],
    debug: true,
    print: true,
  },
];

// \frac{i,j}
// A_{i}^{j}
// \A{i,j}
// i,j:  1 <= i ,j <= n;

function runExamples(toJSON: boolean) {
  const env = new L_Env();
  for (const example of exampleList) {
    if (example.debug) {
      console.log(example.name);
      runStrings(env, example.code, example.print);
      if (example.test !== undefined) {
        runStrings(env, example.test, example.print);
      }
    }
  }
  if (toJSON) envToJSON(env, "env.json");
}

export function envToJSON(env: L_Env, fileName: string) {
  const out = env.toJSON();
  const jsonString = JSON.stringify(out, null, 2);

  fs.writeFileSync(fileName, jsonString, "utf8");

  return out;
}

function runLiTeXFile(filePath: string) {
  try {
    const data = fs.readFileSync(filePath, "utf8");
    const env = new L_Env();
    runStrings(env, [data], true);
  } catch (err) {
    console.error("Error:", err);
  }
}

function run() {
  const args = process.argv.slice(2);
  if (!args || args.length === 0) {
    runExamples(false);
  } else {
    runLiTeXFile(args[0]);
  }
}

run();
