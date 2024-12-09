import { ExampleItem } from "./L_Structs";
import { L_Env } from "./L_Env";
import { runStrings } from "./L_Runner";
import * as fs from "fs";

export const exampleList: ExampleItem[] = [
  {
    name: "define basic concepts: object, set",
    code: ["def object(x); def set(x);", "know if x: set(x) {object(x)};"],
    test: ["{let a: set(a); object(a);}"],
    debug: true,
    print: false,
    runTest: false,
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
    debug: true,
    runTest: false,
    print: false,
  },
  {
    name: "empty set",
    code: ["let EMPTY_SET: set(EMPTY_SET); know if x: {not in(x,EMPTY_SET)};"],
    test: [
      "// here we must use _x to avoid conflict with x;",
      "{ let x;  not in(x, EMPTY_SET)[x];  if _x:  {not in(_x,EMPTY_SET)[_x]}; }",
    ],
    debug: true,
    runTest: false,
    print: false,
  },
  {
    name: "singleton",
    code: [
      "know if x, a: in(x, \\singleton{a})  {equal(x, a)};",
      "know if x, a: equal(x,a)  {in(x, \\singleton{a})};",
    ],
    test: [
      `{let a, b;
      know set( \\singleton{a});
      let x;
      know in (x, \\singleton{a});
      equal(x,a);
      in(x, \\singleton{a}); 
      if _x, _a: equal(_x,_a)  {in(_x, \\singleton{_a})[_x, _a] };}`,
    ],
    debug: true,
    runTest: false,
    print: false,
  },
  {
    name: "pair",
    code: [
      "know if x, a, b: in(x, \\pair{a,b}) { if :  not equal(x, b) {equal(x, a)} , if : not equal(x, a) {equal(x, b)} } ;",
      "know if x, a, b : in(x,a) {in(x, \\pair{a,b})};",
      "know if x, a, b : in(x,b) {in(x, \\pair{a,b})};",
    ],
    test: [
      "{let x, a, b : in(x,a); in(x, \\pair{a,b})[x,a,b]; let y,c,d : in(y, \\pair{c,d}), not equal(y,c); equal(y,d)[y,c,d;]; }",
    ],
    debug: true,
    runTest: false,
    print: false,
  },
  {
    name: "pair-wise union",
    code: [
      "know if x, y: set(x), set(y) {if z: in(z, x) { in(z , \\union{x, y})}, if z : in(z, y) {in(z, \\union{x,y})} };",
      "know if x, y, z: in(z , \\union{x, y}) {if :  not in(z, x) {in(z, y)}, if : not in(z, y) {in(z, x)}};",
    ],
    test: [
      `{let a,b: set(a), set(b);
      let x: in(x,a); 
      in(x, \\union{a,b}) [a,b; x];
      in(x, \\union{a,b});};
      let y, c, d: in(y, \\union{c,d}); know not in(y, c); in(y, d)[c,d,y;];`,
    ],
    debug: true,
    runTest: false,
    print: false,
  },
  {
    name: "subset",
    code: [
      "def subset(x,y);",
      "know if A,B: subset(A,B) {if x: in(x,A)  {in(x,B)} };",
      "know if A,B: if x: in(x,A)  {in(x,B)}  {subset(A,B)};",
    ],
    test: [
      `{let A,B,C,D,E,F;
      know subset(A,B);
      let x: in(x,A);
      in(x,B); // Unknown
      in(x,B)[A,B;x]; // True
      in(x,B);}`,
    ],
    debug: true,
    runTest: false,
    print: false,
  },
  {
    // not tested yet.
    name: "axiom of specification",
    code: [
      "let_composite \\subset_with_property{A,P}: set(A), is_property(P);",
      "know if A, P: is_property(P), set(A) {subset(\\subset_with_property{A,P}, A)};",
    ],
    test: [
      "{def p(x); is_property(p); let x: set(x); subset(\\subset_with_property{x,p}, x)[x,p];}",
    ],
    debug: true,
    runTest: false,
    print: false,
  },
  {
    name: "intersection",
    code: [
      // \frac{a}{b} \intersection(a,b)  $ a - b $
      "know if x, a, b: a is set, b is set , in(x,a), in(x,b) {in(x, \\intersection{a,b}) };",
      "know if x, a, b: set(a), set(b) , in(x, \\intersection{a,b}) { in(x,a), in(x, b) };",
    ],
    test: [
      `let A, B: set(A), set(B);
      let x;
      know in(x,A), in(x,B); in(x, \\intersection{A,B})[x,A,B];
      if X: in(X,A), in(X,B) { in(X, \\intersection{A,B})[X,A,B] } ;  
      if X: in(X, \\intersection{A,B}) { in(X,A)[X,A,B], in(X, B)[X,A,B] }; `,
    ],
    debug: true,
    runTest: false,
    print: false,
  },
  {
    name: "difference",
    code: [
      "let_composite \\difference{a,b}: set(a) ,set(b);",
      "know if x, a, b: set(a), set(b) , in(x,a), not in(x,b) {in(x, \\difference{a,b}) };",
    ],
    debug: true,
    print: false,
  },
  {
    name: "replacement",
    code: [
      // TODO 1. equal here should  be =  2. I should introduce {} into let_composite
      `let_composite \\replacement{a,p}: set(a), is_property(p), if x, a: set(a), in(x,a) {if y1, y2 : p(x, y1), p(x, y2) {equal(y1, y2)} }; `,
      `let_composite \\replacement_var{z,a,p}: ;`,
      `know if z, a, p: set(a), is_property(p), if x, a: set(a), in(x,a) {if y1, y2 : p(x, y1), p(x, y2) {equal(y1, y2)} }, in(z, \\replacement{a,p}) {
        p(\\replacement_var{z,a,p}, z)
      };`,
      `know if z, a, p: set(a), is_property(p), if x, a: set(a), in(x,a) {if y1, y2 : p(x, y1), p(x, y2) {equal(y1, y2)} }, p(\\replacement_var{z,a,p}, z){ 
        in(z, \\replacement{a,p})
      };`,
    ],
    debug: true,
    print: true,
  },
  {
    name: "regularity",
    code: [
      // "def either_not_set_or_disjoint_from_given_set(x,A);",
      // "def disjoint(A,B);",
      // "know if x: disjoint(A,B) => {if x: in(x,A) => {not in(x,B)} , if x: in(x,B) => {not in(x,A)}};",
      // "know if x: in(x,A), either_not_set_or_disjoint_from_given_set(x,A) => {if set(x) => {disjoint(x,A)}, if not disjoint(x,A) => {not  set(x)} };",
      // "know if A: set(A), not equal(A, EMPTY_SET) => {exist either_not_set_or_disjoint_from_given_set(x,A) } ;",
    ],
    debug: false,
    print: true,
  },
  {
    name: "natural number",
    code: [
      "def natural(x);",
      "def =(x,y);",
      " let 0: 0 is natural;",
      "let_composite \\++{n}: n is natural;",
      " know if n: n is natural => {\\++{n} is natural}; ",
      "know if x: => {not =(0, \\++{x}) }",
      "know if x,y: =(x,y) => {=(\\++{x}, \\++{y})};",
      "know if x,y: =(\\++{x}, \\++{y}) => {=(x,y)};",
      "know if P: is_property(P), P(0), if n: n is natural, P(n) => {P(\\++{n})} => {if n is natural => {P(n)}};",
      "let_composite \\+{x,y};",
      "know \\+{x,y} = \\+{y,x};",
      "know \\+{0,x} = \\+{x,0};",
    ],
    debug: false,
    print: true,
  },
];

function runExamples(toJSON: boolean) {
  const env = new L_Env();
  for (const example of exampleList) {
    if (example.debug) {
      if (example.print) {
        console.log(example.name);
      }
      runStrings(env, example.code, example.print);
      if (example.test !== undefined && example.runTest) {
        runStrings(env, example.test, example.print);
      }
    }
  }
  if (toJSON) envToJSON(env, "env.json");
}

runExamples(false);

export function envToJSON(env: any, fileName: string) {
  const out = env.toJSON();
  const jsonString = JSON.stringify(out, null, 2);

  fs.writeFileSync(fileName, jsonString, "utf8");

  return out;
}
