import { L_Env } from "./L_Env.ts";
import { RType } from "./L_Executor.ts";
import * as L_Executor from "./L_Executor.ts";
import { L_Scan } from "./L_Lexer.ts";
import * as L_Parser from "./L_Parser.ts";
import { setTheory } from "./tao_analysis_one.ts";

// Aristotle induction
const testList0 = [
  "def obj(x) => {};",
  "def set(x) => {obj(x)};",
  "def obj2(x) => {set(x)};",
  "let y : y is set;",
  "def z is set2 <=> {set(z)};",
  "set2(y);",
  "set2(y);",
];

const testList1 = [
  "def obj(x) => {};",
  "def obj2(x) => {};",
  "def x is p2 <=> {obj(x), obj2(x)} ",
  "let y : obj(y);",
  "if  x : obj2(x) => {p2(x)};",
  "if : y is obj2 => {y is p2};",
];

// {
//   let x;
//   know obj2(y);
//   check p2(y);
// }

const testList2 = [
  "def obj(x) => {};",
  "def obj0(x) => {};",
  "know obj0(#x);", // know #x is obj0;
  "def x is obj2 <=> {obj(x)} ;",
  "def x is obj3  => {};",
  "def x is obj4  => {obj3(x)};",
  "let EMPTY_SET;",
  "def x is inf  => {obj3(x)};",
  // [if] obj3
  // #x : inf(#x); obj(#x)
  "prove if x : obj(x) => {obj3(x)} {}", // unsuccessful prove
  "prove if x : obj(x) => {obj3(x)} {know obj4(x);}",
];

const testList3 = [
  "def obj(x) => {};",
  "def obj2(x) <=> {obj(x)} ;",
  "def x is obj3  <=  {obj(x), obj2(x)} ; ",
  "def x is obj4 <= {} ;",
  // "prove if x :  => obj2(x) {}", // unsuccessful prove
  // "prove if x :  obj(x), obj3(x) => obj2(x) {}", // obj3 is useless
];

const testList4 = [";;;\n\n;;"];

const testList5 = [
  "def x is p1 => {};",
  "def x is p3 => {};",
  "def p2(x) <=> {p1(x)} ;",
  "let y : y is p2, y is p3;",
  "y is p1;",
  // "def p3 x : p2(x);",
];

// Obsolete
const testList6 = [
  "def p1(x)  => {};",
  // "exist exist-p1(x) <=> p1(x);", // can be used as a "stronger" version of def.
  // "let y : p1(y);",
  // "have x : exist-p1(x);", // unsuccessful have
  // "exist-p1(y);", // we declare and exe exist-fact by exactly using Opt code.
  // "have z : exist-p1(z);",
];

const testList7 = [
  "def p1(x) => {};",
  "def p2(x) <=> {p1(x)};",
  "def p3(x) <=> {p2(x)};",
  "let y : p1(y);",
  "p3(y);", // unknown
  // "p3(y) by {p2(y)};",
  "p3(y);",
  "know not p1(y);",
  "p1(y);",
];

const testList8 = [
  "def obj(x)  => {};;",
  "def obj2(x,y) <=> {obj(x), obj(y)};",
  "let x,y : obj(x), obj(y);",
  "obj(x), obj(y);",
  "obj2(x,y);",
  // "know obj(y);",
  // "obj(y);",
  // "obj2(x,y);",
];

const testList9 = ["def obj(x)  => {};", "let x : not obj(x);", "not obj(x);"];

// obsolete
const testList10 = [
  "def p1(x) => {};",
  // "def p2(x) <=> p1(x);",
  // "def p3(x) <=> p2(x);",
  // "let x : not p3(x);",
  // "assume_by_contradiction p1(x) {p2(x);} {p3(x)}",
];

const testList11 = [
  "def p0(x) <= {};",
  "def p1(x) <= {p0(x)};",
  "let x : p0(x);",
];

const testList12 = ["def p1(x) => {};"];

const testList13 = [
  "def obj(x) => {};",
  "def obj2(x) => {obj(x)} ;",
  "def obj3(x) => {obj2(x)};",
  "def obj4(x) => {obj(x)} ",
  "prove if x : obj3(x) => {obj(x)} {obj2(x); obj(x);};",
  // "prove obj4(#x) {obj2(x); obj(x);}", // obsolete
];

const testList14 = [
  "def obj(x) => {};",
  "def obj2(x) => {x is obj};",
  "let x : x is obj;",
  "let a,b,c : a,b,c are obj;",
  "let q,w,e : w,e are obj;",
  "know a is obj;",
  "know b,c are obj2, obj2(x), w,e are obj2;",
];

const testList15 = [
  "def obj(x) => {};",
  // "know obj(#x);", obsolete
  "obj(#y);",
  "let x,y,z : ;",
  "x,y,z are obj;",
];

const testList16 = [
  "def obj(x) => {};",
  "let x;",
  "def x is obj2 => {x is obj};",
  "know if x : obj(x) => {obj(x)};",
  "def obj3() => {obj2(x)} ;",
  "let x2;",
  "know if obj(x2) => {obj2(x2)};",
  // "x2 <= obj(x2);",
];

const testList17 = [
  "def x is obj0 <=> {};",
  "def x is obj => {};",
  "def x is obj2 <=> {};",
  "def x is obj3 <= {x is obj}  ;",
  "let x: x is obj0, x is obj, x is obj2, x is obj3;",
  "let a;",
  "if => {a is obj0};",
  "iff z: obj0(a), z is obj <=> {};",
  "only_if obj0(a) <= {};",
];

const testList18 = [
  "def obj0(x) => {};",
  "def obj11(x) <=> {};",
  "let 1,2,3,4;",
  "1,2,3,4 are obj0;",
  "1,2,3,4 are obj11;",
  "know obj0(#x);",
  "1,2,3,4 are obj0;",
];

const testList19 = [
  "def obj0(x) => {};",
  "def obj1(x) => {x is obj0};",
  "def obj2(x) => {obj1(x)};",
  "let x : obj2(x);",
  "x is obj0 prove {x is obj1;};", // If we put by at the end, then it's a declarative way of proving: instead of procedurally prove a result, we now declare a result at beginning and then prove it.
];

const setTheory1 = [
  "def object x : => {};",
  // "def set if x : => {};",
  // "def in if x,A : A is set => {};",
  // "def = iff A,B : set(A), set(B) <=> {if x : in(x,A) => {in(x,B)}, if x : in(x,B) => {in(x,A)}}",
];

const testList20 = [
  "def object(x) <=> {};",
  "def obj2(x) => {};",
  // "def = A,B : obj(A), obj(B);",
  // "def deduce only_if x : x is obj <= ;",
  "def eq(A,B)  <=> {A,B are obj2} ;",
];

const testList21 = [
  "def obj0( x) => {};",
  "def obj1(x) => {};",
  "def obj2(x) => {};",
  "def obj3(x,y )  => {};",
  "let a,b;",
  // "know if x : x,b are obj0 => x is obj1;",
  "know if x : x,b are obj1 => {if : obj3(x,a) => {x is obj2}};",
];

const testList22 = [
  "def x is obj0 => {};",
  "def x is obj1 => {};",
  "def obj2(x,y) <=> {x,y are obj1};",
  "def obj3(x,y) => {x,y are obj1};",
  "def obj4(x,y) <= {x,y are obj1};",
];

const testList23 = [
  "def x is object => {};",
  "def x is set => {};",
  "def in(x,A) => {} ",
  "def =(A,B) <=> {if x : in(x,A) => {in(x,B)}, if x : in(x,B) => {in(x,A)} };",
  "let A,B : A,B are set, if x : in(x,A) => {in(x,B)}, if x : in(x,B) => {in(x,A)};",
  "=(A,B);",
  "if x : p(x), p(y), p2(x,y) => q(x,y)",
  // {let x; know p(x); p(y); know p2(x,y); q(x,y); return q(x,y);}
];

const testList24 = [
  "def x is object => {};",
  "def x is obj => {};",
  "def x is object1 => {x is object};",
  "def x is object2 => {x is object1};",
  "def x is object3 => {x is object2};",
  "let y,z,a;",
  "y is object1;",
  "know #x is object;",
  "if :  x is object2 => {if :  x is object1 => {x is object}};",
  "z is object;",
  "if  : y is object2 => {y is object};",
  "if : z is object2 => {if : => {z is object1} } ;",
  "if : a is object3 => {if : => {a is object} };",
  "if : a is object3 => {if : => {a is obj} };",
];

const testList25 = [
  "def x is object => {};",
  // "let x : x is object;",
  // "x is object;",
  // "y is object;",
  "def object2(x,y) <=>  {x,y are object };",
  "let a,b : not object(a), not object(b);",
  "object2(a,b);",
  "assume_by_contradiction object2(a,b) {object(b);} {object(b)}",
  // "let c : not object(c);",
  // "object(c);",
  // "not object(c);",
];

const testList26 = [
  "def x is object => {};",
  "def x is object2 => {object(x)};",
  "know if x is object => {x is object2};",
];

const testList27 = [
  "def x is object => {};",
  "let x : x is object;",
  "x is object;",
  "let y; ",
  "y is object;",
];

const testList28 = [
  "def x is object => {};",
  "def x is object2 => {object(x)};",
  // "def x is object3 => object2(x);",
  "let x,y,z : x is object, ;",
  "x is object;",
  // "y is object;",
  "z is object;",
  "know if z : => {z is object};",
  "y is object;",
  "z is object;",
];

const testList29 = [
  "def x is object => {};",
  "def x is object0 => {};",
  "def x is object2 => {object(x)};",
  "def x is object3 => {x is object2};",
  "if z : z is object2 => {z is object};",
  "if z : z is object => {z is object};",
  "if z : => {z is object0};",
  "let z : z is object0;",
  "z is object0;",
  "if z : z is object3 => {z is object};",
  "if z : => {if : => { if : z is object2 => {z is object}}} ;",
];

const testList30 = [
  "def x is object1 => {};",
  "def x is object2 => {};",
  "def x is p3 => {x is object2};",
  "def x is object12 => {};",
  "know if x : x is object1, x is object2 => {x is object12};",
  "let a,b,c,d : a is object1, a is object2, c is object1, d is object2;",
  "a is object12;",
  "b is object12;",
  "c is object12;",
  "d is object12;",
  "if z : => {if : z is object1, z is p3 => {z is object2, z is object12}};",
];

const testList31 = [
  "def z is p => {};",
  "def z is p1 => {};",
  "def z is p2 <=> {z is p1};",
  "def z is p3 <= {z is p2};",
  "if x : x is p => {x is p2};",
  "if x : x is p1 => {x is p2};",
  "let x : x is p1;",
  "x is p3;",
  "x is p2; x is p3;",
  // " x is p3 by {x is p1; x is p2;} ;",
];

const testList32 = ["def x is p => {};", "let x ; know x is p;"];

const testList33 = [
  "def x is p => {};",
  "def x is p1 => {};",
  "def x is p2 <=> {x is p1};",
  "def x is p3 <= {x is p2};",
  "if x : x is p => {x is p2};",
  "if x : x is p1 => {x is p2};",
  "let x : x is p1;",
  "x is p3;",
  "x is p2; x is p3;",
  // " x is p3 by {x is p1; x is p2;} ;",
];

const testList34 = [
  "def x is p => {}; def x is p1 => {}; def x is p2 => {};",
  "know if x : x is p => {if : x is p1 => {x is p2}} ;",
  "let x : x is p, x is p1;",
  "x is p2;",
];

const testList35 = [
  "def x is p => {}; def x is p1 => {}; def x is p2 =>{} ; let x : x is p1;",
  "{let x : x is p2; x is p2; x is p1;}",
  "x is p1; x is p2;",
  "{def x is p1 => {}; let x; x is p1; if x : x is p1 => {x is p1};}",
];

const testList36 = [
  "def x is p => {}; def x is p1 => {}; def x is p2 => {}; let x : x is p1;",
  "def x is p3 => {};",
  "def p4(x,a) <= {a is p2, x is p1};",
  "def x is p0 => {if a : p1(a) => {p4(x,a)} };", // very important, because x is used over for all a is p2, not a specific a.
  "know if x,a : a is p2, x is p1 => {x is p3};",
  "know if x : => { if a : x is p1, a is p1 => {x is p3} } ;",
  "know if x : => {if a : a is p1, x is p1 => {x is p2, a is p}};",
  "x is p2;", // p2
  "x is p3;", // p3
  "x is p;", // p
  "know x is p0;",
  "let a : a is p1;",
  "p4(x,a);", // very important, because x is used over for all a is p2, not a specific a.
];

const testList37 = [
  "def x is p => {}; def x is p1 => {}; def x is p2 => {}; let x : x is p1;",
  "if x : x is p => {if y : y is p2 => {y is p2, x is p,}};",
  "if a : a is p => {a is p2, x is p2};",
  "if b : b is p5 => {};",
  "if x : y is p => {};",
];

const testList38 = [
  // "def x is p => ; def x is p1 => x is p; def x is p2 => x is p1; def x is p3 => x is p2;",
  // "prove if x : x is p3 => {x is p} {x is p2; x is p1;}",
  // "prove if x : x is p2 => {x is p1} {let x;}", // Error: x double declaration
  // "prove if x : x is p2 => {x is p1} {def x is p1 =>;}", // Err: double declaration of p1
  // "prove if x : x is p2 => {x is p1} {def x is p2 => ;}", // Err: double declaration of p2
  "def x is q => {}; def x is q1 => {x is q}; def x is q2 => {x is q1}; def x is q3 => {x is q2};",
  "let x : x is q3;",
  "prove x is q {x is q2; x is q1;}",
  "prove x is q {let x; }", // Err
  "prove x is q {def x is q => ;};", // Err
  "x is q1 prove {x is q3, x is q2;};",
  "x is q1 prove {let x;};", // Err
  "x is q1 prove {def x is q1 => ;};", // Err
];

const testList39 = [
  "def x is q => {}; def x is q1 => {x is q}; def x is q2 => {x is q1}; def x is q3 => {x is q2};",
  "let x : x is q3;",
  "{x is q2; return x is q1;}",
];

const testList40 = [
  "def p1(x)  => {};",
  "let x : x is p1;",
  "exist p1(x);",
  "have y : p1(y);",
];

const testList41 = [
  "def x is q => {}; def x is q1 => {x is q}; def x is q2 => {x is q1}; def x is q3 => {x is q2};",
  "let x : x is q3;",
  "prove_by_contradiction x is q {not q2(x); not q1(x);} contradiction  not q3(x);",
];

const byList = [
  "def x is obj => {};",
  "def element_of(x,A) => {};",
  "def equal(A,B) => {if x : element_of(x,A) => {element_of(x,B)} };",
  "let x, A, B : element_of(x,A), equal(A,B);",
  "by equal(A,B) => {element_of(x,B)};",
];

const testList42 = [
  "def x is q => {} ;",
  // "def x is q0 => {x is q} [q0_def];",
  "def x is q0 => {x is q} ;",
  "let x;",
  "know x is q;",
  "if y : y is q0 => {y is q} [q0_fact1];",
  "know if y : y is q0 => {x is q} [q0_fact2];",
  "let z : if t : t is q0 => {z is q}[q0_fact3];",
  "if : => {if z : z is q0 => {z is q}[q0_fact4] };",
  "know z is q0;",
  "by q0_fact1(z) => {z is q};",
  "def x is p2 => {};",
  "def x is q1 => {if y : y is p2 => {y is q}[q1_then_p2] };",
];

const testList43 = [
  "def x is p => {}; def x is p1 => {x is p}; def x is p2 => {x is p1}; ",
  "let a,b,c : a,b,c are p2;",
  "a,b,c are p2;",
  "prove a is p {a is p1;}",
];

const 三段论 = [
  // Introduce a concept "mortal"
  // you can also write def mortal(something) => {};
  "def something is mortal => {};",
  // Introduce a concept "human", "human" has property that "human is mortal"
  "def something is human => {something is mortal};",
  // Introduce a variable "Socrates", "Socrates" has property that "Socrates is human"
  "let Socrates : Socrates is human;",
  // Check: "Socrates is mortal"
  "Socrates is mortal;",
  // Introduce a variable "god", "god" has property that "god is not mortal"
  "let god : god is not mortal;",
  // prove by contradiction: to show "god is not human", we assume "god is human"
  // then we get {god is mortal;} which leads to contradiction:
  // "god is mortal" "god is not mortal" is valid at the same time.
  "prove_by_contradiction god is not human {god is mortal;} contradiction god is mortal;",
];

const testList44 = [
  "def x is object => {};",
  "let x ;",
  "{def x is object => {}; know x is object; {x is object;} }",
];

const testList45 = [
  "def x is object => {};",
  "let x : x is object2;",
  "know x is object2;",
  "let a,b: object(a,b);",
];

const testList46 = ["def x is object => {};", "let a,b : a,b are object;"];

const testList47 = [
  "def object(x) => {};",
  "def object2(x) <= {object(x)};",
  "def object3(x) <=> {object2(x)};",
  "if x : x is object3 => {x is object2};",
  "iff x : x is object3 <=> {x is object2};",
];

const testList48 = [
  "def obj(x) => {};",
  "def obj2(x) => {obj(x)}[ha];",
  "if x : x is obj2 => {x is obj}[ha2];",
];

const testList49 = [
  "def obj(x) => {};",
  "def obj2(x,y): x is obj, y is obj => {};",
];

const testList50 = [
  "def obj(x) => {};",
  "def obj2(x,y) <= { or{x is obj, y is obj} };",
  "let a,b,c: a is obj;",
  // "or{b is obj, a is obj};",
  "obj2(a,b);",
  "or{c is obj, not obj(c)};",
];

const testList51 = [
  "def obj(x) => {};",
  "def obj2(x) => {};",
  "def obj3(x) => {};",
  "def obj4(x,a) => {};",
  "know if x : obj(x) => {x is obj2, if a : obj3(x),obj4(x,a) => {obj(x)}};",
  "know if x : obj(x) => {if : x is obj2 => {obj3(x)}};",
];

const testsDict: { [s: string]: [string[], boolean] } = {
  testList: [testList0, false],
  testList1: [testList1, false],
  testList2: [testList2, false],
  testList3: [testList3, false],
  testList4: [testList4, false],
  testList5: [testList5, false],
  testList6: [testList6, false],
  testList7: [testList7, false],
  testList8: [testList8, false],
  testList9: [testList9, false],
  testList10: [testList10, false],
  testList11: [testList11, false],
  testList12: [testList12, false],
  testList13: [testList13, false],
  testList14: [testList14, false],
  testList15: [testList15, false],
  testList16: [testList16, false],
  testList17: [testList17, false],
  testList18: [testList18, false],
  testList19: [testList19, false],
  testList20: [testList20, false],
  testList21: [testList21, false],
  testList22: [testList22, false],
  testList23: [testList23, false],
  setTheory1: [setTheory1, false],
  testList24: [testList24, false],
  testList25: [testList25, false],
  testList26: [testList26, false],
  testList27: [testList27, false],
  testList28: [testList28, false],
  testList29: [testList29, false],
  testList30: [testList30, false],
  testList31: [testList31, false],
  testList32: [testList32, false],
  testList33: [testList33, false],
  testList34: [testList34, false],
  testList35: [testList35, false],
  testList36: [testList36, false],
  testList37: [testList37, false],
  testList38: [testList38, false],
  testList39: [testList39, false],
  testList40: [testList40, false],
  testList41: [testList41, false],
  setTheory: [setTheory, false],
  testList42: [testList42, false],
  testList43: [testList43, false],
  testList44: [testList44, false],
  testList45: [testList45, false],
  testList46: [testList46, false],
  byList: [byList, false],
  三段论: [三段论, false],
  testList47: [testList47, false],
  testList48: [testList48, false],
  testList49: [testList49, false],
  testList50: [testList50, true],
};

export function testCode() {
  for (const testList in testsDict) {
    const env = new L_Env();
    const exprs = testsDict[testList];
    if (exprs[1] === false) continue;

    for (let i = 0; i < exprs[0].length; i++) {
      const expr = exprs[0][i];
      const out = runExprs(env, expr);
      if (out === undefined) {
        env.printClearMessage();
        continue;
      }
    }

    // env.printAllStoredFacts();
    // env.printClearMessage();
    // env.printBys();
  }
}

export function runExprs(env: L_Env, expr: string) {
  try {
    const tokens = L_Scan(expr);
    const nodes = L_Parser.parseUntilGivenEnd(env, tokens, null);
    // const nodes = L_Parser.L_StmtsParse(env, tokens);
    if (nodes === undefined) {
      return undefined;
    }
    const result: RType[] = [];
    for (const node of nodes) {
      const out = L_Executor.nodeExec(env, node);
      result.push(out);
    }
    console.log(`-----\n***  source code  ***\n${expr}\n`);
    console.log("***  results  ***\n");
    env.printClearMessage();
    console.log();

    return result;
  } catch {
    return undefined;
  }
}

testCode();
