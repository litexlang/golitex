import { L_Env } from "./env";
import { executor, RType } from "./executor";
import { L_Storage } from "./L_Storage";
import { scan } from "./lexer";
import { parser } from "./parser";

// Aristotle induction
const testList0 = [
  "def obj(x) => ;",
  "def set(x) => obj(x);",
  "def obj2(x) => set(x);",
  "let y | y is set;",
  "def z is set2 <=> set(z);",
  "set2(y);",
  "set2(y);",
];

const testList1 = [
  "def obj(x) => ;",
  "def obj2(x) => ;",
  "def x is p2 <=> obj(x), obj2(x);",
  "let y | obj(y);",
  "if  x | obj2(y) => {p2(y)};",
];

// {
//   let x;
//   know obj2(y);
//   check p2(y);
// }

const testList2 = [
  "def obj(x) => ;",
  "def x is obj2 <=> obj(x) ;",
  "def x is obj3  => ;",
  "def x is obj4  => obj3(x);",
  "let EMPTY_SET;",
  "def x is inf  => obj3(x) when  obj(x);",
  // [if] obj3
  // #x | inf(#x); obj(#x)
  "prove if x | obj(x) => {obj3(x)} {}", // unsuccessful prove
  "prove if x | obj(x) => {obj3(x)} {know obj4(x);}",
];

const testList3 = [
  "def obj(x) => ;",
  "def obj2(x) <=> obj(x) ;",
  "def x is obj3  <=  obj(x), obj2(x) ; ",
  "def x is obj4 <= when obj(x), obj2(x);",
  // "prove if x |  => obj2(x) {}", // unsuccessful prove
  // "prove if x |  obj(x), obj3(x) => obj2(x) {}", // obj3 is useless
];

const testList4 = [";;;\n\n;;"];

const testList5 = [
  "def x is p1 => ;",
  "def x is p3 => ;",
  "def p2(x) <=> p1(x) when p3(x);",
  // "def p3 x | p2(x);",
];

const testList6 = [
  "def p1(x)  => ;",
  "exist Ex(x) <=> p1(x);", // can be used as a "stronger" version of def.
  "let y | p1(y);",
  "have x | Ex(x);", // unsuccessful have
  "Ex(y);", // we declare and exe exist-fact by exactly using Opt code.
  "have z | Ex(z);",
];

const testList7 = [
  "def p1(x) => ;",
  "def p2(x) <=> p1(x);",
  "def p3(x) <=> p2(x);",
  "let y | p1(y);",
  "p3(y);", // unknown
  // "p3(y) by {p2(y)};",
  "p3(y);",
  "know not p1(y);",
  "p1(y);",
];

const testList8 = [
  "def obj(x)  => ;;",
  "def obj2(x,y) <=> obj(x), obj(y);",
  "let x,y | obj(x), obj(y);",
  "obj(x), obj(y);",
  "obj2(x,y);",
  // "know obj(y);",
  // "obj(y);",
  // "obj2(x,y);",
];

const testList9 = ["def obj(x)  => ;;", "let x | not obj(x);", "not obj(x);"];

const testList10 = [
  "def p1(x) => ;",
  "def p2(x) <=> p1(x);",
  "def p3(x) <=> p2(x);",
  "let x | not p3(x);",
  "assume_by_contradiction p1(x) {p2(x);} {p3(x)}",
];

const testList11 = ["def p0(x) <= ;", "def p1(x) <= p0(x);", "let x | p0(x);"];

const testList12 = ["def p1(x) => ;"];

const testList13 = [
  "def obj(x) => ;",
  "def obj2(x) => obj(x) ;",
  "def obj3(x) => obj2(x);",
  "def obj4(x) => obj(x) when obj3(x);",
  "prove obj4(#x) {obj2(x); obj(x);}",
];

const testList14 = [
  "def obj(x) => ;",
  "def obj2(x) => x is obj;",
  "let x | x is obj;",
  "let a,b,c | a,b,c are obj;",
  "let q,w,e | w,e are obj;",
  "know a is obj;",
  "know b,c are obj2, obj2(x), w,e are obj2;",
];

const testList15 = [
  "def obj(x) => ;",
  "know obj(#x);",
  "obj(#y);",
  "let x,y,z | ;",
  "x,y,z are obj;",
];

const testList16 = [
  "def obj(x) => ;",
  "let x;",
  "def x is obj2 => x is obj;",
  "know if x | obj(x) => {obj(x)};",
  "def obj3() => obj(x) when obj(x);",
  "let x2;",
  "know if obj(x2) => {obj2(x2)};",
];

const testList17 = [
  "def x is obj0 <=> ;",
  "def x is obj =>;",
  "def x is obj2 <=> ;",
  "def x is obj3 <= x is obj  ;",
  "let x| x is obj0, x is obj, x is obj2, x is obj3;",
  "let a;",
  "if => {a is obj0};",
  "iff z| obj0(a), z is obj <=> {};",
  "only_if obj0(a) <= {};",
];

const testList18 = [
  "def obj0(x) => ;",
  "def obj11(x) <=> ;",
  "let 1,2,3,4;",
  "1,2,3,4 are obj0;",
  "1,2,3,4 are obj11;",
  "know obj0(#x);",
  "1,2,3,4 are obj0;",
];

const testList19 = [
  "def obj0(x) => ;",
  "def obj1(x) => x is obj0;",
  "def obj2(x) => obj1(x);",
  "let x | obj2(x);",
  "x is obj0 by {x is obj1;};", // If we put by at the end, then it's a declarative way of proving: instead of procedurally prove a result, we now declare a result at beginning and then prove it.
];

const setTheory1 = [
  "def object x | ;",
  "def set if x | => {};",
  "def in if x,A | A is set => {};",
  "def = iff A,B | set(A), set(B) <=> {if x | in(x,A) => {in(x,B)}, if x | in(x,B) => {in(x,A)}}",
];

const testList20 = [
  "def object(x) <=>;",
  "def obj2(x) =>;",
  // "def = A,B | obj(A), obj(B);",
  // "def deduce only_if x | x is obj <= ;",
  "def eq(A,B)  <=> A,B are obj2 when A,B are object;",
];

const testList21 = [
  "def obj0( x) =>;",
  "def obj1(x) =>;",
  "def obj2(x) =>;",
  "def obj3(x,y )  =>;",
  "let a,b;",
  // "know if x | x,b are obj0 => x is obj1;",
  "know if x | x,b are obj1 => {if | obj3(x,a) => {x is obj2}};",
];

const testList22 = [
  "def x is obj0 =>;",
  "def x is obj1 =>;",
  "def obj2(x,y) <=> x,y are obj1 when x,y are obj0;",
  "def obj3(x,y) => x,y are obj1 when x,y are obj0;",
  "def obj4(x,y) <= x,y are obj1 when x,y are obj0;",
];

const testList23 = [
  "def x is object =>;",
  "def x is set =>;",
  "def in(x,A) => when A is set;",
  "def =(A,B) <=> if x | in(x,A) => {in(x,B)}, if x | in(x,B) => {in(x,A)} when A,B are set;",
  "let A,B | A,B are set, if x | in(x,A) => {in(x,B)}, if x | in(x,B) => {in(x,A)};",
  "=(A,B);",
  "if x | p(x), p(y), p2(x,y) => q(x,y)",
  // {let x; know p(x); p(y); know p2(x,y); q(x,y); return q(x,y);}
];

const testList24 = [
  "def x is object => ;",
  "def x is obj => ;",
  "def x is object1 => x is object;",
  "def x is object2 => x is object1;",
  // "let y,z | y is object2;",
  // "y is object1;",
  // "know #x is object;",
  // "z is object;",
  // check, store
  // "if |  x is object2 => {if |  x is object1 => {x is object}};",
  "let y,z;",
  // "if  | y is object2 => {y is obj};",
  "if  | y is object2 => {y is object};",
  // "if | z is object2 => {if | => {z is object1} } ;",
];

const testsDict: { [s: string]: [string[], Boolean] } = {
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
  testList24: [testList24, true],
};

export function testCode() {
  for (const testList in testsDict) {
    const env = new L_Env();
    const exprs = testsDict[testList];
    if (exprs[1] === false) continue;

    for (let i = 0; i < exprs[0].length; i++) {
      const expr = exprs[0][i];
      const out = run(env, expr);
      if (out === undefined) {
        env.printClearMessage();
        continue;
      }
    }

    // env.printFacts();
    // env.printDeclFacts();
    L_Storage.printEnvFacts(env);
    env.printClearMessage();
  }
}

function run(env: L_Env, expr: string) {
  try {
    const tokens = scan(expr);
    const nodes = parser.L_StmtsParse(env, tokens);
    if (nodes === undefined) {
      return undefined;
    }
    const result: RType[] = [];
    for (const node of nodes) {
      const out = executor.nodeExec(env, node);
      result.push(out);
    }
    env.printClearMessage();

    return result;
  } catch (error) {
    return undefined;
  }
}
