import { L_Env } from "./env";
import { executor } from "./executor";
import { scan } from "./lexer";
import { parser } from "./parser";

// Aristotle induction
export const testList0 = [
  "def obj2 x |;",
  "def obj if x | => ;",
  "def set x | obj(x);",
  "let y | set(y);",
  "def set2 z | set(z);",
  "set2(y);",
  "set2(y);",
];

export const testList1 = [
  "def obj if x | => ;",
  "def obj2 if x | => ;",
  "def p2 x | obj(x), obj2(x);",
  "let y | obj(y);",
  "if | obj2(y) => {p2(y)};",
  // "if | => {p2(y)};",
];

export const testList2 = [
  "def obj if x | => ;",
  "def obj2 x | obj(x) ;",
  "def obj3 if x | => ;",
  "def obj4 if x | => obj3(x);",
  "let EMPTY_SET;",
  "def inf if x | obj(x) => obj3(x);",
  "prove if x | obj(x) => {obj3(x)} {}", // unsuccessful prove
  "prove if x | obj(x) => {obj3(x)} {know obj4(x);}",
];

export const testList3 = [
  "def obj if x | => ;",
  "def obj2 x | obj(x) ;",
  "def obj3 if x | obj(x), obj2(x) => ; ",
  "prove if x |  => {obj2(x)} {}", // unsuccessful prove
  "prove if x |  obj(x), obj3(x) => {obj2(x)} {}", // obj3 is useless
];

export const testList4 = [";;;\n\n;;"];

export const testList5 = [
  "def p1 if x | => ;",
  "def p2 x | p1(x);",
  // "def p3 x | p2(x);",
];

export const testList6 = [
  "def p1 if x | => ;",
  "exist Ex x | p1(x);", // can be used as a "stronger" version of def.
  "let y | p1(y);",
  "have x | Ex(x);", // unsuccessful have
  "Ex(y);", // we declare and exe exist-fact by exactly using shortOpt code.
  "have z | Ex(z);",
];

export const testList7 = [
  "def p1 if x | => ;",
  "def p2 x | p1(x);",
  "def p3 x | p2(x);",
  "let y | p1(y);",
  "p3(y);", // unknown
  "p3(y) by {p2(y)};",
  "p3(y);",
  "know not p1(y);",
  "p1(y);",
];

export const testList8 = [
  "def obj if x | => ;;",
  "def obj2 x,y | obj(x), obj(y);",
  "let x,y | obj(x), obj(y);",
  "obj(x), obj(y);",
  "obj2(x,y);",
  // "know obj(y);",
  // "obj(y);",
  // "obj2(x,y);",
];

export const testList9 = [
  "def obj if x | => ;;",
  "let x| not obj(x);",
  "not obj(x);",
];

export const testList10 = [
  "def p1 if x | => ;",
  "def p2 x | p1(x);",
  "def p3 x | p2(x);",
  "let x | not p3(x);",
  "assume_by_contradiction p1(x) {p2(x);} {p3(x)}",
];

export const testList11 = [
  "def p0 only_if x | ;",
  "def p1 only_if x | p0(x);",
  "let x | p0(x);",
];

const testsDict: { [s: string]: [string[], Boolean] } = {
  testList: [testList0, true],
  testList1: [testList1, true],
  testList2: [testList2, true],
  testList3: [testList3, true],
  testList4: [testList4, true],
  testList5: [testList5, true],
  testList6: [testList6, true],
  testList7: [testList7, true],
  testList8: [testList8, true],
  testList9: [testList9, true],
  testList10: [testList10, true],
  testList11: [testList11, true],
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

    env.printFacts();
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
    const result = nodes?.map((e) => executor.nodeExec(env, e));
    env.printClearMessage();

    return result;
  } catch (error) {
    return undefined;
  }
}
