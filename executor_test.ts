import { L_Env } from "./env";
import { nodePrintExec, RType, RTypeMap } from "./executor";
import { scan } from "./lexer";
import { L_StmtsParse } from "./parser";
import { isL_OutErr, isRTypeErr, RL_Out } from "./shared";
import { setTheory } from "./tao_analysis_one";
import { testCodes, testErrorCode } from "./test_code";

const codes: string[] = [
  // "// Start from one axiom, get followings",
  // "infer Axiom(x,y: P(x), Q(y);) { Thm1(x,y); Thm2(x,y);}",
  // "know P(#x), Q(#2), Axiom(#ha,#y);",
  // "infer Thm1(x,y: Thm2(x,y);) {Thm3(x,y);}",
  // "Thm1(#0, #1);",
  // "Thm3(#x, #3);",
  // "// declare infer using def =>",
  // "def Axiom(x,y: P(x), Q(y)) => {Thm1(x,y), Thm2(x,y);}",
  // "know P(#x), Q(#2), Axiom(#ha,#y);",
  // "def Thm1(x,y: Thm2(x,y)) => {Thm3(x,y);}",
  // "Thm1(#0, #1);",
  // "Thm3(#x, #3);",
  // "// @ is used as know",
  // ": Axiom(x,y| P(x), Q(y)) => {Thm1(x,y), Thm2(x,y);}",
  // "@ P(#x), Q(#2), Axiom(#ha,#y);",
  // ": Thm1(x,y| Thm2(x,y)) => {Thm3(x,y);}",
  // "Thm1(#0, #1);",
  // "Thm3(#x, #3);",
  // "// know and declare at the same time",
  // "@: fun(#x,3);",
  // "fun(2,1);",
  // "fun(3,3);",
  // "@: deduce(#x,#y) => { corollary(#y,#x);};",
  // "deduce(1,2);",
  // "corollary(2,1);",
  // "// declare subTemplate in template",
  // ": fun(x,y) {: subFun(y)}",
  // "@ fun(#x, #y):fun3(#x);",
  // "@ fun(#x, #y):fun4(#x);",
  // "fun(1,2):fun3(3);",
  // ":fun(x) {:fun2(x) :fun3(x,y) => {set(x,y);};fun4(x);}",
  // "know fun(3);",
  // "fun(3);",
  // "know fun(2):fun3(1,2);",
  // "fun(2):fun3(1,2);",
  // "fun(3);",
  // "fun(1):fun3(1,2);",
  // "know fun(1):fun2(x);",
  // "fun(1):fun2(x);",
  // "know fun(#1):fun2(2);",
  // "fun(21):fun2(2);",
  // "fun(3):fun2(1234);",
  // "know fun(1,2,3):fun2(3,4);",
  // "fun(1,2,3):fun2(3,4);",
  // ": inf(x) => {set(x);}",
  // "know inf(2);",
  // "inf(2), set(2);",
  // "// do ?",
  // ": func(x,y) <=> {$ fun2();  $ fun3(y) => {fun4(x);} }",
  // "@ func(1,2):fun2();",
  // "func(1,2):fun2();",
  // "@ func(1,2,3);",
  // "! func(1,2):fun3(3);",
  // ": definedP(x,y) <=> {set(x);}",
  // "know : fun(1,2);",
  // "is_def(definedP2);",
  // ": fun(x,y) <=> set(x), set2(y);",
  // "// emit",
  // "know func(1,2) => fun5(1);",
  // "func(1,2);",
  // "fun5(1);",
  // "know func(1,2);",
  // "fun5(1);",
  // "// know everything",
  // ": everything(x,y: fun0(x,y)) <=> {$ fun2();  $ fun3(y) => {fun4(x);} }",
  // "know_everything everything(1,2);", // requirements, onlyIfs, itself, all emitted.
  // "// test emitFact",
  // "def func4(x);",
  // "def set(x);",
  // "def twoSet(x,y);",
  // "def func(x: set(x)) <=> {func4(x); def subF(y:twoSet(x,y)) }",
  // "know_everything func(1):subF(2);",
  // "! func(3);",
  // "!: func5(3 : set(3)) <=> {func(1):subF(3);}; ",
  // "exist existenceOf(x: set(x))",
  // "know existenceOf(x);",
  // "existenceOf(x);",
  // "def exist2(x:set(x))",
  // "have exist2(y);",
  // "// check and emit",
  // "def inf(x:set(x)) => set(2);",
  // "know inf(1);",
  // "know set(1);",
  // "inf(1);",
  // "set(2);",
  // "set(3);",
  // "// test whether infer can emit facts"
  // "def fun(x) { def fun2(y) {def E(i,j)}}",
  // "know fun(1):fun2(2):E(3,4);",
  // "def fun3(x,y,a,b: fun(x):fun2(y):E(a,b) ) => {set(b); }",
  // "know fun3(1,2,3,4);",
  // "fun3(1,2,3,4);",
  // "know fun3(0,2,3,4);",
  // "fun3(0,2,3,5);",
  // "fun3(0,2,3,4);",
  // "// let",
  // "let x,y: set(x), set(y);",
  // "know set(z);",
  // "// when knowing exist and get the exist",
  // "exist existenceOfX(x: set(x));",
  // "let x;",
  // "know existenceOfX(x);",
  // "existenceOfX(x);",
  // "// test prove",
  // "def set(x);",
  // "def set2(x);",
  // "def fun(x) {set(x); set2(x);}",
  // "know set(#a);",
  // "prove fun(x) {set(x); know set2(x);  set2(x);}",
  // "def set3(x) => set2(x);",
  // "know set3(#1);",
  // "def fun4(x,y: set(x), set(y)) { set(x);}",
  // "let x,y: set(x), set(y);",
  // "prove fun4(*x,*y) {set(x); set(y);}",
  // "def set2(x,y);",
  // "know set2(#x, #y);",
  // "def set2(x,y) ;",
  // "def fun4(x, y: set2(x,y)) ;",
  // "let x,y;",
  // "def set(x);",
  // "prove fun4(x, y: set(y)) {}",
  // "// refactor how facts are stored",
  // "def set(x);",
  // "let 1;",
  // "know set(1);",
  // "set(1);",
  // "def set2(x);",
  // "def inferF(x: set(x)) => {set2(x);}",
  // "know inferF(1);",
  // "inferF(1);",
  // "set2(1);",
  // "def set(x) => {def set2(x) => {}}",
  // "def two(x,y);",
  // "def set3(x);",
  // "def set(x) => {def set2(y:set3(y)) => {two(x,y);}}",
  // "know_everything set(1):set2(2);",
  // "def set(x);",
  // "def set2(x);",
  // "know set(#x: set2(#x));",
  // "let 1: set2(1);",
  // "set(1);",
  // "def set(x) ;",
  // "let x: set(x);",
  "def set(x);",
  "exist func(x: set(x))",
  "have x: func(x);",
];

// function callOptsExecTest() {
//   console.log("\n----results------\n");
//   for (const item of codes) {
//     const tokens = scan(item);
//     const result = L_StmtsParse(env, tokens);
//     if (result === null) {
//       env.printErrorsWithDepth();
//     } else {
//       for (let i = 0; i < result.length; i++) {
//         const res: L_Out<RType>  = nodePrintExec(env, result[i]);
//         if (!res.message) console.log(RTypeMap[res.type]);
//         else console.log(`${RTypeMap[res.type]} '${res.message}'`);
//       }
//     }
//   }
//   console.log("");
//   if (env.messages.length === 0) {
//     env.printCallOptFacts();
//     env.printDeclaredTemplates();
//   } else {
//     env.printErrorsWithDepth();
//   }
// }

// callOptsExecTest();

function testError(asIfRight = false) {
  if (asIfRight) {
    const env = new L_Env();
    for (const [key, code] of Object.entries(testErrorCode)) {
      const tokens = scan(code as string);
      const result = L_StmtsParse(env, tokens);
      if (result === null) {
        console.log(env.messages);
      } else {
        for (let i = 0; i < result.length; i++) {
          const res = nodePrintExec(env, result[i]);
        }
      }
      if (env.messages.length === 0) {
        console.log(`${key} error not detected.`);
      }
    }
  } else {
    console.log("\n----Errors-----\n");
    const whatIsTested = [];
    let env: L_Env = new L_Env();
    for (const [key, code] of Object.entries(testErrorCode)) {
      console.log(key + ":");
      whatIsTested.push(key);
      const tokens = scan(code as string);
      const result = L_StmtsParse(env, tokens);
      if (result === null) {
        console.log(env.messages);
      } else {
        for (let i = 0; i < result.length; i++) {
          const res = nodePrintExec(env, result[i]);
          if (isRTypeErr(res)) console.log(RTypeMap[res as RType]);
          else console.log(env.messages);
        }
      }
      console.log();
    }
  }
}

function testExecutor(testWhat: any = testCodes) {
  let env: L_Env = new L_Env();

  console.log("\n----results------\n");
  const whatIsTested = [];
  for (const [key, code] of Object.entries(testWhat)) {
    whatIsTested.push(key);
    const tokens = scan(code as string);
    const parseResult = L_StmtsParse(env, tokens);
    if (parseResult === null) {
      console.log(env.messages);
      env.messages = [];
    } else {
      for (let i = 0; i < parseResult.length; i++) {
        const res = nodePrintExec(env, parseResult[i]);
        if (key !== "Basics") {
          if (isRTypeErr(res)) {
            console.log(env.messages);
          } else {
            console.log(env.messages.at(-1));
          }
        }
        env.messages = [];
      }
    }
  }
  console.log("\n----TestWhat----\n");
  whatIsTested.forEach((e) => console.log(e));
  if (env.messages.length === 0) {
    if (env.facts.size > 0) env.printFacts();
    // env.printCallOptFacts();
    // do not print templates declared in Basics
    if (env.declaredTemplates.size > 0)
      env.printDeclaredTemplates([
        "obj",
        "set",
        "set0",
        "p1",
        "set2",
        // "F",
        "set3",
      ]);
    if (env.bys.size > 0) env.printBys();
  } else {
    console.log("\n------Error------\n");
    console.log(env.messages);
    console.log();
  }
}

// testExecutor(setTheory);
testExecutor(testCodes);
// testError();
