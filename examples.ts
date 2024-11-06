import { L_Env } from "./L_Env";
import { L_Executor, RType } from "./L_Executor";
import { L_Scan } from "./L_Lexer";
import { L_Parser } from "./L_Parser";

type ExampleItem = {
  name: string;
  code: string[];
  debug: boolean;
  print: boolean;
};

export const exampleList: ExampleItem[] = [
  {
    name: "三段论",
    code: [
      "def something is 会死 => {};",
      "def something is 人 => {something is 会死};",
      "let 苏格拉底 : 苏格拉底 is 人;",
      "苏格拉底 is 会死;",
      "let 神仙 : 神仙 is not 会死;",
      "prove_by_contradiction 神仙 is not 人 {神仙 is 会死;} contradiction 神仙 is 会死;",
    ],
    debug: false,
    print: false,
  },
  {
    name: "defs",
    code: [
      "def x is p => {};",
      "def x is p1 => {x is p};",
      "def x is p2 => {x is p1};",
      "def x is p3 => {x is p2};",
      "def x is p4 <=> {x is p};",
      "def x is p5 <= {x is p4};",
      "def pair_wise(x,y) => {};",
      "def multi_wise(x,y,z) => {};",
      "def q0(x) => {};",
      "def x is q <=> {x is q0} when x is p;",
    ],
    debug: true,
    print: false,
  },
  {
    name: "let",
    code: [
      "let x , y ,z: x is p;",
      "let a,b,c : a,b,c are p;",
      "let 1,0, 12343124, 314_garbage_-code_159, _garbage, 你好world;",
    ],
    debug: true,
    print: false,
  },
  {
    name: "facts",
    code: [
      "x is p;",
      "x is q0;", // unknown
    ],
    debug: true,
    print: false,
  },
  {
    name: "if_for_all",
    code: [
      "if x : x is p2 => {x is p1};",
      "if x : x is p2 => {x is p2};",
      "if x : x is p2, y is p1 => {};",
      "if : y is p1 => {y is p};",
      "if y is p1 => {y is p};",
      "if x : y is p1 => {y is p};",
      "if a: => {if : a is p1 => {if : => {a is p}}};",
      "know if x: x is p1, x is p2, x is p3 => {x is p5};",
      "if x : x is p1 => {if x is p2 => {if x is p3 => {x is p5}}};",
    ],
    debug: true,
    print: false,
  },
  {
    name: "not",
    code: ["if x : x is not q0 => {x is not q0};"],
    debug: true,
    print: false,
  },
  {
    name: "knows",
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
  {
    name: "exist_have",
    code: [
      "exist something is p;",
      "exist pq(y,z);",
      "have d: d is p1;",
      "have e,f: pq(e,f);",
    ],
    debug: true,
    print: false,
  },
  {
    name: "prove",
    code: [
      "prove if x : x is p2 => {x is p} {x is p1;}",
      "know z is p3;",
      "prove z is p {z is p2; z is p1;}",
    ],
    debug: true,
    print: false,
  },
  {
    name: "prove_by_contradiction",
    code: [
      "let n : n is not p;",
      "prove_by_contradiction n is not p3 {n is p2; n is p1;} contradiction n is p;",
    ],
    debug: true,
    print: false,
  },
  {
    name: "postfix_prove",
    code: ["z is p2 prove {z is p3;};"],
    debug: true,
    print: false,
  },
  {
    name: "by",
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
  {
    name: "block",
    code: [
      "let u,v : u,v are p3;",
      "{u is p2; return u is p1;}",
      "{v is p2;} => {v is p1;};",
    ],
    debug: true,
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
      }`
        .replace(/\s+/g, " ")
        .trim(),
      "x1 is object;",
      "x2 is object;",
      "if x : x is object2 => {x is set};",
    ],
    debug: true,
    print: false,
  },
];

function runExampleDict() {
  const env = new L_Env();
  for (const example of exampleList) {
    if (example["debug"] !== true) continue;
    const exprs = example["code"];
    console.log(example);

    if (example.print) {
      const newEnv = new L_Env();
      for (const expr of exprs) {
        const out = run(newEnv, expr);
        if (out === undefined) {
          newEnv.printClearMessage();
          continue;
        }
      }
    }

    for (const expr of exprs) {
      const out = run(env, expr);
      if (out === undefined) {
        env.printClearMessage();
        continue;
      }
    }
  }

  // env.printFacts();
  // env.printDeclFacts();
  // L_FactStorage.printEnvFacts(env);
  env.printAllStoredFacts();
  env.printClearMessage();
  env.printBys();
}

function run(env: L_Env, expr: string) {
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
    env.printClearMessage();

    return result;
  } catch (error) {
    return undefined;
  }
}

runExampleDict();
