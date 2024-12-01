import { ExampleItem } from "./L_DataStructures";
import { L_Env } from "./L_Env";
import { runStrings } from "./L_Runner";
import * as fs from "fs";

export const exampleList: ExampleItem[] = [
  {
    name: "basic syllogism",
    code: [
      "def mortal(something);",
      "def something is human {if x : x is human => {x is mortal}};",
      "let Socrates: Socrates is human;",
      "Socrates is mortal;",
      "if x : x is human => {x is mortal};",
      "let god : god is not mortal;",
      `prove_by_contradiction god is not human {
        god is mortal;
      } contradiction god is mortal;`,
      "god is not human;",
    ],
    debug: false,
    print: true,
  },
  {
    name: "concept definition",
    code: [
      "def p(x);",
      "def x is p1;",
      "def q(x,y);",
      "def p2(x) {if x: x is p1 => {x is p2} }",
      "def p3(x) {if x: p3(x) => {p(x)} , if x: p(x) => {p3(x)} }",
      "let x,y: p3(x), p(y);",
      "p(x), p3(y);",
      "def p(x);", // error: you can not declare a concept twice.
    ],
    debug: false,
    print: true,
  },
  {
    name: "expression checking",
    code: [
      "def human(x);",
      "def teacher(x,y);",
      "let 亚里士多德, Plato: 亚里士多德  is human;",
      "亚里士多德 is not human; // False",
      "human(亚里士多德);",
      "Plato, 亚里士多德 are human;",
      "teacher(Plato, 亚里士多德);",
      "know teacher(Plato, 亚里士多德);",
      "teacher(Plato, 亚里士多德);",
      "let somebody;",
      "somebody is human; // Unknown",
    ],
    debug: false,
    print: true,
  },
  {
    name: "variable introduction",
    code: [
      "def p(x); def q(x,y);",
      "let x,y,z;",
      "let 变量, 10.2, _nonsense, 你好 world, I-AM-MEANINGLESS;",
      "let a,b,c: a is p, q(b,c);",
      "let y;", // y already declared.
    ],
    debug: false,
    print: true,
  },
  {
    name: "not operator",
    code: [
      "def p(x);",
      "let v1, v2, v3, v4, v5: not p(v1), v2 is not p, not v3 is p, v4,v5 are not p;",
      "not p(v1);",
      "let v6;",
      "not p(v6); // Unknown",
      "know not p(v6);",
      "not p(v6); // True",
    ],
    debug: false,
    print: true,
  },
  {
    name: "if and forall",
    code: [
      "def p1(x); def p(x); def p2(x) {if x: x is p2 => {x is p1}}",
      "if x: x is p2 => {x is p1}; // True",
      "if x: x is p => {x is p1}; // Unknown",
      "if x : x is p => {x is p}; // Always true",
    ],
    debug: false,
    print: true,
  },
  {
    name: "prove and contradiction",
    code: [
      "def p3(x); def p2(x); def p1(x);",
      "know if x: p3(x) => {p2(x)}, if x : p2(x) => {p1(x)} ;",
      "prove if x : x is p3 => {x is p1} {x is p2;}",
      "let v10,v12: v10 is p2; // prove factual-expression {proofs}",
      "prove v10 is p1 {v10 is p2;}",
      "know v12 is not p1;",
      `prove_by_contradiction v12 is not p3 {v12 is p2;} contradiction v12 is p1;`,
    ],
    debug: false,
    print: true,
  },
  {
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
    name: "prove exist",
    code: ["def p(x); prove exist(p) {let x: p(x); exist(p)[x];}"],
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
    name: "use [] to pass in extra parameters example: define subset",
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
    name: "use [] to pass in extra parameters example: transitivity",
    code: [
      "def <(x,y); know if x,y,z: <(x,y), <(y,z) => {<(x,z)};",
      "let a,b,c: <(a,b), <(b,c);",
      "<(a,c)[a,b,c];",
    ],
    debug: false,
    print: true,
  },
  {
    name: "macro: bind properties to a variable based on its literal",
    code: [
      "def natural(x);",
      'macro "^(0|[1-9]d*)$" v natural(v);',
      "let 2;",
      "natural(2);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "check if-then example:continuous",
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
    debug: true,
    print: true,
  },
];
function runExamples(toJSON: boolean) {
  const env = new L_Env();
  for (const example of exampleList) {
    if (example.debug) {
      console.log(example.name);
      runStrings(env, example.code, example.print);
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
