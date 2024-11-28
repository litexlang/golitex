import { L_Env } from "./L_Env.ts";
import { runStrings } from "./L_Runner.ts";

type ExampleItem = {
  name: string;
  code: string[];
  debug: boolean;
  print: boolean;
};

export const exampleList: ExampleItem[] = [
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
    name: "reqSpace & use",
    code: [
      "def set(x); def subset(A,B); def in(x,A);",
      "know if A,B: if x: in(x,A) => {in(x,B)} => {subset(A,B)};",
      // "def P(A,B); know if A,B: P(A,B), subset(A,B) =>  {if x: in(x,A) => {in(x,B)} };",
      "know if[P] A,B: subset(A,B) =>  {if x: in(x,A) => {in(x,B)} };",
      "let A,B,C,D,E,F;",
      "know subset(A,B);",
      "let x: in(x,A);",
      "use P(A,B);",
      "if x : in(x,A) => {in(x,B)};",
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
    name:
      "known if req => opt must satisfy: req does not contain if-then-type fact that has opt as onlyIf",
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
    name: "by and know if-then work together, not implemented",
    code: [
      "def p(x);",
      "def q(x)",
      "def a(x,y);",
      "know if [P] x : p(x), if [Q] y: q(y) => {} => {if [A] p(y) => {a(x,y)}};",
      "let v1,v2: p(v1), q(v2), p(v2);",
      "by P(v1): by Q(v2) => {by A() => {a(v1,v2)}};",
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
      "def something is human; know if x is human => {x is mortal};",
      "let Socrates : Socrates is human;",
      "Socrates is  mortal;",
      "let god : god is not mortal;",
      "god is not human;",
      "prove_by_contradiction god is not human {god is mortal;} contradiction god is mortal;",
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
    name: "exist",
    code: ["def p(x); def q(x); ", "let x: p(x);", "exist(p,x);", "exist(p);"],
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

export function envToJSON(env: L_Env, fileName: string) {
  const out = env.toJSON();
  // Convert the JSON object to a string and then to Uint8Array
  const jsonString = JSON.stringify(out, null, 2);
  const encoder = new TextEncoder();
  const data = encoder.encode(jsonString);

  Deno.writeFileSync(fileName, data);
  return out;
}
