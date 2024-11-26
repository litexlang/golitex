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
      "know if A,B: if x: in(x,A) => {in(x,B)} => {subset(A,B)};",
      "know if A,B: subset(A,B) => {if x: in(x,A) => {in(x,B)} };",
      "let A,B,C,D,E,F;",
      "know subset(A,B);",
      "let x: in(x,A);",
      "in(x,B);", //Unknown
    ],
    debug: false,
    print: false,
  },
  {
    name: "reqSpace & use",
    code: [
      "def set(x); def subset(A,B); def in(x,A);",
      "know if A,B: if x: in(x,A) => {in(x,B)} => {subset(A,B)};",
      "know if A,B: subset(A,B) => [P] {if x: in(x,A) => {in(x,B)} };",
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
    debug: true,
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
    name: "by and know if-then work together",
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
