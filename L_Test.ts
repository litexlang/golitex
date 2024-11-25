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
      "let x,A,B: in(x,A), subset(A,B); ",
      // "in(x,A);",
      "in(x,B)[x,A,B];",
    ],
    debug: true,
    print: true,
  },
];

function runExamples() {
  const env = new L_Env();
  for (const example of exampleList) {
    if (example.debug) {
      console.log(example.name);
      runStrings(env, example.code, example.print);
    }
  }
  envToJSON(env, "env.json");
}

runExamples();

function envToJSON(env: L_Env, fileName: string) {
  const out = env.toJSON();
  // Convert the JSON object to a string and then to Uint8Array
  const jsonString = JSON.stringify(out, null, 2);
  const encoder = new TextEncoder();
  const data = encoder.encode(jsonString);

  Deno.writeFileSync(fileName, data);
  return out;
}

export function testEnvToJSON() {
  const env = new L_Env();
  for (const example of exampleList) {
    if (example.debug) {
      console.log(example.name);
      runStrings(env, example.code, example.print);
    }
  }
  envToJSON(env, "env.json");
}
