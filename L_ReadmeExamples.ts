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
    debug: true,
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
      "prove if x : x is p3 => {x is p1} {x is p2;}",
      "let v10,v12: v10 is p2; // prove factual-expression {proofs}",
      "prove v10 is p1 {v10 is p2;}",
      "// prove_by_contradiction factual-expression {proofs}",
      "contradiction expression;",
      "know v12 is not p1;",
      "prove_by_contradiction v12 is not p3 {v12 is p2}",
      "contradiction v12 is p1;",
    ],
    debug: false,
    print: true,
  },
  {
    name: "exist and have",
    code: [
      "def E(x): p(x) exist y {q(x,y)};",
      "have E(x): v11; // Failed: p(v10) is unknown",
      "know p(v11);",
      "have E(x): v11; // True",
      "q(x,v11);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "inline definition during proving",
    code: [
      "if x: p(x) => {p(x)} [p1_1];",
      "let v15: p(v15)[p1_2];",
      "p1_1(x);",
      "def nothing();",
      "know if nothing() => {exist x,y {q(x,y)} [p1_3]};",
      "have p1_3(): v16,17;",
      "q(v16,v17); // True",
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
