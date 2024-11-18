import { L_Env } from "./L_Env.ts";
import { runStrings } from "./L_Runner.ts";

type ExampleItem = {
  name: string;
  code: string[];
  debug: boolean;
  print: boolean;
};

const exampleList: ExampleItem[] = [
  {
    name: "t0",
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
    name: "t1",
    code: [
      "def set(x); def subset(A,B); def in(x,A);",
      "know if A,B: if x: in(x,A) => {in(x,B)} => {subset(A,B)};",
      "know if A,B: subset(A,B) => [P] {if x: in(x,A) => {in(x,B)} };",
      "let A,B,C,D,E,F;",
      "know subset(A,B);",
      "let x: in(x,A);",
      "P<A,B>;",
    ],
    debug: false,
    print: false,
  },
];

function runExamples() {
  for (const example of exampleList) {
    const env = new L_Env();
    if (example.debug) {
      console.log(example.name);
      runStrings(env, example.code, example.print);
    }
  }
}

runExamples();
