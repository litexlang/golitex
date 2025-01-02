import { ExampleItem } from "./L_Structs";
import { L_Env } from "./L_Env";
import { runStringsWithLogging } from "./L_Runner";
import * as fs from "fs";

const exampleList: ExampleItem[] = [
  {
    name: "三段论",
    code: [
      "concept something is mortal;",
      "concept something is human; know if x: x is human  {x is mortal};",
      "let Socrates : Socrates is human;",
      "Socrates is  mortal;",
      "let god :  not $mortal(god);",
      "not $human(god);",
      "prove_by_contradiction  not  $human(god) {god is mortal;}  god is mortal;",
      "not $human(god);",
    ],
    debug: false,
    print: true,
  },
  {
    name: "新的parser检查",
    code: [
      "concept $p(x); concept $q(x): $p(x) {$p(x)};",
      "operator \\frac{x,y}: $p(x);",
      "know if x: $p(x) {$q(x)};",
      "let y: $p(y);",
      "let_formal x: $p(x);",
      "let_alias Y: y;",
      "if y: $p(y) {$q(y)};",
    ],
    debug: false,
    print: true,
  },
  {
    name: "throw error system",
    code: ["concept $p(x); concept $q(x); concept $t(x); know $t(y);"],
    debug: false,
    print: true,
  },
  {
    name: "is_property",
    code: [
      "concept $p(x); let x: $p(x); $is_concept(p; $p(x)); $is_concept(p; $p(z));",
    ],
    debug: false,
    print: true,
  },
  {
    name: "is_form",
    code: [
      "concept $p(x); let x: $p(x); operator \\++{x}; let a; $is_form(\\++{a}; \\++{A}) ;",
    ],
    debug: false,
    print: true,
  },
  {
    name: "checkFacts",
    code: [
      "concept $=(x, y); operator \\frac{x,y}; operator \\*{x,y};",
      " know if n,x,y {\\frac{\\*{x,n}, \\*{y,n}} = \\frac{x,y} } ; ",
      " if n,x,y {\\frac{\\*{x,n}, \\*{y,n}} = \\frac{x,y} [n,x,y] } ;",
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
      runStringsWithLogging(env, example.code, example.print);
      if (example.test !== undefined) {
        runStringsWithLogging(env, example.test, example.print);
      }
    }
  }
  if (toJSON) envToJSON(env, "env.json");
}

export function envToJSON(env: L_Env, fileName: string) {
  const out = env.toJSON();
  const jsonString = JSON.stringify(out, null, 2);

  fs.writeFileSync(fileName, jsonString, "utf8");

  return out;
}

function runLiTeXFile(filePath: string) {
  try {
    const data = fs.readFileSync(filePath, "utf8");
    const env = new L_Env();
    const logging = true;
    runStringsWithLogging(env, [data], logging);
  } catch (err) {
    console.error("Error:", err);
  }
}

function run() {
  const args = process.argv.slice(2);
  if (!args || args.length === 0) {
    runExamples(false);
  } else {
    runLiTeXFile(args[0]);
  }
}

run();
