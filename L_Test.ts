import { ExampleItem } from "./L_Structs";
import { L_Env } from "./L_Env";
import * as fs from "fs";
import { runString, runStringWithLogging } from "./L_Runner";

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
  },
  {
    name: "throw error system",
    code: ["concept $p(x); concept $q(x); concept $t(x); know $t(y);"],
    debug: false,
  },
  {
    name: "is_property",
    code: [
      "concept $p(x); let x: $p(x); $is_concept(p; $p(x)); $is_concept(p; $p(z));",
    ],
    debug: false,
  },
  {
    name: "is_form",
    code: [
      "concept $p(x); let x: $p(x); operator \\++{x}; let a; $is_form(\\++{a}; \\++{A}) ;",
    ],
    debug: false,
  },
  {
    name: "checkFacts",
    code: [
      "concept commutative $=(x, y); operator \\frac{x,y}; operator \\*{x,y};",
      " know if n,x,y {\\frac{\\*{x,n}, \\*{y,n}} = \\frac{x,y} } ; ",
      // " if n,x,y {\\frac{\\*{x,n}, \\*{y,n}} = \\frac{x,y} [n,x,y] } ;",
      "let 1,2,3;",
      // "[n: 1,x: \\frac{1,2}, y: \\frac{1,3}] {\\frac{\\*{x,n}, \\*{y,n}} = \\frac{x,y}}; ",
      // "\\frac{\\*{\\frac{1,2},1}, \\*{\\frac{1,3},1}} = \\frac{\\frac{1,2},\\frac{1,3}};",
      "[1,x: \\frac{1,2}, y: \\frac{1,3}] {\\frac{\\*{x,1}, \\*{y,1}} = \\frac{x,y}}; ",
    ],
    debug: false,
  },
  {
    name: "new if expr",
    code: [
      `concept $=(x, y); operator \\frac{x,y}; let 1; concept $nat(x);`,
      `if [x(a, b): \\frac{\\frac{a,1}, b}]: $nat(a) {x = \\frac{a, b}};`,
    ],
    debug: false,
  },
  {
    name: "",
    code: [
      "concept $p(x); concept $q(x,y); know if x, y: $p(x), $p(y) {$q(x,y) };",
      "if a,b: all a,b are p {$q(a,b)} ;",
    ],
    debug: false,
  },
  {
    name: "",
    code: [
      `operator \\*{a,b};`,
      "concept $real(x);",
      `let 1,2,3;`,
      `know all 1,2,3 are real;`,
      "know if [n(a,b): \\*{a,b}]: a is real {n is real};",
      "3 is real;",
      "1 * 2 is real;",
    ],
    debug: false,
  },
  {
    name: "",
    code: [
      `concept $real(x); lets nat "a|b" ;`,
      `know nat is real;`,
      "nat is real;",
      "a is real;",
    ],
    debug: false,
  },
  {
    name: "",
    code: [
      `concept $real(x); operator \\frac{a,b}; let x,y: x is real;`,
      `\\frac{x,y}[0] is real;`,
    ],
    debug: false,
  },
  {
    name: "",
    code: [
      `concept $real(x); operator \\frac{a,b}; let x,y: x is real;`,
      `concept_alias 实数 real;`,
      "x is 实数;",
      "know if x :  x is 实数 {x is real};",
    ],
    debug: false,
  },
  {
    name: "=",
    code: ["let x,y; x = x; x = y;"],
    debug: false,
  },
  {
    name: "",
    code: [
      "concept $real(x); operator \\frac{x,y} ; ",
      "know if [x(a,b): \\frac{a,b}]: a is real, b is real {x is real};",
      "if [x(a,b): \\frac{a,b}]: a is real, b is real {x is real};",
    ],
    debug: true,
  },
];

function runExamples(
  logSourceCode: boolean = true,
  logMessages: boolean = true
) {
  for (const example of exampleList) {
    const env = L_Env.constructWithInitialization();
    if (example.debug) {
      console.log(example.name);
      for (const expr of example.code) {
        runStringWithLogging(env, expr, logSourceCode, logMessages);
      }
    }
  }
}

function runLiTeXFile(
  filePath: string,
  logSourceCode = true,
  logMessages = true
) {
  try {
    const data = fs.readFileSync(filePath, "utf8");
    const env = new L_Env();

    const exprs = [data];
    for (let i = 0; i < exprs.length; i++) {
      const expr = exprs[i];
      runStringWithLogging(env, expr, logSourceCode, logMessages);
    }
  } catch (err) {
    console.error("Error:", err);
  }
}

function runTest() {
  const args = process.argv.slice(2);
  if (!args || args.length === 0) {
    runExamples();
  } else {
    runLiTeXFile(args[0]);
  }
}

runTest();
