import { ExampleItem } from "./L_Structs";
import { L_Env } from "./L_Env";
import { L_Scan } from "./L_Lexer";
import { parseNodes } from "./L_Parser";

export const exampleList: ExampleItem[] = [
  {
    name: "define subset",
    code: [
      "def set(x);",
      "let x;",
      "know set(x);",
      "set(x)[x,y];",
      "set (\\frac{1,2})[\\frac{3,4}, \\frac{5,6}] ;",
      "if x, \\frac{a,b}[a,b] : set(x) {set(x)};",
    ],
    debug: false,
    print: true,
  },
  {
    name: "def_composite",
    code: [
      "def_composite \\frac{x,y} : number(x), number(y);",
      "know if x, a, b: in(x, \\pair{a,b}) { if :  not equal(x, b) {equal(x, a)} , if : not equal(x, a) {equal(x, b)} } ;",
      `
      let a ; // ha
      let b;
      `,
    ],
    debug: false,
    print: true,
  },
  {
    name: "comment",
    code: [
      `
      let a ; // ha
      let b;
      `,
    ],
    debug: false,
    print: true,
  },
  {
    name: "opt",
    code: [
      `
let EMPTY_SET: set(EMPTY_SET);

know if x {
    not in(x,EMPTY_SET),
};

{
    let x : not in(x, EMPTY_SET);
    if _x {
        not in(_x,EMPTY_SET)[_x];
    };
}
`,
    ],
    debug: false,
    print: true,
  },
  {
    name: "bool fact",
    code: [`let x: (p(x) or q(y) and j(z) or t(x));`],
    debug: false,
    print: true,
  },
  {
    name: "()",
    code: [`know if x: x is nat {not =(0, \++{x}) }; if x {p(x)};`],
    debug: false,
    print: true,
  },
  {
    name: "()",
    code: [
      `know if a,b,c: a is nat, b is nat, c is nat, $a + b$ = $a + c$ {$b = c$};`,
    ],
    debug: false,
    print: true,
  },
  {
    name: "()",
    code: ["def_function f(x);"],
    debug: true,
    print: true,
  },
];

function runExamples() {
  const env = new L_Env();
  for (const example of exampleList) {
    if (example.debug) {
      console.log(example.name);
      runParserTest(env, example.code, example.print);
      if (example.test !== undefined) {
        runParserTest(env, example.test, example.print);
      }
    }
  }
}

function runParserTest(env: L_Env, codes: string[], print: boolean) {
  for (const code of codes) {
    const tokens = L_Scan(env, code);
    const nodes = parseNodes(env, tokens, null);
    for (const node of nodes) {
      if (print) console.log(node);
    }
  }
}

runExamples();
