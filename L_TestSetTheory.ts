import { ExampleItem } from "./L_Structs";
import { L_Env } from "./L_Env";
import { runStrings } from "./L_Runner";
import * as fs from "fs";

const exampleList: ExampleItem[] = [
  {
    name: "define subset",
    code: [
      `
def object(x);
def set(x);
know if x: set(x) {
  object(x)
};
{
  let a: set(a);
  object(a);
}
def equal(a,b);
def in(x,a);
know if a,b: set(a), set(b), equal(a,b)  {
  if x: in(x,a) {
    in(x,b)
  }, 
  if x: in(x,b) {
    in(x,a)
  }
};
know if a,b: set(a), set(b), if x: in(x,a) {in(x,b)}, if x: in(x,b) {in(x,a)} {
  equal(a,b)
};

{
  let a, b: set(a), set(b), equal(a,b); 
  know if x: in(x,a)  {
    in(x,b)
  };
  know if x: in(x,b)  {
    in(x,a)
  }; 
  let x: in(x,a); 
  in(x,b); 
}

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

def_composite \\singleton{a};
know if x, a: in(x, \\singleton{a}) {
    equal(x, a);
};

know if x, a: equal(x,a) {
    in(x, \\singleton{a});
};

{
    let a, b;
    know set(\\singleton{a});
    let x;
    know in(x, \\singleton{a});
    equal(x,a);
    in(x, \\singleton{a});
    if _x, _a: equal(_x,_a) {
        in(_x, \\singleton{_a})[_x, _a];
    };
}

`,
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
      if (example.test !== undefined) {
        runStrings(env, example.test, example.print);
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
    runStrings(env, [data], true);
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
