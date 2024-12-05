import { ExampleItem } from "./L_Structs";
import { L_Env } from "./L_Env";
import { runStrings } from "./L_Runner";
import * as fs from "fs";

export const exampleList: ExampleItem[] = [
  {
    name: "define basic concepts: object, set",
    code: ["def object(x); def set(x);", "know if x: set(x) => {object(x)};"],
    debug: true,
    print: true,
  },
  {
    name: "equality of sets",
    code: [
      "def equal(a,b); def in(x,a);",
      "know if a,b: set(a), set(b), equal(a,b) => {if x: in(x,a) => {in(x,b)}, if x: in(x,b) => {in(x,a)}};",
      "know if a,b: set(a), set(b), if x: in(x,a) => {in(x,b)}, if x: in(x,b) => {in(x,a)} => {equal(a,b)};",
    ],
    debug: false,
    print: true,
  },
  {
    name: "empty set",
    code: [
      "let EMPTY_SET: set(EMPTY_SET);know if x: => {not in(x,EMPTY_SET)};",
    ],
    debug: false,
    print: true,
  },
  {
    name: "singleton",
    code: [
      "know if x, a: in(x, \\singleton{a}) => {equal(x, a)};",
      "know if x, a: equal(x,a) => {in(x, \\singleton{a})};",
    ],
    debug: false,
    print: true,
  },
  {
    name: "pair",
    code: [
      "know if x, a, b: in(x, \\pair{a}{b}) => { if not equal(x, b) => {equal(x, a)} , if not equal(x, a) => {equal(x, b)} } ;",
      "know if x, a : in(x,a) => {in(x, \\pair{a}{b})}",
      "know if x, b : in(x,b) => {in(x, \\pair{a}{b})}",
    ],
    debug: false,
    print: true,
  },
  {
    name: "pair-wise union",
    code: [
      "know if x, y: set(x), set(y) => {if z: in(z, x) => { in(z , \\union{x, y})}, if z : in(z, y) => {in(z, \\union{x,y})} };",
      "know if x, y, z: in(z , \\union{x, y}) => {if not in(z, x) => {in(z, y)}, if not in(z, y) => {in(z, x)}};",
    ],
    debug: false,
    print: true,
  },
  {
    name: "subset",
    code: [
      "def subset(x,y);",
      "know if A,B: subset(A,B) => {if x: in(x,A) => {in(x,B)} };",
      "know if A,B: if x: in(x,A) => {in(x,B)} => {subset(A,B)};",
    ],
    debug: false,
    print: true,
  },
  {
    name: "exist",
    code: [],
    debug: false,
    print: true,
  },
  {
    name: "know not exist",
    code: [],
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

export function envToJSON(env: any, fileName: string) {
  const out = env.toJSON();
  const jsonString = JSON.stringify(out, null, 2);

  fs.writeFileSync(fileName, jsonString, "utf8");

  return out;
}
