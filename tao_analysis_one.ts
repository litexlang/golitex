import { L_Env } from "./L_Env.ts";
import { runStrings } from "./L_Run.ts";

const setTheory = [
  "def object(x);",
  "def set(x);",
  "know if x: set(x) => {object(x)};",
];

const setTheoryTest1 = [
  "let A,B,x : A is set, B is set, equal(A,B), element_of(x,A);",
  "by set_equal(A,B,x) => {element_of(x,B)};",
  "know if x, y : x is empty, y is empty => {equal(x,y)};",
  "let s1, s2 : s1 is empty, s2 is empty;",
  "equal(s1,s2);",
];

const setTheory2 = [
  "def subset(A,B);",
  "def in(x,A);",
  "know if A, B: A,B are set => {if x: if in(x,A) => {in(x,B)} => {subset(A,B)}};",
  "let A,B,C: A,B,C are set;",
  "know if x: in(x,A) => {in(x,B)};",
  "subset(A,B);",
  "know subset(B,C);",
  "if x: in(x,A) => {in(x,B), in(x,C)};",
  "subset(A,C);",
];

const setTheoryDict: { [s: string]: [string[], boolean, boolean] } = {
  setTheory: [setTheory, true, false],
  setTheoryTest1: [setTheoryTest1, false, false],
  setTheory2: [setTheory2, true, true],
};

function testSetTheory() {
  const env = new L_Env();

  for (const testList in setTheoryDict) {
    const exprs = setTheoryDict[testList];
    if (exprs[1] === false) continue;

    runStrings(env, exprs[0], exprs[2]);
    env.clearMessages();
  }
}

testSetTheory();
