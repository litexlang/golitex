import { L_Env } from "./L_Env.ts";
import { runStrings } from "./L_Run.ts";

const setTheory = [
  "def object(x);",
  "def set(x);",
  "know if x: set(x) => {obj(x)};",
];

const setTheoryTest1 = [
  "let A,B,x : A is set, B is set, equal(A,B), element_of(x,A);",
  "by set_equal(A,B,x) => {element_of(x,B)};",
  "know if x, y : x is empty, y is empty => {equal(x,y)};",
  "let s1, s2 : s1 is empty, s2 is empty;",
  "equal(s1,s2);",
];

const setTheoryDict: { [s: string]: [string[], boolean, boolean] } = {
  setTheory: [setTheory, true, false],
  setTheoryTest1: [setTheoryTest1, true, true],
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
