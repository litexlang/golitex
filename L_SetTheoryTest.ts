import { L_Env } from "./L_Env.ts";
import { runStrings } from "./L_Run.ts";

const setTheory = [
  "def object(x);",
  "def set(x);",
  "know if x: set(x) => {object(x)};",
  "def subset(A,B);",
  "def in(x,A);",
  "let A,B,C: A,B,C are set;",
];

const setTheoryTest1 = [
  "let A,B,x : A is set, B is set, equal(A,B), element_of(x,A);",
  "by set_equal(A,B,x) => {element_of(x,B)};",
  "know if x, y : x is empty, y is empty => {equal(x,y)};",
  "let s1, s2 : s1 is empty, s2 is empty;",
  "equal(s1,s2);",
];

const setTheory2 = [
  "know if A, B: A,B are set => {if x: if in(x,A) => {in(x,B)} => {subset(A,B)}};",
  "know if x: in(x,A) => {in(x,B)};",
  "subset(A,B);",
  "know subset(B,C);",
  "if A,B,C: A,B,C are set, subset(A,B), subset(B,C) => {if x: in(x,A) => {in(x,B), in(x,C)}, subset(A,C)};",
  "subset(A,C);",
];

const setTheory3 = [
  "def specification(P,A) : is_property(P, 1), set(A) exist B: {B is set, if x: in(x,B) => {P(x), in(x,A)}, if x: P(x), in(x,A) => {in(x,B)} };",
  "have specification(object, A) : objects_in_A;",
  "objects_in_A is set;",
];

const setTheory4 = [
  "know if y: y is object => {exist x: {P(x,y)}[replacement]};",
];

const setTheoryDict: { [s: string]: [string[], boolean, boolean] } = {
  setTheory: [setTheory, true, false],
  setTheoryTest1: [setTheoryTest1, false, false],
  setTheory2: [setTheory2, false, false],
  setTheory3: [setTheory3, false, false],
  setTheory4: [setTheory4, true, true],
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
