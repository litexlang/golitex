import { CallOptNode } from "./ast";
import { LiTeXEnv } from "./env";

function test_is_fact() {
  const env = new LiTeXEnv();
  const callOptNode = new CallOptNode([
    ["set", ["a", "b"]],
    [">", ["21", "2"]],
  ]);
  const callOptNode2 = new CallOptNode([
    ["set", ["a", "b"]],
    [">", ["21", "2", "3"]],
  ]);
  env.newFact(callOptNode);
  console.log(env.isCallOptFact(callOptNode2));
}

test_is_fact();
