import { CallOptNode } from "./ast";
import { LiTeXEnv } from "./env";
import { catchRuntimeError, ResultType } from "./executor";

export const builtInCallOptNames: { [key: string]: Function } = {
  isDef: isDefFunc,
};

export function isDefFunc(env: LiTeXEnv, node: CallOptNode): ResultType {
  try {
    if (node.opts[0][1].length !== 1) {
      throw new Error("isDef has one parameter, get too many inputs");
    }

    const name: string = node.opts[0][1][0];
    if (env.keyInDefs(name)) {
      return ResultType.True;
    } else {
      return ResultType.False;
    }
  } catch (error) {
    catchRuntimeError(env, error, "isDef");
    return ResultType.Error;
  }
}
