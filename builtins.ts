import { CallOptNode, LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";
import { ExecInfo, execInfo, handleRuntimeError, ResultType } from "./executor";

export const LiTeXBuiltinKeywords: {
  [key: string]: (env: LiTeXEnv, node: LiTeXNode) => ExecInfo;
} = {
  is_def: (env: LiTeXEnv, node: LiTeXNode): ExecInfo => {
    const T = env.getDeclaredTemplate((node as CallOptNode).optParams[0][0])
      ? execInfo(ResultType.True)
      : execInfo(ResultType.False);
    if (!T)
      return handleRuntimeError(
        env,
        ResultType.Error,
        `${(node as CallOptNode).optName} is not declared.`
      );
    else return execInfo(ResultType.True);
  },
};
