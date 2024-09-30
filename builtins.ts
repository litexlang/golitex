import { CallOptNode, LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";
import { ExecInfo, execInfo, ResultType } from "./executor";

export const LiTeXBuiltinKeywords: {
  [key: string]: (env: LiTeXEnv, node: LiTeXNode) => ExecInfo;
} = {
  is_def: (env: LiTeXEnv, node: LiTeXNode): ExecInfo => {
    return env.getDeclaredTemplate((node as CallOptNode).optParams[0][0])
      ? execInfo(ResultType.True)
      : execInfo(ResultType.False);
  },
};
