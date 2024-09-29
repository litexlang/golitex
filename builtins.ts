import { CallOptNode, LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";
import { ExecInfo, resultInfo, ResultType } from "./executor";

export const LiTeXBuiltinKeywords: {
  [key: string]: (env: LiTeXEnv, node: LiTeXNode) => ExecInfo;
} = {
  is_def: (env: LiTeXEnv, node: LiTeXNode): ExecInfo => {
    return env.getDeclaredTemplate((node as CallOptNode).optParams[0][0])
      ? resultInfo(ResultType.True)
      : resultInfo(ResultType.False);
  },
};
