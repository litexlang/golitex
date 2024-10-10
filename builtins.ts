import { CallOptNode, LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";
import { ExecInfo, execInfo, hRunErr, RType } from "./executor";

export const LiTeXBuiltinKeywords: {
  [key: string]: (env: LiTeXEnv, node: LiTeXNode) => ExecInfo;
} = {
  is_def: (env: LiTeXEnv, node: LiTeXNode): ExecInfo => {
    const T = env.getDeclaredTemplate((node as CallOptNode).optParams[0][0])
      ? execInfo(RType.True)
      : execInfo(RType.False);
    if (!T)
      return hRunErr(
        env,
        RType.Error,
        `${(node as CallOptNode).optName} is not declared.`
      );
    else return execInfo(RType.True);
  },
};
