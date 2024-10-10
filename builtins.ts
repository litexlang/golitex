import { CallOptNode, LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";
import { hInfo, rInfo, hRunErr, RType } from "./executor";

export const LiTeXBuiltinKeywords: {
  [key: string]: (env: LiTeXEnv, node: LiTeXNode) => rInfo;
} = {
  is_def: (env: LiTeXEnv, node: LiTeXNode): rInfo => {
    const T = env.getDeclaredTemplate((node as CallOptNode).optParams[0][0])
      ? hInfo(RType.True)
      : hInfo(RType.False);
    if (!T)
      return hRunErr(
        env,
        RType.Error,
        `${(node as CallOptNode).optName} is not declared.`
      );
    else return hInfo(RType.True);
  },
};
