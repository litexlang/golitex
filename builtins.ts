import { CallOptNode, LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";
import { hInfo, RInfo, hRunErr, RType } from "./executor";

export const LiTeXBuiltinKeywords: {
  [key: string]: (env: LiTeXEnv, node: LiTeXNode) => RInfo;
} = {
  is_def: (env: LiTeXEnv, node: LiTeXNode): RInfo => {
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
