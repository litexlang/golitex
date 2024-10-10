import { CallOptNode, LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";
import { Rinfo, Rinfo, hRunErr, RType } from "./executor";

export const LiTeXBuiltinKeywords: {
  [key: string]: (env: LiTeXEnv, node: LiTeXNode) => Rinfo;
} = {
  is_def: (env: LiTeXEnv, node: LiTeXNode): Rinfo => {
    const T = env.getDeclaredTemplate((node as CallOptNode).optParams[0][0])
      ? Rinfo(RType.True)
      : Rinfo(RType.False);
    if (!T)
      return hRunErr(
        env,
        RType.Error,
        `${(node as CallOptNode).optName} is not declared.`
      );
    else return Rinfo(RType.True);
  },
};
