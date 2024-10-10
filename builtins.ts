import { CallOptNode, L_Node } from "./ast";
import { L_Env } from "./env";
import { hInfo, RInfo, hRunErr, RType } from "./executor";

export const L_Builtins: {
  [key: string]: (env: L_Env, node: L_Node) => RInfo;
} = {
  is_def: (env: L_Env, node: L_Node): RInfo => {
    const T = env.getRelT((node as CallOptNode).optParams[0][0])
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
