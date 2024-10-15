import { FactNode, L_Node } from "./ast";
import { L_Env } from "./env";
import { hInfo, RType } from "./executor";
import { cEnvErrL_Out, cL_Out, RL_Out } from "./shared";

export const L_Builtins: {
  [key: string]: (env: L_Env, node: L_Node) => RL_Out;
} = {
  is_def: (env: L_Env, node: L_Node): RL_Out => {
    const T = env.getRelT((node as FactNode).optParams[0][0])
      ? hInfo(RType.True)
      : hInfo(RType.False);
    if (!T)
      return cEnvErrL_Out(
        env,
        RType.Error,
        `${(node as FactNode).optName} is not declared.`
      );
    else return cL_Out(RType.True);
  },
};
