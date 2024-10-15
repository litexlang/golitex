import { FactNode, L_Node } from "./ast";
import { L_Env } from "./env";
import { hInfo, RType } from "./executor";
import { cEnvRType, cL_Out, RL_Out } from "./shared";

export const L_Builtins: {
  [key: string]: (env: L_Env, node: L_Node) => RType;
} = {
  is_def: (env: L_Env, node: L_Node): RType => {
    const T = env.getRelT((node as FactNode).optParams[0][0])
      ? hInfo(RType.True)
      : hInfo(RType.False);
    if (!T)
      return cEnvRType(
        env,
        RType.Error,
        `${(node as FactNode).optName} is not declared.`
      );
    else return RType.True;
  },
};
