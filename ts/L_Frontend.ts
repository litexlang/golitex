import { L_Env } from "./L_Env";
import { runString } from "./L_Runner";
import { L_Out } from "./L_Structs";

export function L_InteractWithFrontend(
  env: L_Env,
  text: string
): { env: L_Env; messages: string[] } {
  try {
    const outs = runString(env, text);
    if (outs !== undefined) {
      for (const out of outs) {
        if (out !== L_Out.True) throw Error();
      }
      return { env: env, messages: env.getMessages() };
    } else throw Error();
  } catch {
    return { env: env, messages: env.getMessages() };
  }
}
