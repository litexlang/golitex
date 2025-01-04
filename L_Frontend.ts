import { writeFileSync } from "fs";
import { L_Env } from "./L_Env";
import { runString } from "./L_Runner";
import { L_Out } from "./L_Structs";

export function LiTeXnbInteract(
  env: L_Env,
  text: string
): { newEnv: L_Env; messages: string[] } {
  const newEnv = new L_Env(env);

  try {
    const outs = runString(newEnv, text);
    if (outs !== undefined) {
      for (const out of outs) {
        if (out !== L_Out.True) throw Error();
      }

      return { newEnv: newEnv, messages: newEnv.getMessages() };
    } else throw Error();
  } catch {
    return { newEnv: env, messages: newEnv.getMessages() };
  }
}

function envToJSON(env: L_Env, fileName: string) {
  const out = env.toJSON();
  const jsonString = JSON.stringify(out, null, 2);
  writeFileSync(fileName, jsonString, "utf8");
  return out;
}
