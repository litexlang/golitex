import type { L_Env } from "./L_Env.ts";
import { L_Out } from "./L_Executor.ts";

export function lstLengthNotEql(
  env: L_Env,
  lst1: unknown[],
  lst2: unknown[],
): L_Out {
  env.newMessage(
    `Error: ${lst1} and ${lst2} are supposed to have the same length.`,
  );

  return L_Out.Error;
}
