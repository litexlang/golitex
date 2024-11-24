import type { L_Env } from "./L_Env.ts";

export function testEnvToJSON(env: L_Env) {
  const out = env.toJSON();
  return out;
}
