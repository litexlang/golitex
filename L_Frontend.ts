import type { L_Env } from "./L_Env.ts";

export function testEnvToJSON(env: L_Env, fileName: string) {
  const out = env.toJSON();
  // Convert the JSON object to a string and then to Uint8Array
  const jsonString = JSON.stringify(out, null, 2);
  const encoder = new TextEncoder();
  const data = encoder.encode(jsonString);

  Deno.writeFileSync(fileName, data);
  return out;
}
