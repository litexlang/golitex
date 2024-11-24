import { L_Env } from "./L_Env.ts";
import { runStrings } from "./L_Runner.ts";
import { exampleList } from "./L_Test.ts";

export function envToJSON(env: L_Env, fileName: string) {
  const out = env.toJSON();
  // Convert the JSON object to a string and then to Uint8Array
  const jsonString = JSON.stringify(out, null, 2);
  const encoder = new TextEncoder();
  const data = encoder.encode(jsonString);

  Deno.writeFileSync(fileName, data);
  return out;
}

function testEnvToJSON() {
  const env = new L_Env();
  for (const example of exampleList) {
    if (example.debug) {
      console.log(example.name);
      runStrings(env, example.code, example.print);
    }
  }
  envToJSON(env, "env.json");
}

testEnvToJSON();
