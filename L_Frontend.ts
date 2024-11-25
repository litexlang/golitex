import { L_Env } from "./L_Env.ts";
import { runStrings } from "./L_Runner.ts";
import { envToJSON, exampleList } from "./L_Test.ts";

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
