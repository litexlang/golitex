import { L_Env } from "./L_Env.ts";
import { runString } from "./L_Runner.ts";

function L_REPL() {
  const env = new L_Env(undefined);
  console.log("LiTeX 0.0.1");
  console.log(
    `More information about LiTeX is available at <https://github.com/malloc-realloc/tslitex>\n`
  );
  console.log(`Exit by inputting 'exit'\n`);
  while (true) {
    const expr = prompt(">");
    if (expr === "exit") {
      console.log("See you later.");
      break;
    }
    if (expr === null) continue;
    runString(env, expr, true, false);
  }
}

L_REPL();
