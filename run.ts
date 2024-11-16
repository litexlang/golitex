import { L_Env } from "./L_Env.ts";
import { runFile, runString } from "./L_Runner.ts";

async function L_REPL(files: string[]) {
  const env = new L_Env(undefined);
  console.log("LiTeX 0.0.1\n");
  console.log(
    `More information about LiTeX is available at <https://github.com/malloc-realloc/tslitex>\n`
  );
  console.log(`Exit by inputting 'exit'\n`);

  if (Deno.args.length > 0) {
    const fileName = Deno.args[0];
    await runFile(env, fileName, true, false);
  }

  for (const fileName of files) {
    await runFile(env, fileName, true, false);
  }

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

L_REPL([]);
