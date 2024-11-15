import { L_Env } from "./L_Env.ts";
import { runString } from "./L_Runner.ts";

async function L_REPL() {
  const env = new L_Env(undefined);
  console.log("LiTeX 0.0.1\n");
  console.log(
    `More information about LiTeX is available at <https://github.com/malloc-realloc/tslitex>\n`
  );
  console.log(`Exit by inputting 'exit'\n`);

  if (Deno.args.length > 0) {
    const filename = Deno.args[0];
    try {
      const fileContent = await Deno.readTextFile(filename);
      console.log(`Running file: ${filename}\n`);
      runString(env, fileContent, true, false);
      console.log(`End Running file: ${filename}\n`);
    } catch (err) {
      if (err instanceof Error)
        console.error(
          `Error: Unable to read file "${filename}": ${err.message}\n`
        );
      else console.error(`Error: Unable to read file ${filename}\n`);
    }
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

L_REPL();
