import { readFileSync } from "fs";
import { scan } from "./lexer";
import { LiTeXEnv } from "./env";
import { LiTeXParse } from "./parser";

const codes: string[] = [
  // "def object(x) {object(x), object2(x)}",
  "know object;",
];

function testLexer() {
  const fileContent: string = readFileSync("example_914.txt", "utf-8");
  const tokens = scan(fileContent);
  console.log(tokens[tokens.length - 1]);
}

function testParser() {
  const env = new LiTeXEnv();
  for (let i = 0; i < codes.length; i++) {
    const tokens = scan(codes[i]);
    console.log(LiTeXParse(env, tokens));
  }
}

testParser();
