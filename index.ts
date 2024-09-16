import { readFileSync } from "fs";
import { scan } from "./lexer";

const fileContent: string = readFileSync("example_914.txt", "utf-8");
const tokens = scan(fileContent);
console.log(tokens);
