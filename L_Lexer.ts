import { L_Keywords, specialChars } from "./L_Keywords";
import { L_Env } from "./L_Env";

export function L_Scan(env: L_Env, text: string): string[] {
  const tokens: string[] = [];
  let currentToken = "";
  let inLineComment = false;
  let inBlockComment = false;

  for (let i = 0; i < text.length; i++) {
    const char = text[i];

    // Handle end of block comments
    if (inBlockComment) {
      if (char === "*" && text[i + 1] === "/") {
        inBlockComment = false;
        i++; // Skip the '/'
      }
      continue;
    }

    // Handle end of line comments
    if (inLineComment) {
      if (char === "\n") {
        inLineComment = false;
      }
      continue;
    }

    // Start of line comments
    if (char === "/" && text[i + 1] === "/") {
      inLineComment = true;
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
      i++; // Skip the next '/'
      continue;
    }

    // Start of block comments
    if (char === "/" && text[i + 1] === "*") {
      inBlockComment = true;
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
      i++; // Skip the '*'
      continue;
    }

    // Handle "::" token
    if (char === ":" && text[i + 1] === ":") {
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
      tokens.push(":");
      i++; // Skip the next ':'
      continue;
    }

    // Handle special characters
    if (specialChars.includes(char)) {
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
      tokens.push(char);
    } else if (char.trim() === "") {
      // Handle whitespace
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
    } else {
      // Accumulate characters for the current token
      currentToken += char;
    }
  }

  // Push the final token if any
  if (currentToken) {
    tokens.push(currentToken);
  }

  for (let i = tokens.length - 1; i >= 0; i--) {
    const token = tokens[i];
    if (token.startsWith(L_Keywords.macroPrefix)) {
      const searchKey = token.slice(1);
      const out = env.getMacro(searchKey);
      if (out === undefined) {
        env.report(`${token} is not a declared macro name.`);
        throw Error();
      } else {
        tokens.splice(i, 1, ...out.macroTokens);
      }
    }
  }

  return tokens;
}
