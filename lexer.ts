import { specialChars } from "./common";

export function scan(text: string): string[] {
  const tokens: string[] = [];
  let currentToken = "";
  let inComment = false;
  let inEscape = false;

  for (let i = 0; i < text.length; i++) {
    const char = text[i];

    if (inEscape) {
      if (char === "\n" || i === text.length - 1) {
        inEscape = false;
      }
      continue;
    }

    if (char === "\\") {
      inEscape = true;
      continue;
    }

    if (inComment) {
      if (char === "\n") {
        inComment = false;
      }
      continue;
    }

    // use // as comment
    if (char === "/" && text[i + 1] === "/") {
      inComment = true;
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
      continue;
    }

    if (char === ":" && text[i + 1] === ":") {
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
      tokens.push(":");
      i++;
      continue;
    }

    // notice specialChars.includes('\n')
    if (specialChars.includes(char)) {
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
      tokens.push(char);
    } else if (char.trim() === "") {
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
    } else {
      currentToken += char;
    }
  }

  if (currentToken) {
    tokens.push(currentToken);
  }

  // tokens.push("_EOF");

  return tokens;
}
