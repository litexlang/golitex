export function scan(text: string): string[] {
  const specialChars = ["(", ")", "{", "}", ":", ",", ";"];
  const tokens: string[] = [];
  let currentToken = "";
  let inComment = false;

  for (let i = 0; i < text.length; i++) {
    const char = text[i];

    if (inComment) {
      if (char === "\n") {
        inComment = false;
      }
      continue;
    }

    if (char === "/" && text[i + 1] === "/") {
      inComment = true;
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
      continue;
    }

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

  tokens.push("_EOF");

  return tokens;
}
