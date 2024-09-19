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

    // 检查 :: 分隔符
    if (char === ":" && text[i + 1] === ":") {
      if (currentToken) {
        tokens.push(currentToken);
        currentToken = "";
      }
      tokens.push("::");
      i++; // 跳过下一个 ":"
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
