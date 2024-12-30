// import { L_Keywords, specialChars } from "./L_Keywords";
// import { L_Env } from "./L_Env";

// class L_Tokens {
//   constructor(
//     public sc: string,
//     public tokens: [number, number][],
//     public curTok: number
//   ) {}

//   shift(): string {
//     const out = this.sc.slice(
//       this.tokens[this.curTok][0],
//       this.tokens[this.curTok][1]
//     );
//     this.curTok += 1;

//     return out;
//   }
// }

// export function L_Scan(env: L_Env, text: string): string[] {
//   const tokens: string[] = [];
//   let currentToken = "";
//   let inLineComment = false;
//   let inBlockComment = false;

//   for (let i = 0; i < text.length; i++) {
//     const char = text[i];

//     // Handle end of block comments
//     if (inBlockComment) {
//       if (char === "*" && text[i + 1] === "/") {
//         inBlockComment = false;
//         i++; // Skip the '/'
//       }
//       continue;
//     }

//     // Handle end of line comments
//     if (inLineComment) {
//       if (char === "\n") {
//         inLineComment = false;
//       }
//       continue;
//     }

//     // Start of line comments
//     if (char === "/" && text[i + 1] === "/") {
//       inLineComment = true;
//       if (currentToken) {
//         tokens.push(currentToken);
//         currentToken = "";
//       }
//       i++; // Skip the next '/'
//       continue;
//     }

//     // Start of block comments
//     if (char === "/" && text[i + 1] === "*") {
//       inBlockComment = true;
//       if (currentToken) {
//         tokens.push(currentToken);
//         currentToken = "";
//       }
//       i++; // Skip the '*'
//       continue;
//     }

//     // Handle "::" token
//     if (char === ":" && text[i + 1] === ":") {
//       if (currentToken) {
//         tokens.push(currentToken);
//         currentToken = "";
//       }
//       tokens.push(":");
//       i++; // Skip the next ':'
//       continue;
//     }

//     // Handle special characters
//     if (specialChars.includes(char)) {
//       if (currentToken) {
//         tokens.push(currentToken);
//         currentToken = "";
//       }
//       tokens.push(char);
//     } else if (char.trim() === "") {
//       // Handle whitespace
//       if (currentToken) {
//         tokens.push(currentToken);
//         currentToken = "";
//       }
//     } else {
//       // Accumulate characters for the current token
//       currentToken += char;
//     }
//   }

//   // Push the final token if any
//   if (currentToken) {
//     tokens.push(currentToken);
//   }

//   return tokens;
// }

import { L_Keywords, specialChars } from "./L_Keywords";
import { L_Env } from "./L_Env";
import { L_Tokens } from "./L_Structs";

export function L_Scan(env: L_Env, text: string): L_Tokens {
  const tokens: [number, number][] = [];
  let currentToken = "";
  let inLineComment = false;
  let inBlockComment = false;
  let tokenStart = 0;

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
        tokens.push([tokenStart, i]);
        currentToken = "";
      }
      i++; // Skip the next '/'
      continue;
    }

    // Start of block comments
    if (char === "/" && text[i + 1] === "*") {
      inBlockComment = true;
      if (currentToken) {
        tokens.push([tokenStart, i]);
        currentToken = "";
      }
      i++; // Skip the '*'
      continue;
    }

    // Handle "::" token
    if (char === ":" && text[i + 1] === ":") {
      if (currentToken) {
        tokens.push([tokenStart, i]);
        currentToken = "";
      }
      tokens.push([i, i + 2]);
      i++; // Skip the next ':'
      continue;
    }

    // Handle special characters
    if (specialChars.includes(char)) {
      if (currentToken) {
        tokens.push([tokenStart, i]);
        currentToken = "";
      }
      tokens.push([i, i + 1]);
    } else if (char.trim() === "") {
      // Handle whitespace
      if (currentToken) {
        tokens.push([tokenStart, i]);
        currentToken = "";
      }
    } else {
      // Accumulate characters for the current token
      if (!currentToken) {
        tokenStart = i;
      }
      currentToken += char;
    }
  }

  // Push the final token if any
  if (currentToken) {
    tokens.push([tokenStart, text.length]);
  }

  return new L_Tokens(text, tokens);
}
