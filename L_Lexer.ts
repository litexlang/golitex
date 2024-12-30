// // import { L_Keywords, specialChars } from "./L_Keywords";
// // import { L_Env } from "./L_Env";

// // class L_Tokens {
// //   constructor(
// //     public sc: string,
// //     public tokens: [number, number][],
// //     public curTok: number
// //   ) {}

// //   shift(): string {
// //     const out = this.sc.slice(
// //       this.tokens[this.curTok][0],
// //       this.tokens[this.curTok][1]
// //     );
// //     this.curTok += 1;

// //     return out;
// //   }
// // }

// // export function L_Scan(env: L_Env, text: string): string[] {
// //   const tokens: string[] = [];
// //   let currentToken = "";
// //   let inLineComment = false;
// //   let inBlockComment = false;

// //   for (let i = 0; i < text.length; i++) {
// //     const char = text[i];

// //     // Handle end of block comments
// //     if (inBlockComment) {
// //       if (char === "*" && text[i + 1] === "/") {
// //         inBlockComment = false;
// //         i++; // Skip the '/'
// //       }
// //       continue;
// //     }

// //     // Handle end of line comments
// //     if (inLineComment) {
// //       if (char === "\n") {
// //         inLineComment = false;
// //       }
// //       continue;
// //     }

// //     // Start of line comments
// //     if (char === "/" && text[i + 1] === "/") {
// //       inLineComment = true;
// //       if (currentToken) {
// //         tokens.push(currentToken);
// //         currentToken = "";
// //       }
// //       i++; // Skip the next '/'
// //       continue;
// //     }

// //     // Start of block comments
// //     if (char === "/" && text[i + 1] === "*") {
// //       inBlockComment = true;
// //       if (currentToken) {
// //         tokens.push(currentToken);
// //         currentToken = "";
// //       }
// //       i++; // Skip the '*'
// //       continue;
// //     }

// //     // Handle "::" token
// //     if (char === ":" && text[i + 1] === ":") {
// //       if (currentToken) {
// //         tokens.push(currentToken);
// //         currentToken = "";
// //       }
// //       tokens.push(":");
// //       i++; // Skip the next ':'
// //       continue;
// //     }

// //     // Handle special characters
// //     if (specialChars.includes(char)) {
// //       if (currentToken) {
// //         tokens.push(currentToken);
// //         currentToken = "";
// //       }
// //       tokens.push(char);
// //     } else if (char.trim() === "") {
// //       // Handle whitespace
// //       if (currentToken) {
// //         tokens.push(currentToken);
// //         currentToken = "";
// //       }
// //     } else {
// //       // Accumulate characters for the current token
// //       currentToken += char;
// //     }
// //   }

// //   // Push the final token if any
// //   if (currentToken) {
// //     tokens.push(currentToken);
// //   }

// //   return tokens;
// // }

// import { L_Keywords, specialChars } from "./L_Keywords";
// import { L_Env } from "./L_Env";

// export function L_Scan(env: L_Env, text: string): L_Tokens {
//   const tokens: [number, number][] = [];
//   let currentToken = "";
//   let inLineComment = false;
//   let inBlockComment = false;
//   let tokenStart = 0;

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
//         tokens.push([tokenStart, i]);
//         currentToken = "";
//       }
//       i++; // Skip the next '/'
//       continue;
//     }

//     // Start of block comments
//     if (char === "/" && text[i + 1] === "*") {
//       inBlockComment = true;
//       if (currentToken) {
//         tokens.push([tokenStart, i]);
//         currentToken = "";
//       }
//       i++; // Skip the '*'
//       continue;
//     }

//     // Handle "::" token
//     if (char === ":" && text[i + 1] === ":") {
//       if (currentToken) {
//         tokens.push([tokenStart, i]);
//         currentToken = "";
//       }
//       tokens.push([i, i + 2]);
//       i++; // Skip the next ':'
//       continue;
//     }

//     // Handle special characters
//     if (specialChars.includes(char)) {
//       if (currentToken) {
//         tokens.push([tokenStart, i]);
//         currentToken = "";
//       }
//       tokens.push([i, i + 1]);
//     } else if (char.trim() === "") {
//       // Handle whitespace
//       if (currentToken) {
//         tokens.push([tokenStart, i]);
//         currentToken = "";
//       }
//     } else {
//       // Accumulate characters for the current token
//       if (!currentToken) {
//         tokenStart = i;
//       }
//       currentToken += char;
//     }
//   }

//   // Push the final token if any
//   if (currentToken) {
//     tokens.push([tokenStart, text.length]);
//   }

//   return new L_Tokens(text, tokens);
// }

// export class L_Tokens {
//   constructor(
//     public sc: string,
//     public tokens: [number, number][],
//     public curTok: number = 0
//   ) {}

//   shift(): string {
//     if (this.curTok >= this.tokens.length) {
//       throw new Error("No more tokens to shift.");
//     }
//     const out = this.sc.slice(
//       this.tokens[this.curTok][0],
//       this.tokens[this.curTok][1]
//     );
//     this.curTok += 1;
//     return out;
//   }

//   peek(further: number = 0): string {
//     if (this.curTok + further >= this.tokens.length) {
//       throw new Error("No more tokens to peek.");
//     }
//     return this.sc.slice(
//       this.tokens[this.curTok + further][0],
//       this.tokens[this.curTok + further][1]
//     );
//   }

//   reset(): void {
//     this.curTok = 0;
//   }

//   isEnd(): boolean {
//     return this.curTok >= this.tokens.length;
//   }

//   curTokIndex(): number {
//     return this.tokens[this.curTok][0];
//   }
// }

import { L_Keywords, specialChars } from "./L_Keywords";
import { L_Env } from "./L_Env";

export class L_Tokens {
  private curPos: number = 0;
  public sc = "";

  constructor(sc: string) {
    this.sc = sc; // necessary, because isEnd is assumed to be equivalent to curPos >= sc.length
  }

  private isSpecialChar(char: string): boolean {
    return specialChars.includes(char);
  }

  private isWhitespace(char: string): boolean {
    return char.trim() === "";
  }

  private readNextToken(): [string, number] | null {
    let currentToken = "";
    let inLineComment = false;
    let inBlockComment = false;
    let tokenStart = this.curPos;

    for (let i = this.curPos; i < this.sc.length; i++) {
      const char = this.sc[i];

      // Handle end of block comments
      if (inBlockComment) {
        if (char === "*" && this.sc[i + 1] === "/") {
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
      if (char === "/" && this.sc[i + 1] === "/") {
        inLineComment = true;
        if (currentToken) {
          return [currentToken, i];
        }
        i++; // Skip the next '/'
        continue;
      }

      // Start of block comments
      if (char === "/" && this.sc[i + 1] === "*") {
        inBlockComment = true;
        if (currentToken) {
          return [currentToken, i];
        }
        i++; // Skip the '*'
        continue;
      }

      // Handle "::" token
      if (char === ":" && this.sc[i + 1] === ":") {
        if (currentToken) {
          return [currentToken, i];
        }
        return ["::", i + 2];
      }

      // Handle special characters
      if (this.isSpecialChar(char)) {
        if (currentToken) {
          return [currentToken, i];
        }
        return [char, i + 1];
      } else if (this.isWhitespace(char)) {
        // Handle whitespace
        if (currentToken) {
          return [currentToken, i];
        }
        tokenStart = i + 1;
      } else {
        // Accumulate characters for the current token
        if (!currentToken) {
          tokenStart = i;
        }
        currentToken += char;
      }
    }

    // Return the final token if any
    if (currentToken) {
      return [currentToken, this.sc.length];
    }

    return null;
  }

  shift(): string {
    const [token, nextPos] = this.readNextToken() as [string, number];
    this.curPos = nextPos;
    return token;
  }

  peek(further: number = 0): string {
    let tempPos = this.curPos;
    let token: string = "";

    for (let i = 0; i <= further; i++) {
      [token, tempPos] = this.readNextToken() as [string, number];
    }

    return token;
  }

  reset(): void {
    this.curPos = 0;
  }

  isEnd(): boolean {
    if (this.readNextToken() === null) return true;
    else return false;
  }

  curTokIndex(): number {
    return this.curPos;
  }

  viewCurTokSurroundings(): string {
    const viewWidth = 25;

    return this.sc.slice(
      Math.max(0, this.curPos - viewWidth),
      Math.min(this.sc.length, this.curPos + viewWidth)
    );
  }

  toString() {
    return `curTok: at ${this.curPos} "${this.peek()}"`;
  }
}
