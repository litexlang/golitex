// import { L_Keywords, specialChars } from "./L_Keywords";
// import { L_Env } from "./L_Env";

// export class L_Tokens {
//   private curPos: number = 0;
//   public sc = "";

//   constructor(sc: string) {
//     this.sc = sc; // necessary, because isEnd is assumed to be equivalent to curPos >= sc.length
//   }

//   private isSpecialChar(char: string): boolean {
//     return specialChars.includes(char);
//   }

//   private isWhitespace(char: string): boolean {
//     return char.trim() === "";
//   }

//   private readNextToken(): [string, number] | null {
//     let currentToken = "";
//     let inLineComment = false;
//     let inBlockComment = false;
//     let tokenStart = this.curPos;

//     for (let i = this.curPos; i < this.sc.length; i++) {
//       const char = this.sc[i];

//       // Handle end of block comments
//       if (inBlockComment) {
//         if (char === "*" && this.sc[i + 1] === "/") {
//           inBlockComment = false;
//           i++; // Skip the '/'
//         }
//         continue;
//       }

//       // Handle end of line comments
//       if (inLineComment) {
//         if (char === "\n") {
//           inLineComment = false;
//         }
//         continue;
//       }

//       // Start of line comments
//       if (char === "/" && this.sc[i + 1] === "/") {
//         inLineComment = true;
//         if (currentToken) {
//           return [currentToken, i];
//         }
//         i++; // Skip the next '/'
//         continue;
//       }

//       // Start of block comments
//       if (char === "/" && this.sc[i + 1] === "*") {
//         inBlockComment = true;
//         if (currentToken) {
//           return [currentToken, i];
//         }
//         i++; // Skip the '*'
//         continue;
//       }

//       // Handle "::" token
//       if (char === ":" && this.sc[i + 1] === ":") {
//         if (currentToken) {
//           return [currentToken, i];
//         }
//         return ["::", i + 2];
//       }

//       // Handle special characters
//       if (this.isSpecialChar(char)) {
//         if (currentToken) {
//           return [currentToken, i];
//         }
//         return [char, i + 1];
//       } else if (this.isWhitespace(char)) {
//         // Handle whitespace
//         if (currentToken) {
//           return [currentToken, i];
//         }
//         tokenStart = i + 1;
//       } else {
//         // Accumulate characters for the current token
//         if (!currentToken) {
//           tokenStart = i;
//         }
//         currentToken += char;
//       }
//     }

//     // Return the final token if any
//     if (currentToken) {
//       return [currentToken, this.sc.length];
//     }

//     return null;
//   }

//   shift(): string {
//     const [token, nextPos] = this.readNextToken() as [string, number];
//     this.curPos = nextPos;
//     return token;
//   }

//   peek(further: number = 0): string {
//     let tempPos = this.curPos;
//     let token: string = "";

//     for (let i = 0; i <= further; i++) {
//       [token, tempPos] = this.readNextToken() as [string, number];
//     }

//     return token;
//   }

//   reset(): void {
//     this.curPos = 0;
//   }

//   isEnd(): boolean {
//     if (this.readNextToken() === null) return true;
//     else return false;
//   }

//   curTokIndex(): number {
//     return this.curPos;
//   }

//   viewCurTokSurroundings(): string {
//     const viewWidth = 25;

//     return this.sc.slice(
//       Math.max(0, this.curPos - viewWidth),
//       Math.min(this.sc.length, this.curPos + viewWidth)
//     );
//   }

//   toString() {
//     return `curTok: at ${this.curPos} "${[0, 1, 2].map((e) => this.peek(e))} "`;
//   }
// }

import { L_KW, specialChars } from "./L_Keywords";
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

  private readNextToken(startPos: number): [string, number] | null {
    let currentToken = "";
    let inLineComment = false;
    let inBlockComment = false;
    let tokenStart = startPos;

    for (let i = startPos; i < this.sc.length; i++) {
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
    const [token, nextPos] = this.readNextToken(this.curPos) as [
      string,
      number
    ];
    this.curPos = nextPos;
    return token;
  }

  peek(further: number = 0): string {
    let tempPos = this.curPos;
    let token: string = "";

    for (let i = 0; i <= further; i++) {
      const result = this.readNextToken(tempPos);
      if (!result) {
        return "";
      }
      [token, tempPos] = result;
    }

    return token;
  }

  reset(): void {
    this.curPos = 0;
  }

  isEnd(): boolean {
    return this.readNextToken(this.curPos) === null;
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
    return `at ${this.curPos} "${[0, 1, 2, 3, 4, 5]
      .map((e) => this.peek(e))
      .join(" ")} "`;
  }
}
