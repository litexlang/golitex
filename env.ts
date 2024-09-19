import { DefNode } from "./ast";

export class LiTeXEnv {
  errors: string[] = [];
  defs: Map<string, DefNode> = new Map<string, DefNode>();
  constructor() {}

  pushErrorMessage(s: string) {
    this.errors.push(s);
  }

  keyInDefs(s: string) {
    return this.defs.has(s);
  }
}
