import { CallOptNode, DefNode } from "./ast";

export class LiTeXEnv {
  errors: string[] = [];
  defs: Map<string, DefNode> = new Map<string, DefNode>();
  //! string[] will be symbols[] because $$
  facts: CallOptNode[] = [];

  constructor() {}

  pushErrorMessage(s: string) {
    this.errors.push(s);
  }

  keyInDefs(s: string) {
    return this.defs.has(s);
  }

  newFact(optNode: CallOptNode) {
    this.facts.push(optNode);
  }

  //! has not introduce # here.
  isFact(optNode: CallOptNode): Boolean {
    for (let i = 0; i < this.facts.length; i++) {
      const length = this.facts[i].opts.length;
      if (length !== optNode.opts.length) continue;

      let indeedFact = 1;
      for (let j = 0; j < length; j++) {
        const targetNode = this.facts[i].opts[j];
        if (targetNode[0] !== optNode.opts[j][0]) {
          indeedFact = 0;
          break;
        }
        if (!strListEql(targetNode[1], optNode.opts[j][1])) {
          indeedFact = 0;
          break;
        }
      }

      if (indeedFact) return true;
    }
    return false;
  }
}

function strListEql(lst1: string[], lst2: string[]): Boolean {
  if (lst1.length !== lst2.length) {
    return false;
  }
  for (let i = 0; i < lst1.length; i++) {
    if (lst1[i] !== lst2[i]) {
      return false;
    }
  }
  return true;
}
