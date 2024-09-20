import { CallOptNode, DefNode } from "./ast";

export class LiTeXEnv {
  errors: string[] = [];
  defs: Map<string, DefNode> = new Map<string, DefNode>();
  //! string[] will be symbols[] because $$
  callOptFacts: Map<string, string[][][]> = new Map<string, string[][][]>();
  fatherFreeVars: string[][] = [];
  defDepth = 0;
  snapShot = { defDepth: 0, fatherFreeVars: [] as string[][] };

  isDefMode() {
    return this.defDepth !== 0;
  }

  clearUpSnapShot() {
    return { defDepth: 0, fatherFreeVars: [] as string[][] };
  }

  setSnapShot() {
    this.snapShot.defDepth = this.defDepth;
    this.snapShot.fatherFreeVars = [...this.fatherFreeVars];
  }

  returnToSnapShot() {
    this.defDepth = this.snapShot.defDepth;
    this.fatherFreeVars = this.snapShot.fatherFreeVars;
    this.clearUpSnapShot();
  }

  constructor() {}

  pushErrorMessage(s: string) {
    this.errors.push(s);
  }

  keyInDefs(s: string) {
    return this.defs.has(s);
  }

  callOptNodeName(optNode: CallOptNode) {
    return optNode.opts.map((e) => e[0]).join("::");
  }

  getFromCallOptFacts(optNode: CallOptNode) {
    const optName: string = optNode.opts.map((e) => e[0]).join("::");
    const validParamsLst = this.callOptFacts.get(optName);
    return validParamsLst;
  }

  newFact(node: CallOptNode) {
    // check whether it's truly a new fact
    if (this.isCallOptFact(node)) {
      return;
    } else {
      if (!this.getFromCallOptFacts(node)) {
        this.callOptFacts.set(this.callOptNodeName(node), [
          node.opts.map((e) => e[1]),
        ]);
      } else {
        this.callOptFacts
          .get(this.callOptNodeName(node))
          ?.push(node.opts.map((e) => e[1]));
      }
    }
  }

  //! has not introduce # here.
  isCallOptFact(optNode: CallOptNode): Boolean {
    const validParamsLst = this.getFromCallOptFacts(optNode);
    if (!validParamsLst) return false;

    for (const item of validParamsLst) {
      let sig = true;
      for (let i = 0; i < item.length; i++) {
        if (!strListEql(item[i], optNode.opts[i][1])) {
          sig = false;
          break;
        }
      }
      if (sig) return true;
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
