import {
  CallOptNode,
  InferNode,
  DefNode,
  LiTexNodeType,
  LiTeXNode,
  CallOptsNode,
} from "./ast";

type SnapShot = { fatherFreeVars: string[][] };

export class LiTeXEnv {
  errors: string[] = [];
  infers: Map<string, InferNode> = new Map<string, InferNode>();
  //! string[] will be symbols[] because $$
  callOptFacts: Map<string, string[][][]> = new Map<string, string[][][]>();
  fatherFreeVars: string[][] = [];
  declaredVars: string[] = [];
  defs: Map<string, DefNode> = new Map<string, DefNode>();

  callOptType(node: CallOptNode) {
    return this.optType(node.optName);
  }

  optType(s: string): LiTexNodeType {
    let node: LiTeXNode = this.infers.get(s) as LiTeXNode;
    if (node) return LiTexNodeType.InferNode;
    node = this.defs.get(s) as LiTeXNode;
    if (node) return LiTexNodeType.DefNode;
    return LiTexNodeType.Error;
  }

  returnToSnapShot(original: SnapShot) {
    this.fatherFreeVars = original.fatherFreeVars;
  }

  getSnapShot(): SnapShot {
    return { fatherFreeVars: [...this.fatherFreeVars] };
  }

  constructor() {}

  pushErrorMessage(s: string) {
    this.errors.push(s);
  }

  keyInDefs(s: string) {
    return this.infers.has(s);
  }

  callOptNodeName(optNode: CallOptNode) {
    return optNode.optName;
  }

  getFromCallOptFacts(optNode: CallOptNode) {
    const optName: string = optNode.optName;
    const validParamsLst = this.callOptFacts.get(optName);
    return validParamsLst;
  }

  newFact(node: CallOptNode) {
    // check whether it's truly a new fact
    // if (this.isCallOptFact(node)) {
    //   return;
    // } else
    {
      if (!this.getFromCallOptFacts(node)) {
        this.callOptFacts.set(this.callOptNodeName(node), [node.optParams]);
      } else {
        this.callOptFacts.get(this.callOptNodeName(node))?.push(node.optParams);
      }
    }
  }

  isCallOptFact(optNode: CallOptNode): Boolean {
    function paramsIsValid(lst1: string[], lst2: string[]): Boolean {
      if (lst1.length !== lst2.length) {
        return false;
      }
      for (let i = 0; i < lst1.length; i++) {
        // The reason why [0] exists in lst1[i][0] is that user sometimes want to specify sequence of given parameter
        if (lst1[i] !== lst2[i] && lst1[i][0] !== "#") {
          return false;
        }
      }
      return true;
    }

    const validParamsLst = this.getFromCallOptFacts(optNode);
    if (!validParamsLst) return false;

    for (const item of validParamsLst) {
      for (let i = 0; i < item.length; i++) {
        if (paramsIsValid(item[i], optNode.optParams[i])) {
          return true;
        }
      }
    }

    return false;
  }

  printCallOptFacts() {
    console.log("----callOpt------\n");
    for (const [key, value] of this.callOptFacts) {
      console.log("[opt]  " + key);
      for (const item of value) {
        console.log(item);
      }
    }
    console.log("");
  }

  printInfers() {
    console.log("------infer-------\n");
    for (const [key, value] of this.infers) {
      console.log("[infer]  " + key);
      console.log(value.params);
      console.log("requirements:");
      for (const item of value.requirements) {
        console.log(item);
      }
      console.log("onlyIfs:");
      for (const item of value.onlyIfExprs) {
        console.log(item);
      }
    }
    console.log("");
  }

  newFacts(node: LiTeXNode) {
    if (node.type === LiTexNodeType.CallOptsNode) {
      for (const [j, callOptNode] of (node as CallOptsNode).nodes.entries()) {
        this.newFact(callOptNode);
      }
    }
  }
}

function strLstEql(lst1: string[], lst2: string[]): Boolean {
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
