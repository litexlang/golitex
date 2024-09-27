import {
  CallOptNode,
  InferNode,
  DefNode,
  LiTexNodeType,
  LiTeXNode,
  CallOptsNode,
  TemplateNode,
  FactNode,
  areStrArrStructureEqual,
} from "./ast";
import { OptsConnectionSymbol } from "./common";
import { ExecInfo, resultInfo, ResultType } from "./executor";

// type SnapShot = { fatherFreeVars: string[][] };

export type FactAboutGivenOpt = { params: string[][]; onlyIfs: CallOptNode[] };

export type TemplateFact = {
  subTemplates: Map<string, TemplateFact>;
  facts: string[][][];
  templateNode: TemplateNode;
};

export class LiTeXEnv {
  errors: string[] = [];
  infers: Map<string, InferNode> = new Map<string, InferNode>();
  callOptFacts: Map<string, string[][][]> = new Map<string, string[][][]>();
  declaredVars: string[] = [];
  defs: Map<string, DefNode> = new Map<string, DefNode>();
  callOptFactsOnlyIfs: Map<string, FactAboutGivenOpt[]> = new Map<
    string,
    FactAboutGivenOpt[]
  >();

  declaredTemplates: Map<string, TemplateNode> = new Map<
    string,
    TemplateNode
  >();

  pushNewFact(fact: FactNode): ExecInfo {
    const declaredTemplate = this.getDeclaredTemplate(fact.optName);
    if (!declaredTemplate)
      return resultInfo(
        ResultType.Error,
        fact.optName + "has not been declared"
      );
    declaredTemplate?.facts.push(fact.optParams);
    return resultInfo(ResultType.KnowTrue);
  }

  // facts: Map<string, TemplateFact> = new Map<string, TemplateFact>();

  checkFact(calledFact: FactNode): ExecInfo {
    const declaredTemplate = this.getDeclaredTemplate(calledFact.optName);
    if (!declaredTemplate)
      return resultInfo(
        ResultType.Error,
        calledFact.optName + " has not been declared."
      );
    for (const value of declaredTemplate?.facts) {
      if (areNestedArraysEqual(value, calledFact.optParams)) {
        return resultInfo(ResultType.True);
      }
    }

    return resultInfo(ResultType.Unknown);

    function areNestedArraysEqual(arr1: string[][], arr2: string[][]): boolean {
      if (arr1.length !== arr2.length) {
        return false;
      }

      for (let i = 0; i < arr1.length; i++) {
        if (arr1[i].length !== arr2[i].length) {
          return false;
        }

        for (let j = 0; j < arr1[i].length; j++) {
          if (arr1[i][j] !== arr2[i][j]) {
            return false;
          }
        }
      }

      return true;
    }
  }

  // knowNewFact(calledFact: FactNode): ExecInfo {
  //   const knownFacts: string[][][] | undefined = this.getTemplateFactFacts(
  //     calledFact.optName
  //   );
  //   if (!knownFacts)
  //     return resultInfo(
  //       ResultType.Unknown,
  //       calledFact.optName + "is not declared."
  //     );
  //   else {
  //   }
  // }

  // private getTemplateFactFacts(
  //   nameWithColons: string
  // ): string[][][] | undefined {
  //   const names = nameWithColons.split(OptsConnectionSymbol);
  //   if (names.length === 1) {
  //     return this.facts.get(names[0])?.facts;
  //   } else {
  //     let factMap = this.facts.get(names[0]);
  //     if (!factMap) return undefined;
  //     for (let i = 1; i < names.length; i++) {
  //       factMap = factMap.subTemplates.get(names[i]);
  //       if (!factMap) return undefined;
  //     }
  //     return factMap.facts;
  //   }
  // }

  // newTemplateDecl(env: LiTeXEnv, node: TemplateNode): ExecInfo {}

  callOptType(node: CallOptNode) {
    return this.optType(node.optName);
  }

  getDeclaredTemplate(node: string | CallOptNode): TemplateNode | undefined {
    const isTop = (s: string): Boolean => {
      return !s.includes(OptsConnectionSymbol);
    };

    const getBeforeFirstColon = (str: string): string => {
      const colonIndex = str.indexOf(":");
      return colonIndex !== -1 ? str.slice(0, colonIndex) : str;
    };

    let s = "";
    if (node instanceof CallOptNode) s = node.optName;
    else s = node;

    let relatedTemplate: TemplateNode | undefined;
    if (isTop(s)) {
      relatedTemplate = this.declaredTemplates.get(s);
    } else {
      relatedTemplate = this.declaredTemplates
        .get(getBeforeFirstColon(s))
        ?.getDeclaredSubTemplate(s);
    }

    return relatedTemplate;
  }

  optType(s: string): LiTexNodeType {
    const node = this.getDeclaredTemplate(s);
    return (node as TemplateNode).type;
    // let node: LiTeXNode = this.infers.get(s) as LiTeXNode;
    // if (node) return LiTexNodeType.InferNode;
    // node = this.defs.get(s) as LiTeXNode;
    // if (node) return LiTexNodeType.DefNode;
    // return LiTexNodeType.Error;
  }

  // returnToSnapShot(original: SnapShot) {
  //   this.fatherFreeVars = original.fatherFreeVars;
  // }

  // getSnapShot(): SnapShot {
  //   return { fatherFreeVars: [...this.fatherFreeVars] };
  // }

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
        this.callOptFactsOnlyIfs.set(this.callOptNodeName(node), []);
      } else {
        this.callOptFacts.get(this.callOptNodeName(node))?.push(node.optParams);
        this.callOptFactsOnlyIfs
          .get(this.callOptNodeName(node))
          ?.push({ params: node.optParams, onlyIfs: [] });
      }
    }
  }

  isCallOptFact(optNode: CallOptNode): Boolean {
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

  getCallOptFactIndex(optNode: CallOptNode): number {
    const validParamsLst = this.getFromCallOptFacts(optNode);
    if (!validParamsLst) return -1;

    for (const item of validParamsLst) {
      for (let i = 0; i < item.length; i++) {
        if (paramsIsValid(item[i], optNode.optParams[i])) {
          return i;
        }
      }
    }

    return -1;
  }

  newCallOptFactsOnlyIf(optNode: CallOptNode): Boolean {
    return true;
  }

  getCalledFactOnlyIfs(optNode: CallOptNode): CallOptNode[] | undefined {
    const validParamsLst = this.callOptFactsOnlyIfs.get(optNode.optName);
    if (!validParamsLst) return undefined;

    for (const item of validParamsLst) {
      let isTheSame = true;
      for (let i = 0; i < item.params.length; i++) {
        if (!paramsIsValid(item.params[i], optNode.optParams[i])) {
          isTheSame = false;
          break;
        }
      }
      if (isTheSame) {
        return item.onlyIfs;
      }
    }
    return undefined;
  }

  printCallOptFacts() {
    console.log("----facts------\n");
    for (const [key, value] of this.callOptFacts) {
      console.log("[opt]  " + key);
      for (const item of value) {
        console.log(item);
      }
    }
    console.log("");
  }

  printDeclaredTemplates() {
    console.log("------template-----\n");

    for (const value of this.declaredTemplates) {
      console.log(value);
      console.log("");
    }
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

// export function twoFixedOptHasTheSameMeaning(optNode1 : CallOptNode, optNode2: CallOptNode): Boolean {
//   if (optNode1.optName !== optNode2.optName) {
//     return false
//   }

// }
