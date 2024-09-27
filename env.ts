import {
  CallOptNode,
  LiTexNodeType,
  LiTeXNode,
  CallOptsNode,
  TemplateNode,
  FactNode,
} from "./ast";
import { OptsConnectionSymbol } from "./common";
import { ExecInfo, resultInfo, ResultType } from "./executor";

export class LiTeXEnv {
  errors: string[] = [];
  callOptFacts: Map<string, string[][][]> = new Map<string, string[][][]>();
  declaredVars: string[] = [];
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
  }

  constructor() {}

  pushErrorMessage(s: string) {
    this.errors.push(s);
  }

  callOptNodeName(optNode: CallOptNode) {
    return optNode.optName;
  }

  getFromCallOptFacts(optNode: CallOptNode) {
    const optName: string = optNode.optName;
    const validParamsLst = this.callOptFacts.get(optName);
    return validParamsLst;
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
