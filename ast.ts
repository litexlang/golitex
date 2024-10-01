import { OptsConnectionSymbol } from "./common";
import { LiTeXEnv } from "./env";
import { checkParams, ExecInfo, execInfo, ResultType } from "./executor";

// There are 3 things in LiTex: Declaration (var, fact-template) ; check; know
export enum LiTexNodeType {
  Error,
  Node,

  // Fact
  CallOptNode,
  CallOptsNode,

  // Operators
  KnowNode,
  ExistNode,
  HaveNode,
  LetNode,
  ProofNode,

  // Template
  InferNode,
  DefNode,

  // Helper
  FreeVarsWithFactsNode,
  DollarMarkNode,
}

export abstract class LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.Node;
  constructor() {}
}

export class CallOptNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.CallOptNode;
  optName: string = "";
  optParams: string[][] = [];
  optNameAsLst: string[] = [];

  constructor(opts: [string, string[]][]) {
    super();

    this.optName = opts.map((e) => e[0]).join(OptsConnectionSymbol);
    this.optParams = opts.map((e) => e[1]);
    this.optNameAsLst = opts.map((e) => e[0]);
  }

  static create(name: string, params: string[][]) {
    const names = name.split(OptsConnectionSymbol);
    return new CallOptNode(names.map((e, i) => [e, params[i]]));
  }

  getOptNameParamsPairs(): [string, string[]][] {
    return this.optNameAsLst.map((v, i) => {
      return [this.optName, this.optParams[i]];
    });
  }

  pushNewNameParamsPair(pair: [string, string[]]) {
    if (this.optName !== "") this.optName += OptsConnectionSymbol + pair[0];
    else this.optName += pair[0];

    this.optParams.push(pair[1]);
  }
}

export type TemplateNodeFact = {
  params: string[][];
  onlyIfs: CallOptNode[];
  activated: Boolean;
};
export function makeTemplateNodeFact(
  params: string[][],
  onlyIfs: CallOptNode[],
  activated: Boolean = true
) {
  return { params: params, onlyIfs: onlyIfs, activated: activated };
}

// Main data structure of the whole project
export abstract class TemplateNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.InferNode;
  declOptName: string;
  requirements: LiTeXNode[] = [];
  onlyIfExprs: LiTeXNode[] = [];
  declaredTemplates = new Map<string, TemplateNode>();
  facts: TemplateNodeFact[] = [];
  freeVars: string[];

  constructor(
    declOptName: string,
    freeVars: string[],
    requirements: LiTeXNode[]
  ) {
    super();
    this.declOptName = declOptName;
    this.freeVars = freeVars;
    this.requirements = requirements;
  }

  // Input a full name with colons and get descendants from any depth
  getDeclaredSubTemplate(s: string): undefined | TemplateNode {
    const names: string[] = s.split(":");
    let curTemplate: TemplateNode | undefined = this;
    for (let i = 1; i < names.length; i++) {
      curTemplate = curTemplate?.declaredTemplates.get(names[i]);
      if (!curTemplate) {
        return undefined;
      }
    }
    return curTemplate;
  }

  // If a node is DollarMarkNode or TemplateNode, i.e. it is the son template of this, then it is pushed into this.declaredTemplates and it is removed from this.onlyIfExprs. If there is non-def, non-call node in block, report error
  initDeclaredTemplates(): ExecInfo {
    for (let i = this.onlyIfExprs.length - 1; i >= 0; i--) {
      const value = this.onlyIfExprs[i];

      if (value instanceof DollarMarkNode) {
        this.onlyIfExprs.splice(i, 1);

        const callNode = new CallOptNode([
          [value.template.declOptName, value.template.freeVars],
        ]);
        const templateNode: TemplateNode = value.template;

        //! Here lies a problem: the templateNode's optName should start with : and anything start with : means it inherits from all above.
        this.onlyIfExprs.splice(i, 0, templateNode, callNode);
      }
    }

    for (let i = this.onlyIfExprs.length - 1; i >= 0; i--) {
      const value = this.onlyIfExprs[i];
      if (value instanceof TemplateNode) {
        value.initDeclaredTemplates();
        this.declaredTemplates.set(value.declOptName, value);
        this.onlyIfExprs.splice(i, 1);
      } else if (value instanceof CallOptsNode) {
        this.onlyIfExprs = insertListIntoListAndDeleteElemOnIndex(
          this.onlyIfExprs,
          (value as CallOptsNode).nodes,
          i
        );
      }
    }

    for (let i = 0; i < this.onlyIfExprs.length; i++) {
      if (this.onlyIfExprs[i].type !== LiTexNodeType.CallOptNode) {
        return execInfo(
          ResultType.DefError,
          `arguments of def block should have type callOpt-type or def-type.`
        );
      }
    }
    return execInfo(ResultType.DefTrue);

    function insertListIntoListAndDeleteElemOnIndex<T>(
      originalList: T[],
      itemsToInsert: T[],
      position: number
    ): T[] {
      const newList = [...originalList];
      newList.splice(position, 1, ...itemsToInsert);
      return newList;
    }
  }

  abstract knowCallOptExecCheck(node: FactNode): ExecInfo;
}

export class DefNode extends TemplateNode {
  type: LiTexNodeType = LiTexNodeType.DefNode;

  // When a fact is to be stored, whether it satisfies requirements must be checked
  knowCallOptExecCheck(node: CallOptNode): ExecInfo {
    let template: undefined | TemplateNode = this as TemplateNode;
    for (let i = 0; ; i++) {
      if (template.freeVars.length !== node.optParams[i].length) {
        return execInfo(
          ResultType.KnowError,
          template.declOptName +
            " has " +
            template.freeVars.length +
            " parameters, get " +
            node.optNameAsLst[i].length +
            " instead."
        );
      }

      if (i + 1 < node.optNameAsLst.length) {
        template = template.declaredTemplates.get(node.optNameAsLst[i + 1]);
        if (!template)
          return execInfo(
            ResultType.KnowError,
            "Undefined operator " + node.optName
          );
      } else {
        break;
      }
    }
    return execInfo(ResultType.KnowTrue);
  }
}

export class InferNode extends TemplateNode {
  type: LiTexNodeType = LiTexNodeType.InferNode;

  knowCallOptExecCheck(node: CallOptNode): ExecInfo {
    let template: undefined | TemplateNode = this as TemplateNode;
    for (let i = 0; ; i++) {
      if (template.freeVars.length !== node.optParams[i].length) {
        return execInfo(
          ResultType.KnowError,
          `${template.declOptName} has ${template.freeVars.length} parameters, get ${node.optNameAsLst[i].length} instead.`
        );
      }

      if (i + 1 < node.optNameAsLst.length) {
        template = template.declaredTemplates.get(node.optNameAsLst[i + 1]);
        if (!template)
          return execInfo(
            ResultType.KnowError,
            "Undefined operator " + node.optName
          );
      } else {
        break;
      }
    }
    return execInfo(ResultType.KnowTrue);
  }
}

export class ExistNode extends TemplateNode {
  type = LiTexNodeType.ExistNode;

  knowCallOptExecCheck(node: CallOptNode): ExecInfo {
    return execInfo(ResultType.KnowTrue);
  }
}

export type CanBeKnownNode = FactNode | TemplateNode;
export class KnowNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.KnowNode;
  facts: CanBeKnownNode[] = [];
  isKnowEverything: Boolean = false;
}

export class FreeVarsWithFactsNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.FreeVarsWithFactsNode;
  params: string[];
  properties: CallOptNode[];

  constructor(params: string[], properties: CallOptNode[]) {
    super();
    this.params = params;
    this.properties = properties;
  }
}

export type FactNode = CallOptNode | CallOptsNode;
export enum CallOptsNodeType {
  And,
  Or,
  False,
}
export class CallOptsNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.CallOptsNode;
  nodes: CallOptNode[] = [];
  factType: CallOptsNodeType = CallOptsNodeType.And;

  constructor(nodes: CallOptNode[]) {
    super();
    this.nodes = nodes;
  }
}

export class LetNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.LetNode;
  params: string[];
  properties: CallOptNode[];

  constructor(node: FreeVarsWithFactsNode) {
    super();
    this.params = node.params;
    this.properties = node.properties;
  }
}

export class DollarMarkNode extends LiTeXNode {
  type = LiTexNodeType.DollarMarkNode;
  template: TemplateNode;

  constructor(template: TemplateNode) {
    super();
    this.template = template;
  }
}
