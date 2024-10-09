// import { on } from "events";
import { LiTeXKeywords, OptsConnectionSymbol } from "./common";
import { LiTeXEnv } from "./env";
import {
  // _paramsInOptAreDeclared,
  // _VarsAreNotDeclared,
  ExecInfo,
  execInfo,
  handleRuntimeError,
  ResultType,
} from "./executor";

// There are several things in LiTex: Declaration (var, fact-template) ; check; know(let); emit
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
  CheckInProof,

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
  requirements: CallOptNode[][] = [];

  constructor(opts: [string, string[]][], requirements: CallOptNode[][] = []) {
    super();

    this.optName = opts.map((e) => e[0]).join(OptsConnectionSymbol);
    this.optParams = opts.map((e) => e[1]);
    this.optNameAsLst = opts.map((e) => e[0]);
    this.requirements = requirements;
  }

  static create(name: string, params: string[][]) {
    const names = name.split(OptsConnectionSymbol);
    return new CallOptNode(names.map((e, i) => [e, params[i]]));
  }
}

export type TemplateNodeFact = {
  params: string[][];
  onlyIfs: CallOptNode[];
  requirements: CallOptNode[];
  activated: Boolean;
};
export function makeTemplateNodeFact(
  params: string[][],
  onlyIfs: CallOptNode[] = [],
  requirements: CallOptNode[] = [],
  activated: Boolean = true
) {
  return {
    params: params,
    onlyIfs: onlyIfs,
    activated: activated,
    requirements: requirements,
  };
}

// Main data structure of the whole project
export abstract class TemplateNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.InferNode;
  declOptName: string;
  freeVars: string[];
  requirements: LiTeXNode[] = [];
  onlyIfExprs: LiTeXNode[] = []; // After declaration, this becomes CallOpt[]
  declaredTemplates = new Map<string, TemplateNode>();
  // facts: TemplateNodeFact[] = [];
  private fathers: TemplateNode[] = [];
  // Fix all free variables in this template, no matter it's declared in fathers or itself
  // private freeFixMap: Map<string, string> = new Map<string, string>();
  // private fixedFullParams: string[][] = [];
  isRedefine: Boolean = false;

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

  // newFact(env: LiTeXEnv, fact: TemplateNodeFact): ExecInfo {
  //   if (!_paramsInOptAreDeclared(env, fact.params))
  //     return _VarsAreNotDeclared(fact);
  //   else {
  //     env.newStoredFact(fact.params, this);
  //     // this.facts.push(fact);
  //   }
  //   return execInfo(ResultType.True);
  // }

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
  //! REFACTOR THIS SO THAT DEF IN REQ CAN APPEAR HERE.
  initDeclaredTemplates(env: LiTeXEnv, fathers: TemplateNode[] = []): ExecInfo {
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

    this.fathers = fathers;

    for (let i = this.onlyIfExprs.length - 1; i >= 0; i--) {
      const value = this.onlyIfExprs[i];
      if (value instanceof TemplateNode) {
        if (LiTeXKeywords.includes(value.declOptName))
          return handleRuntimeError(
            env,
            ResultType.DefError,
            `Template '${value.declOptName}' is LiTeX keyword.`
          );
        value.initDeclaredTemplates(env, [...fathers, this]);
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

  // Fix all free variables in this template, no matter it's declared in fathers or itself
  // callOptParams: the fullOpt that calls this template
  fix(
    callOptParams: CallOptNode | string[][]
  ): Map<string, string> | undefined {
    if (callOptParams instanceof CallOptNode) {
      callOptParams = callOptParams.optParams;
    }
    callOptParams = callOptParams as string[][];

    const freeFixMap = new Map<string, string>();

    const relatedTemplates = [...this.fathers, this];

    if (
      !areArraysEqual(
        callOptParams,
        relatedTemplates.map((e) => e.freeVars)
      )
    ) {
      return undefined;
    }

    for (let [i, template] of relatedTemplates.entries()) {
      template.freeVars.forEach((v, j: number) =>
        freeFixMap.set(v, callOptParams[i][j])
      );
    }

    return freeFixMap;

    function areArraysEqual(arr1: string[][], arr2: string[][]): boolean {
      if (arr1.length !== arr2.length) {
        return false;
      }

      for (let i = 0; i < arr1.length; i++) {
        if (arr1[i].length !== arr2[i].length) {
          return false;
        }
      }

      return true;
    }
  }

  emit(
    env: LiTeXEnv,
    freeFixMap: Map<string, string>,
    fathers: string[][] = []
  ): ExecInfo {
    try {
      const keys = fathers.map((arr) => [...arr]);
      keys.push([...this.freeVars].map((e) => freeFixMap.get(e) || e));

      env.newStoredFact(keys, this);

      return execInfo(ResultType.True);
    } catch (error) {
      return execInfo(
        ResultType.Error,
        "error when emitting new fact into environment."
      );
    }
  }

  emitOnlyIfs(
    env: LiTeXEnv,
    freeFixMap: Map<string, string>,
    fathers: string[][] = []
  ) {
    for (let onlyIf of this.onlyIfExprs) {
      (env.getDeclaredTemplate(onlyIf as CallOptNode) as TemplateNode).emit(
        env,
        freeFixMap,
        fathers
      );
    }
  }

  emitRequirements(
    env: LiTeXEnv,
    freeFixMap: Map<string, string>,
    fathers: string[][] = []
  ) {
    for (let requirement of this.requirements) {
      const relatedTemplate = env.getDeclaredTemplate(
        requirement as CallOptNode
      ) as TemplateNode;
      if (!relatedTemplate) return false;
      relatedTemplate.emit(env, freeFixMap, fathers);
    }
    return true;
  }

  requirementsSatisfied(env: LiTeXEnv, mapping: Map<string, string>): Boolean {
    let allRequirementsAreSatisfied: Boolean = true;
    for (let requirement of this.requirements) {
      if (requirement instanceof CallOptNode) {
        const keys: string[][] = [
          ...(requirement as CallOptNode).optParams,
        ].map((sArr) => sArr.map((s) => mapping.get(s) || ""));
        let calledT = env.getDeclaredTemplate(requirement as CallOptNode);
        if (!calledT) return false;
        let res = env.isStoredTrueFact(keys, calledT);
        if (!res) {
          allRequirementsAreSatisfied = false;
          break;
        }
      }
    }
    return allRequirementsAreSatisfied;
  }
}

export class DefNode extends TemplateNode {
  type: LiTexNodeType = LiTexNodeType.DefNode;
}

export class InferNode extends TemplateNode {
  type: LiTexNodeType = LiTexNodeType.InferNode;
}

export class ExistNode extends TemplateNode {
  type = LiTexNodeType.ExistNode;
  isTrue = false;
}

export type CanBeKnownNode = FactNode | TemplateNode;
export class KnowNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.KnowNode;
  facts: CanBeKnownNode[] = [];
  isKnowEverything: Boolean = false;
}

export type FactNode = CallOptNode | CallOptsNode;
export enum CallOptsNodeType {
  And,
  Or,
  Not,
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
  vars: string[];
  properties: CallOptNode[];

  constructor(node: { freeVars: string[]; properties: CallOptNode[] }) {
    super();
    this.vars = node.freeVars;
    this.properties = node.properties;
  }
}

// Declare and call at the same time.
export class DollarMarkNode extends LiTeXNode {
  type = LiTexNodeType.DollarMarkNode;
  template: TemplateNode;

  constructor(template: TemplateNode) {
    super();
    this.template = template;
  }
}

export class ProveNode extends LiTeXNode {
  type = LiTexNodeType.ProofNode;
  templateName: string;
  freeVars: string[];
  requirements: LiTeXNode[];
  onlyIfExprs: LiTeXNode[];

  constructor(
    templateName: string,
    freeVars: string[],
    requirements: LiTeXNode[],
    onlyIfExprs: LiTeXNode[]
  ) {
    super();
    this.templateName = templateName;
    this.freeVars = freeVars;
    this.requirements = requirements;
    this.onlyIfExprs = onlyIfExprs;
  }
}

export class YAProveNode extends LiTeXNode {
  type = LiTexNodeType.ProofNode;
  templateNames: string[];
  freeVars: string[][];
  requirements: CallOptNode[][];
  onlyIfExprs: LiTeXNode[];

  constructor(
    templateNames: string[],
    freeVars: string[][],
    requirements: CallOptNode[][],
    onlyIfExprs: LiTeXNode[]
  ) {
    super();
    this.templateNames = templateNames;
    this.freeVars = freeVars;
    this.requirements = requirements;
    this.onlyIfExprs = onlyIfExprs;
  }
}

export class HaveNode extends LiTeXNode {
  type = LiTexNodeType.HaveNode;
  params: string[];
  opt: CallOptNode;
  constructor(params: string[], opt: CallOptNode) {
    super();
    this.params = params;
    this.opt = opt;
  }
}
