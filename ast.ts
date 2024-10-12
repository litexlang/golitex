import { L_Keywords, OptsConnectionSymbol } from "./common";
import { L_Env } from "./env";
import { hInfo, RInfo, hRunErr, RType } from "./executor";

//? There are several things in LiTex: Declaration (var, fact-template) ; check; know(let); emit
export enum L_NodeType {
  Error,
  Node,

  CallOptNode,
  CallOptsNode,

  KnowNode,
  HaveNode,
  LetNode,
  ProofNode,
  CheckInProof,
  ImpliesFactNode,

  InferNode,
  DefNode,
  ExistNode,

  FreeVarsWithFactsNode,
  DollarMarkNode,
}

export abstract class L_Node {
  type: L_NodeType = L_NodeType.Node;
}

export class CallOptNode extends L_Node {
  type: L_NodeType = L_NodeType.CallOptNode;
  optName: string;
  optParams: string[][];
  optNameAsLst: string[];

  /**Extra features: used in know, prove*/
  req: CallOptNode[] = [];
  onlyIFs: CallOptNode[] = [];

  constructor(
    opts: [string, string[]][],
    req: CallOptNode[][] = [],
    onlyIfs: CallOptNode[] = []
  ) {
    super();

    this.optName = opts.map((e) => e[0]).join(OptsConnectionSymbol);
    this.optParams = opts.map((e) => e[1]);
    this.optNameAsLst = opts.map((e) => e[0]);
    this.req = req.flat();
    this.onlyIFs = onlyIfs;
  }

  static create(
    name: string,
    params: string[][],
    req: CallOptNode[][] = [],
    onlyIfs: CallOptNode[] = []
  ) {
    const names = name.split(OptsConnectionSymbol);
    return new CallOptNode(
      names.map((e, i) => [e, params[i]]),
      req,
      onlyIfs
    );
  }

  toString() {
    let s = this.optNameAsLst
      .map((v, i) => `${v}(${this.optParams[i].join(", ")})`)
      .join(":");
    return s;
  }
}

export type TNodeFact = {
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
export abstract class TNode extends L_Node {
  type: L_NodeType = L_NodeType.InferNode;
  name: string;
  freeVars: string[];
  requirements: CallOptNode[] = [];
  onlyIfExprs: L_Node[] = []; // After declaration, this becomes CallOpt[]
  declaredTemplates = new Map<string, TNode>();
  private fathers: TNode[] = [];
  isRedefine: Boolean = false;

  constructor(name: string, freeVars: string[], requirements: CallOptNode[]) {
    super();
    this.name = name;
    this.freeVars = freeVars;
    this.requirements = requirements;
  }
  // Input a full name with colons and get descendants from any depth
  getDeclaredSubTemplate(s: string): undefined | TNode {
    const names: string[] = s.split(":");
    let curTemplate: TNode | undefined = this;
    for (let i = 1; i < names.length; i++) {
      curTemplate = curTemplate?.declaredTemplates.get(names[i]);
      if (!curTemplate) {
        return undefined;
      }
    }
    return curTemplate;
  }

  getSelfFathersReq(): CallOptNode[] {
    const out: CallOptNode[] = [];
    this.fathers.forEach((e) => e.requirements.forEach((req) => out.push(req)));
    this.requirements.forEach((e) => out.push(e));
    return out;
  }

  getSelfFathersFreeVars() {
    const out: string[][] = [];
    for (const father of this.fathers) {
      out.push(father.freeVars);
    }
    out.push(this.freeVars);
    return out;
  }

  // If a node is DollarMarkNode or TNode, i.e. it is the son template of this, then it is pushed into this.declaredTemplates and it is removed from this.onlyIfExprs. If there is non-def, non-call node in block, report error
  //! REFACTOR THIS SO THAT DEF IN REQ CAN APPEAR HERE.
  initDeclaredTemplates(env: L_Env, fathers: TNode[] = []): RInfo {
    this.fathers = fathers;

    // process DollarMarks
    for (let i = this.onlyIfExprs.length - 1; i >= 0; i--) {
      const value = this.onlyIfExprs[i];

      if (value instanceof DollarMarkNode) {
        this.onlyIfExprs.splice(i, 1);

        const callNode = new CallOptNode([
          [value.template.name, value.template.freeVars],
        ]);
        const templateNode: TNode = value.template;

        //! Here lies a problem: the templateNode's optName should start with : and anything start with : means it inherits from all above.
        this.onlyIfExprs.splice(i, 0, templateNode, callNode);
      }
    }

    // eliminate template declarations in onlyIfs, retain callOpts
    for (let i = this.onlyIfExprs.length - 1; i >= 0; i--) {
      const value = this.onlyIfExprs[i];
      if (value instanceof TNode) {
        if (L_Keywords.includes(value.name))
          return hRunErr(
            env,
            RType.DefError,
            `Template '${value.name}' is L_ keyword.`
          );
        value.initDeclaredTemplates(env, [...fathers, this]);
        this.declaredTemplates.set(value.name, value);
        this.onlyIfExprs.splice(i, 1);
      } else if (value instanceof CallOptsNode) {
        this.onlyIfExprs = insertListIntoListAndDeleteElemOnIndex(
          this.onlyIfExprs,
          (value as CallOptsNode).nodes,
          i
        );
      }
    }

    // make sure everything is done well.
    for (let i = 0; i < this.onlyIfExprs.length; i++) {
      if (this.onlyIfExprs[i].type !== L_NodeType.CallOptNode) {
        return hInfo(
          RType.DefError,
          `arguments of def block should have type callOpt-type or def-type.`
        );
      }
    }
    return hInfo(RType.DefTrue);

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

    const relTs = [...this.fathers, this];

    if (
      !areArraysEqual(
        callOptParams,
        relTs.map((e) => e.freeVars)
      )
    ) {
      return undefined;
    }

    for (let [i, template] of relTs.entries()) {
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

  // emit(
  //   env: L_Env,
  //   freeFixMap: Map<string, string>,
  //   fathers: string[][] = []
  // ): RInfo {
  //   try {
  //     const keys = fathers.map((arr) => [...arr]);
  //     keys.push([...this.freeVars].map((e) => freeFixMap.get(e) || e));

  //     env.newStoredFact(keys, this);

  //     return hInfo(RType.True);
  //   } catch (error) {
  //     return hInfo(
  //       RType.Error,
  //       "error when emitting new fact into environment."
  //     );
  //   }
  // }

  // emitOnlyIfs(
  //   env: L_Env,
  //   freeFixMap: Map<string, string>,
  //   fathers: string[][] = []
  // ) {
  //   for (let onlyIf of this.onlyIfExprs) {
  //     (env.getRelT(onlyIf as CallOptNode) as TNode).emit(
  //       env,
  //       freeFixMap,
  //       fathers
  //     );
  //   }
  // }

  // emitRequirements(
  //   env: L_Env,
  //   freeFixMap: Map<string, string>,
  //   fathers: string[][] = []
  // ) {
  //   for (let requirement of this.requirements) {
  //     const relT = env.getRelT(requirement as CallOptNode) as TNode;
  //     if (!relT) return false;
  //     relT.emit(env, freeFixMap, fathers);
  //   }
  //   return true;
  // }

  // requirementsSatisfied(env: L_Env, mapping: Map<string, string>): Boolean {
  //   let allRequirementsAreSatisfied: Boolean = true;
  //   for (let requirement of this.requirements) {
  //     if (requirement instanceof CallOptNode) {
  //       const keys: string[][] = [
  //         ...(requirement as CallOptNode).optParams,
  //       ].map((sArr) => sArr.map((s) => mapping.get(s) || ""));
  //       let calledT = env.getRelT(requirement as CallOptNode);
  //       if (!calledT) return false;
  //       let res = env.isStoredTrueFact(keys, calledT);
  //       if (!res) {
  //         allRequirementsAreSatisfied = false;
  //         break;
  //       }
  //     }
  //   }
  //   return allRequirementsAreSatisfied;
  // }
}

export class DefNode extends TNode {
  type: L_NodeType = L_NodeType.DefNode;
}

export class InferNode extends TNode {
  type: L_NodeType = L_NodeType.InferNode;
}

export class ExistNode extends TNode {
  type = L_NodeType.ExistNode;
  isTrue = false;
}

export type CanBeKnownNode = FactNode | TNode;
export class KnowNode extends L_Node {
  type: L_NodeType = L_NodeType.KnowNode;
  facts: CanBeKnownNode[] = [];
  isKnowEverything: Boolean = false;
}

export type FactNode = CallOptNode | CallOptsNode;
export enum CallOptsNodeType {
  And,
  Or,
  Not,
}
export class CallOptsNode extends L_Node {
  type: L_NodeType = L_NodeType.CallOptsNode;
  nodes: CallOptNode[] = [];
  factType: CallOptsNodeType = CallOptsNodeType.And;

  constructor(nodes: CallOptNode[]) {
    super();
    this.nodes = nodes;
  }
}

export class LetNode extends L_Node {
  type: L_NodeType = L_NodeType.LetNode;
  vars: string[];
  properties: CallOptNode[];

  constructor(node: { freeVars: string[]; properties: CallOptNode[] }) {
    super();
    this.vars = node.freeVars;
    this.properties = node.properties;
  }
}

// Declare and call at the same time.
export class DollarMarkNode extends L_Node {
  type = L_NodeType.DollarMarkNode;
  template: TNode;

  constructor(template: TNode) {
    super();
    this.template = template;
  }
}

export class YAProveNode extends L_Node {
  type = L_NodeType.ProofNode;
  opt: CallOptNode;
  proveBlock: L_Node[];

  constructor(opt: CallOptNode, proveBlock: L_Node[]) {
    super();
    this.opt = opt;
    this.proveBlock = proveBlock;
  }
}

export class HaveNode extends L_Node {
  type = L_NodeType.HaveNode;
  opt: CallOptNode;
  constructor(opt: CallOptNode) {
    super();
    this.opt = opt;
  }
}

// export class ImpliesFactNode extends L_Node {
//   type: L_NodeType = L_NodeType.ImpliesFactNode;
//   callOpt: CallOptNode;
//   requirements: CallOptNode[][] = [];
//   onlyIfExprs: CallOptNode[] = [];

//   constructor(
//     callOpt: CallOptNode,
//     onlyIfExprs: CallOptNode[],
//     requirements: CallOptNode[][] = []
//   ) {
//     super();
//     this.callOpt = callOpt;
//     this.requirements = requirements;
//     this.onlyIfExprs = onlyIfExprs;
//   }
// }
