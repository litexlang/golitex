import {
  // CallOptNode,
  // ExistNode,
  KnowNode,
  L_Node,
  LetNode,
  // ProveNode,
  // HaveNode,
  // ByNode,
  // ThmNode,
  OrNode,
  ShortCallOptNode,
  IfThenNode,
  DeclNode,
  DefDeclNode,
  IfThenDeclNode,
  FactNode,
  ByNode,
} from "./ast";
import { L_Env } from "./env";
import {
  KnowTypeKeywords,
  specialChars,
  SymbolsFactsSeparator,
  ProveKeywords,
  suchThats,
  byLBracket,
  byRBracket,
  StdStmtEnds,
  yaIfThenKeywords,
  IfThenKeywords,
  DefKeywords,
  LetKeywords,
  ThenKeywords,
} from "./common";
import { only } from "node:test";
import { add } from "lodash";

function skip(tokens: string[], s: string | string[] = "") {
  if (typeof s === "string") {
    if (s === "") {
      return tokens.shift();
    } else if (s === tokens[0]) {
      return tokens.shift();
    } else {
      throw Error("unexpected symbol: " + tokens[0]);
    }
  } else {
    for (const value of s) {
      if (value === tokens[0]) {
        return tokens.shift();
      }
    }
    throw Error("unexpected symbol: " + tokens[0]);
  }
}

//! Not only gets symbol, in the future it will parse $$
function shiftVar(tokens: string[]): string {
  const token = tokens.shift();
  if (typeof token !== "string") {
    throw new Error("No more tokens");
  }
  return token;
}

function isCurToken(tokens: string[], s: string) {
  return s === tokens[0];
}

function handleParseError(
  // tokens: string[],
  env: L_Env,
  m: string,
  index: number,
  start: string = ""
) {
  env.newMessage(`At ${start}[${index * -1}]: ${m}`);
}

export function L_StmtsParse(env: L_Env, tokens: string[]): L_Node[] | null {
  try {
    const result: L_Node[] = [];
    while (tokens.length > 0) {
      LiTexStmtParse(env, tokens, result);
    }
    return result;
  } catch (error) {
    return null;
  }
}

const KeywordFunctionMap: {
  [key: string]: Function; // (env: L_Env, tokens: string[]) => any;
} = {
  ";": (env: L_Env, tokens: string[]) => {
    tokens.shift();
  },
  "\n": (env: L_Env, tokens: string[]) => {
    tokens.shift();
  },
  know: knowParse,
  "@": knowParse,
  // have: haveParse,
  let: letParse,
  def: DeclNodeParse,
  ":": DeclNodeParse,
  // exist: existParse,
  // prove: proveParse,
  // by: byParse,
  // thm: thmParse,
};

export function LiTexStmtParse(
  env: L_Env,
  tokens: string[],
  putInto: L_Node[]
) {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const func = KeywordFunctionMap[tokens[0]];
    const funcName = tokens[0];
    if (func) {
      const node = func(env, tokens);
      if (KnowTypeKeywords.includes(funcName)) {
        skip(tokens, StdStmtEnds);
      }
      if (node) {
        putInto.push(node);
      } else {
        return;
      }
    } else {
      callOptsParse(env, tokens, putInto);
      return;
    }
  } catch (error) {
    handleParseError(env, "Stmt", index, start);
    throw error;
  }
}

function knowParse(env: L_Env, tokens: string[]): KnowNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const knowNode: KnowNode = new KnowNode();

    skip(tokens, KnowTypeKeywords);
    while (1) {
      const relParser: Function | undefined = factParserSignals[tokens[0]];
      let out: FactNode;
      if (relParser === undefined) {
        out = shortCallOptParse(env, tokens, false);
      } else {
        out = relParser(env, tokens, true);
      }
      knowNode.facts.push(out);

      if (tokens[0] === ",") skip(tokens, ",");
      else break;
    }

    return knowNode;
  } catch (error) {
    handleParseError(env, "know", index, start);
    throw error;
  }
}

// skips begin and end
// function freeVarsAndTheirFactsParse(
//   env: L_Env,
//   tokens: string[],
//   begin: string = "(",
//   end: string[] = [")"],
//   optWithReqAndOnlyIf: Boolean = false
// ): { freeVars: string[]; properties: CallOptNode[] } {
//   const requirements: CallOptNode[] = [];
//   const freeVars: string[] = [];

//   skip(tokens, begin);

//   if (!end.includes(tokens[0])) {
//     while (1) {
//       const freeVar = tokens.shift() as string;
//       freeVars.push(freeVar);
//       if (tokens[0] === ",") tokens.shift();
//       else if (tokens[0] === SymbolsFactsSeparator) break;
//       else if (end.includes(tokens[0])) break;
//       else throw Error("infer parameters");
//     }
//     if (!end.includes(tokens[0])) {
//       skip(tokens, SymbolsFactsSeparator);
//       while (!end.includes(tokens[0])) {
//         let node: CallOptNode;
//         if (optWithReqAndOnlyIf) node = callOptParse(env, tokens, true, true);
//         else node = callOptParse(env, tokens);
//         if (node) requirements.push(node as CallOptNode);

//         if (tokens[0] === ",") tokens.shift();
//         if (end.includes(tokens[0])) break;
//       }
//     }
//   }

//   skip(tokens, end);

//   return { freeVars: freeVars, properties: requirements };
// }

function blockParse(env: L_Env, tokens: string[]): L_Node[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const result: L_Node[] = [];
    skip(tokens, "{"); // skip {

    while (!isCurToken(tokens, "}")) {
      LiTexStmtParse(env, tokens, result);
    }

    skip(tokens, "}"); // skip }

    return result;
  } catch (error) {
    handleParseError(env, "{}", index, start);
    throw error;
  }
}

// function callOptParse(
//   env: L_Env,
//   tokens: string[],
//   // the followings all false means vanilla callOpt
//   withReq: Boolean = false,
//   withOnlyIf: Boolean = false,
//   withByName: Boolean = false
// ): CallOptNode {
//   const index = tokens.length;
//   const start = tokens[0];

//   try {
//     const opts: [string, string[]][] = [];
//     const requirements: CallOptNode[][] = [];

//     /**
//      * There are 2 ways to parse here
//      * 1. fun(X):fun2(Y)..
//      * 2. X:Y.. is fun:fun2
//      */
//     if (tokens.length >= 1 && tokens[1] === "(") {
//       while (1) {
//         const name = shiftVar(tokens) as string;

//         if (!withReq) {
//           const params: string[] = [];

//           skip(tokens, "(");
//           if (!isCurToken(tokens, ")")) {
//             while (1) {
//               params.push(shiftVar(tokens));
//               if (isCurToken(tokens, ",")) skip(tokens, ",");
//               else if (isCurToken(tokens, ")")) {
//                 skip(tokens, ")");
//                 break;
//               } else throw Error("");
//             }
//           } else {
//             skip(tokens, ")");
//           }

//           opts.push([name, params]);
//         } else {
//           const freeVarsAndFacts = freeVarsAndTheirFactsParse(env, tokens);
//           opts.push([name, freeVarsAndFacts.freeVars]);
//           requirements.push(freeVarsAndFacts.properties);
//         }

//         if (isCurToken(tokens, ":")) {
//           skip(tokens, ":");
//         } else {
//           break;
//         }
//       }
//     } else {
//       // suchThat version of callOpt only works when !withReq
//       let n = 0;
//       const vars: string[][] = [[]];
//       const optNames: string[] = [];

//       if (!withReq) {
//         while (!suchThats.includes(tokens[0])) {
//           vars[n].push(shiftVar(tokens));
//           if (isCurToken(tokens, ",")) skip(tokens, ",");
//           else if (isCurToken(tokens, ":")) {
//             skip(tokens, ":");
//             vars.push([]);
//             n++;
//           }
//         }
//       }
//       skip(tokens, suchThats);

//       optNames.push(shiftVar(tokens));
//       for (let i = 1; i < n + 1; i++) {
//         skip(tokens, ":");
//         optNames.push(shiftVar(tokens));
//       }

//       vars.forEach((v, i) => opts.push([optNames[i], v]));
//     }

//     let out: CallOptNode;
//     if (!withOnlyIf || !isCurToken(tokens, "=>"))
//       out = new CallOptNode(opts, requirements);
//     else {
//       skip(tokens, "=>");
//       skip(tokens, "{");

//       const onlyIfs: CallOptNode[] = [];
//       callOptsParse(env, tokens, onlyIfs, ["}"]);

//       out = new CallOptNode(opts, requirements, onlyIfs);
//     }

//     if (!withByName) return out;
//     else {
//       if (!isCurToken(tokens, "[")) return out;
//       else {
//         skip(tokens, "[");

//         skip(tokens, "]");
//         return out;
//       }
//     }
//   } catch (error) {
//     handleParseError(env, "operator", index, start);
//     throw error;
//   }
// }

function callOptsParse(
  env: L_Env,
  tokens: string[],
  putInto: L_Node[] | undefined,
  end: string[] = StdStmtEnds
): FactNode[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const callOpts: FactNode[] = [];

    while (1) {
      callOpts.push(factParse(env, tokens));
      if (tokens[0] === ",") {
        skip(tokens, ",");
      } else if (end.includes(tokens[0])) {
        break;
      } else if (
        specialChars.includes(tokens[0]) &&
        !StdStmtEnds.includes(tokens[0])
      ) {
        throw Error(
          tokens[0] +
            "is not expected to appear here.',' is used to split between two facts."
        );
      }
    }

    skip(tokens, end);

    callOpts.forEach((e) => putInto?.push(e));

    return callOpts;
  } catch (error) {
    handleParseError(env, "operators", index, start);
    throw error;
  }
}

// function templateParse(env: L_Env, tokens: string[]): TNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     const defName = skip(tokens, TemplateDeclarationKeywords);
// const name = shiftVar(tokens);

//     const freeVarsFact: { freeVars: string[]; properties: CallOptNode[] } =
//       freeVarsAndTheirFactsParse(env, tokens);

//     // skip(tokens, ")");

//     let result: L_Node;
//     switch (tokens[0]) {
//       case "=>":
//         skip(tokens, "=>");
//         if (!isCurToken(tokens, "{")) {
//           result = new InferNode(
//             name,
//             freeVarsFact.freeVars,
//             freeVarsFact.properties
//           );
//           const facts: CallOptNode[] = [];
//           callOptsParse(env, tokens, facts);
//           for (let i = 0; i < facts.length; i++) {
//             (result as InferNode).onlyIfs.push(facts[i]);
//           }
//         } else {
//           const blockArrow = blockParse(env, tokens);
//           result = new InferNode(
//             name,
//             freeVarsFact.freeVars,
//             freeVarsFact.properties
//           );
//           (result as InferNode).onlyIfs = blockArrow;
//         }

//         break;

//       case "{":
//         const blockBrace = blockParse(env, tokens);
//         result = new InferNode(
//           name,
//           freeVarsFact.freeVars,
//           freeVarsFact.properties
//         );
//         (result as DefNode).onlyIfs = blockBrace;
//         break;

//       case "<=>":
//         skip(tokens, "<=>");
//         if (!isCurToken(tokens, "{")) {
//           result = new DefNode(
//             name,
//             freeVarsFact.freeVars,
//             freeVarsFact.properties
//           );
//           callOptsParse(env, tokens, (result as DefNode).onlyIfs);
//         } else {
//           const blockDoubleArrow = blockParse(env, tokens);
//           result = new DefNode(
//             name,
//             freeVarsFact.freeVars,
//             freeVarsFact.properties
//           );
//           (result as DefNode).onlyIfs = blockDoubleArrow;
//         }

//         break;

//       default:
//         // no arrow, no block
//         result = new DefNode(name, freeVarsFact.freeVars, []);
//         (result as TNode).requirements = freeVarsFact.properties;
//         break;
//     }

//     if (redefineTemplateDeclarationKeywords.includes(defName as string)) {
//       (result as TNode).isRedefine = true;
//     }
//     return result as TNode;
//   } catch (error) {
//     handleParseError(env, "declare template", index, start);
//     // env.returnToSnapShot(snapShot);
//     throw error;
//   }
// }

function letParse(env: L_Env, tokens: string[]): LetNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, LetKeywords);
    const vars = listParse<string>(
      env,
      tokens,
      (env, e) => shiftVar(e),
      [...StdStmtEnds, "|"],
      false
    );

    if (StdStmtEnds.includes(tokens[0])) {
      skip(tokens, StdStmtEnds);
      return new LetNode(vars, []);
    } else {
      skip(tokens, "|");
      const facts = listParse<FactNode>(
        env,
        tokens,
        factParse,
        StdStmtEnds,
        true
      );
      return new LetNode(vars, facts);
    }
  } catch (error) {
    handleParseError(env, "let", index, start);
    throw error;
  }
}

// function proveParse(env: L_Env, tokens: string[]): ProveNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     skip(tokens, ProveKeywords);
//     let name = "";
//     if (isCurToken(tokens, byLBracket)) {
//       skip(tokens, byLBracket);
//       name = shiftVar(tokens);
//       skip(tokens, byRBracket);
//     }
//     const relatedOpt = callOptParse(env, tokens, true, true);
//     const blockBrace = blockParse(env, tokens);
//     const result = new ProveNode(relatedOpt, blockBrace, name);
//     return result;
//   } catch (error) {
//     handleParseError(env, "prove", index, start);
//     throw error;
//   }
// }

// function existParse(env: L_Env, tokens: string[]): ExistNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     /** Copy code from templateParse */
//     skip(tokens, "exist") as string; // KnowTypeKeywords

//     const name = shiftVar(tokens);

//     const freeVarsFact: { freeVars: string[]; properties: CallOptNode[] } =
//       freeVarsAndTheirFactsParse(env, tokens);

//     let result: ExistNode;

//     result = new ExistNode(
//       name,
//       freeVarsFact.freeVars,
//       freeVarsFact.properties
//     );

//     return result;
//   } catch (error) {
//     handleParseError(env, "exist", index, start);
//     throw error;
//   }
// }

// function haveParse(env: L_Env, tokens: string[]): HaveNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     skip(tokens, "have");

//     const vars: string[] = [];
//     while (!isCurToken(tokens, SymbolsFactsSeparator)) {
//       vars.push(shiftVar(tokens));
//       if (isCurToken(tokens, ",")) skip(tokens, ",");
//     }
//     skip(tokens, SymbolsFactsSeparator);

//     const opt = callOptParse(env, tokens, false, false);

//     skip(tokens, StdStmtEnds);

//     return new HaveNode(vars, opt);
//   } catch (error) {
//     handleParseError(env, "have", index, start);
//     throw error;
//   }
// }

// function byParse(env: L_Env, tokens: string[]): ByNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     skip(tokens, "by");

//     const name = shiftVar(tokens);
//     const opt = callOptParse(env, tokens);

//     skip(tokens, StdStmtEnds);
//     return new ByNode(name, opt);
//   } catch (error) {
//     handleParseError(env, "by", index, start);
//     throw error;
//   }
// }

// function thmParse(env: L_Env, tokens: string[]): ThmNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     skip(tokens, "thm");

//     const opt = callOptParse(env, tokens, true, true);

//     // opt.optName should not have ':'
//     if (opt.optNameAsLst.length > 1 || opt.optParams.length > 1) {
//       handleParseError(
//         env,
//         `operator in thm should not have concatenated name ${opt.optName}`,
//         index,
//         start
//       );
//     }

//     const block = blockParse(env, tokens);

//     return new ThmNode(opt, block);
//   } catch (error) {
//     handleParseError(env, "thm", index, start);
//     throw error;
//   }
// }

// // all facts here are vanilla, which means they are of form opt(...)
// function reqOnlyIfFactParse(env: L_Env, tokens: string[]): CallOptNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     const req: CallOptNode[] = [];
//     skip(tokens, "(");
//     while (!isCurToken(tokens, ")")) {
//       req.push(callOptParse(env, tokens, false, false));
//       if (isCurToken(tokens, ",")) skip(tokens, ",");
//     }
//     skip(tokens, ")");

//     skip(tokens, "=>");
//     skip(tokens, "{");

//     const onlyIf: CallOptNode[] = [];
//     while (!isCurToken(tokens, "}")) {
//       onlyIf.push(callOptParse(env, tokens, false, false));
//       if (isCurToken(tokens, ",")) skip(tokens, ",");
//     }

//     skip(tokens, "}");

//     return new CallOptNode([], [req], onlyIf);
//   } catch (error) {
//     handleParseError(env, "fact", index, start);
//     throw error;
//   }
// }

const factParserSignals: { [key: string]: Function } = {
  or: orParse,
  not: notParse,
  if: yaIfThenParse,
  "?": yaIfThenParse,
};

function factParse(env: L_Env, tokens: string[], addHash = false): FactNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const relParser: Function | undefined = factParserSignals[tokens[0]];
    let out: FactNode;
    if (relParser === undefined) {
      out = shortCallOptParse(env, tokens, addHash);
    } else {
      out = relParser(env, tokens, addHash);
    }

    if (isCurToken(tokens, "by")) {
      skip(tokens, "by")
      skip(tokens, "{")
      const bys = listParse<FactNode>(env, tokens, factParse, ["}"]);
      return new ByNode(out, bys)
    }

    return out;
  } catch (error) {
    handleParseError(env, "fact", index, start);
    throw error;
  }
}

// parse p1:p2:p3(x1,x2:x3:x4,x5,x6)
function shortCallOptParse(
  env: L_Env,
  tokens: string[],
  addHash = false
): ShortCallOptNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    let nameAsParam: string[] = [];
    while (!isCurToken(tokens, "(")) {
      let curTok = shiftVar(tokens);
      nameAsParam.push(curTok);
      if (isCurToken(tokens, ":")) skip(tokens, ":");
    }

    skip(tokens, "(");
    const params: string[][] = [];
    while (!isCurToken(tokens, ")")) {
      const curParams: string[] = [];

      while (!isCurToken(tokens, ":") && !isCurToken(tokens, ")")) {
        let curTok = shiftVar(tokens);
        if (addHash && !env.declaredVars.includes(curTok)) {
          curTok = "#" + curTok;
        }
        curParams.push(curTok);
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }

      params.push(curParams);
      if (isCurToken(tokens, ":")) skip(tokens, ":");
    }

    skip(tokens, ")");

    return new ShortCallOptNode(nameAsParam.join(":"), params);
  } catch (error) {
    handleParseError(env, `${start} is invalid operator.`, index, start);
    throw error;
  }
}

function notParse(env: L_Env, tokens: string[], addHash = false): FactNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, "not");
    const fact = factParse(env, tokens, addHash);
    fact.isT = false;
    return fact;
  } catch (error) {
    handleParseError(env, "not", index, start);
    throw error;
  }
}

function orParse(env: L_Env, tokens: string[], addHash = false): OrNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, "or");

    skip(tokens, "{");

    const facts: FactNode[] = [];
    while (!isCurToken(tokens, "}")) {
      facts.push(factParse(env, tokens, addHash));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    skip(tokens, "}");
    return new OrNode(facts);
  } catch (error) {
    handleParseError(env, "or", index, start);
    throw error;
  }
}

// function arrowFuncParse(env: L_Env, tokens: string[]): IfThenNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     skip(tokens, "(");
//     const req: FactNode[] = [];
//     while (!isCurToken(tokens, ")")) {
//       req.push(factParse(env, tokens));
//       if (isCurToken(tokens, ",")) skip(tokens, ",");
//     }
//     skip(tokens, ")");

//     const onlyIfs: FactNode[] = [];
//     skip(tokens, "=>");
//     skip(tokens, "{");
//     while (!isCurToken(tokens, "}")) {
//       onlyIfs.push(factParse(env, tokens));
//       if (isCurToken(tokens, ",")) skip(tokens, ",");
//     }
//     skip(tokens, "}");

//     return new IfThenNode(req, onlyIfs);
//   } catch (error) {
//     handleParseError(env, "()=>{}", index, start);
//     throw error;
//   }
// }

function yaIfThenParse(
  env: L_Env,
  tokens: string[],
  addHash = false
): IfThenNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, ["if", "?"]);

    const vars = varLstParse(
      env,
      tokens,
      ["|", ...ThenKeywords],
      false,
      addHash
    );

    // const vars = listParse<string>(
    //   env,
    //   tokens,
    //   (env: L_Env, tokens: string[]) => {
    //     return shiftVar(tokens);
    //   },

    //   false
    // );

    let req: FactNode[] = [];
    if (ThenKeywords.includes(tokens[0])) {
      skip(tokens, ThenKeywords);
    } else {
      skip(tokens, "|");
      req = listParse<FactNode>(
        env,
        tokens,
        factParse,
        ["=>", "then"],
        true,
        addHash
      );
    }

    let onlyIfs: ShortCallOptNode[];
    if (!isCurToken(tokens, "{")) {
      const fact = factParse(env, tokens, addHash);
      if (!(fact instanceof ShortCallOptNode))
        throw Error(`${fact.toString()} is not operator-type fact.`);
      else onlyIfs = [fact];
    } else {
      skip(tokens, "{");
      const out = listParse<FactNode>(
        env,
        tokens,
        factParse,
        ["}"],
        true,
        addHash
      );
      if (out.every((e) => e instanceof ShortCallOptNode)) {
        onlyIfs = out as ShortCallOptNode[];
      } else {
        throw Error(`Not all onlyIfs are operator-type fact.`);
      }
    }

    let name = "";
    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
      name = shiftVar(tokens);
      skip(tokens, "]");
    }
    const out = new IfThenNode(vars, req, onlyIfs);
    out.useName = name;
    return out;
  } catch (error) {
    handleParseError(env, "()=>{}", index, start);
    throw error;
  }
}

function listParse<T>(
  env: L_Env,
  tokens: string[],
  parseFunc: (env: L_Env, tokens: string[], ...args: any[]) => T,
  end: string[],
  skipEnd: Boolean = true,
  addHash: Boolean = false,
  separation: string = ","
): T[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const out: T[] = [];
    while (!end.includes(tokens[0])) {
      out.push(parseFunc(env, tokens, addHash));
      if (isCurToken(tokens, separation)) skip(tokens, separation);
    }

    if (skipEnd) skip(tokens, end);

    return out;
  } catch (error) {
    handleParseError(env, "Parsing variables", index, start);
    throw error;
  }
}

function varLstParse(
  env: L_Env,
  tokens: string[],
  end: string[],
  skipEnd: Boolean = true,
  addHash: Boolean = true,
  separation: string = ","
): string[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const out: string[] = [];
    while (!end.includes(tokens[0])) {
      let curTok = shiftVar(tokens);
      if (addHash && !env.declaredVars.includes(curTok)) {
        curTok = "#" + curTok;
      }
      out.push(curTok);
      if (isCurToken(tokens, separation)) skip(tokens, separation);
    }

    if (skipEnd) skip(tokens, end);

    return out;
  } catch (error) {
    handleParseError(env, "Parsing variables", index, start);
    throw error;
  }
}

function DeclNodeParse(env: L_Env, tokens: string[]): DeclNode {
  const start = tokens[0];
  const index = tokens.length;
  try {
    let nodeType = shiftVar(tokens);
    const name = shiftVar(tokens);

    if (IfThenKeywords.includes(tokens[0])) {
      nodeType = shiftVar(tokens);
    }

    const vars = varLstParse(env, tokens, ["|", ...StdStmtEnds], false, true);

    // const vars = listParse<string>(
    //   env,
    //   tokens,
    //   (env: L_Env, tokens: string[]) => {
    //     return shiftVar(tokens);
    //   },
    //   ["|", ...StdStmtEnds],
    //   false
    // );

    if (StdStmtEnds.includes(tokens[0])) {
      skip(tokens, StdStmtEnds);
      return new DefDeclNode(name, vars);
    } else {
      skip(tokens, "|");
    }

    const req = listParse<FactNode>(
      env,
      tokens,
      factParse,
      [...StdStmtEnds, "=>"],
      false,
      true //! DeclNodeParse addHash = true
    );

    let onlyIfs: ShortCallOptNode[] = [];
    if (StdStmtEnds.includes(tokens[0])) {
      skip(tokens, StdStmtEnds);
    } else if (isCurToken(tokens, "=>")) {
      nodeType = IfThenKeywords[0]
      skip(tokens, "=>");

      if (!isCurToken(tokens, "{")) {
        onlyIfs = [shortCallOptParse(env, tokens, true)];
      } else {
        skip(tokens, "{");
        onlyIfs = listParse<ShortCallOptNode>(
          env,
          tokens,
          shortCallOptParse,
          ["}"],
          true,
          true
        );
      }
    }

    if (IfThenKeywords.includes(nodeType)) {
      return new IfThenDeclNode(name, vars, req, onlyIfs);
    } else if (DefKeywords.includes(nodeType)) {
      return new DefDeclNode(name, vars, req, onlyIfs);
    }

    throw Error();
  } catch (error) {
    handleParseError(env, "Parsing variables", index, start);
    throw error;
  }
}
