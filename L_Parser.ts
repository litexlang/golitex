import {
  KnowNode,
  L_Node,
  LetNode,
  OptNode,
  IfIffNode,
  DeclNode,
  IffDeclNode,
  FactNode,
  ProveNode,
  HaveNode,
  OnlyIfDeclNode,
  PostfixProve,
  IfThenDeclNode,
  LocalEnvNode,
  ReturnNode,
  // ReturnExistNode,
  ByNode,
  OrNode,
  ExistNode,
  STNode,
} from "./ast.ts";
import { L_Env } from "./L_Env.ts";
import {
  KnowTypeKeywords,
  StdStmtEnds,
  IfKeywords,
  LetKeywords,
  ThenKeywords,
  ProveKeywords,
  HaveKeywords,
  ProveByContradictionKeyword,
  IsKeywords,
  L_Keywords,
  IffKeywords,
  LogicalOptPairs,
  LogicalKeywords,
  PostfixProveKeywords,
  DefKeywords,
  IffThenKeywords,
  OnlyIfThenKeywords,
  ContradictionKeyword,
  ReturnKeyword,
  // ReturnExistKeyword,
  ByKeyword,
  OrKeywords,
  NotsKeyword,
  NotKeywords,
  ExistKeyword,
  STKeyword,
} from "./common.ts";

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

export function parseUntilGivenEnd(
  env: L_Env,
  tokens: string[],
  end: string | null
): L_Node[] {
  try {
    const out: L_Node[] = [];

    if (end !== null) {
      while (!isCurToken(tokens, end)) {
        getNodesFromSingleNode(env, tokens, out);
      }
    } else {
      while (tokens.length !== 0) {
        getNodesFromSingleNode(env, tokens, out);
      }
    }

    return out;
  } catch (error) {
    env.newMessage(`Error: Syntax Error.`);
    throw error;
  }
}

const KeywordFunctionMap: {
  // deno-lint-ignore ban-types
  [key: string]: Function; // (env: L_Env, tokens: string[]) => any;
} = {
  know: knowParse,
  let: letParse,
  "{": localEnvParse,
  def: defParse,
  prove: proveParse,
  prove_by_contradiction: proveParse,
  // exist: existParse,
  have: haveParse,
  return: returnParse,
  // return_exist: returnExistParse,
  by: byParse,
  st: stParse,
};

export function getNodesFromSingleNode(
  env: L_Env,
  tokens: string[],
  holder: L_Node[]
): void {
  const start = tokens[0];
  const index = tokens.length;
  try {
    // while (tokens.length > 0) {
    //   while (tokens.length > 0 && StdStmtEnds.includes(tokens[0])) {
    //     tokens.shift();
    //   }
    //   if (tokens.length === 0) return;
    //   break;
    // }

    if (tokens.length === 0) return;

    if (StdStmtEnds.includes(tokens[0])) {
      tokens.shift();
      while (tokens.length > 0 && StdStmtEnds.includes(tokens[0])) {
        tokens.shift();
      }
      return; // return is necessary because ; \n is empty expr.
    }

    const func = KeywordFunctionMap[tokens[0]];
    if (func) {
      const node = func(env, tokens);
      holder.push(node);
      return node;
    } else {
      const postProve = PostfixProveParse(env, tokens, StdStmtEnds, true);
      if (postProve.block.length === 0) {
        postProve.facts.forEach((e) => holder.push(e));
      } else {
        holder.push(postProve);
      }
    }
  } catch (error) {
    handleParseError(env, "node", index, start);
    throw error;
  }
}

function knowParse(env: L_Env, tokens: string[]): KnowNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const keyword = skip(tokens, KnowTypeKeywords);
    const strict = keyword === "know" ? false : true;

    const knowNode: KnowNode = new KnowNode([], strict);
    while (!StdStmtEnds.includes(tokens[0])) {
      const outs: FactNode[] = factsParse(
        env,
        tokens,
        [...StdStmtEnds, ","],
        false
      );
      knowNode.facts = knowNode.facts.concat(outs);

      if (tokens[0] === ",") skip(tokens, ",");
      else break;
    }
    skip(tokens, StdStmtEnds);

    return knowNode;
  } catch (error) {
    handleParseError(env, "know", index, start);
    throw error;
  }
}

function letParse(env: L_Env, tokens: string[]): LetNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const keyword = skip(tokens, LetKeywords);
    const strict = keyword === "let" ? false : true;

    const vars: string[] = [];
    while (![...StdStmtEnds, , ":"].includes(tokens[0])) {
      vars.push(shiftVar(tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    if (!vars.every((e) => !L_Keywords.includes(e))) {
      env.newMessage(`Error: ${vars} contain LiTeX keywords.`);
      throw Error();
    }

    if (StdStmtEnds.includes(tokens[0])) {
      skip(tokens, StdStmtEnds);
      return new LetNode(vars, [], strict);
    } else {
      skip(tokens, ":");
      const facts = factsParse(env, tokens, StdStmtEnds, true);
      return new LetNode(vars, facts, strict);
    }
  } catch (error) {
    handleParseError(env, "let", index, start);
    throw error;
  }
}

function optParseWithNot(
  env: L_Env,
  tokens: string[],
  parseNot: boolean
): OptNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    let name: string = "";
    const vars: string[] = [];
    let isT = true;

    if (tokens.length >= 2 && tokens[1] === "(") {
      // parse functional operator
      name = shiftVar(tokens);

      skip(tokens, "(");

      while (!isCurToken(tokens, ")")) {
        vars.push(shiftVar(tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }

      skip(tokens, ")");
    } else {
      const v = shiftVar(tokens);
      vars.push(v);

      skip(tokens, IsKeywords);

      if (parseNot && NotKeywords.includes(tokens[0])) {
        isT = !isT;
        skip(tokens, NotKeywords);
      }

      name = shiftVar(tokens);
    }

    return new OptNode(name, vars, isT);
  } catch (error) {
    handleParseError(env, `${start} is invalid operator.`, index, start);
    throw error;
  }
}

function varLstParse(
  env: L_Env,
  tokens: string[],
  end: string[],
  skipEnd: boolean = true,
  separation: string = ","
): string[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const out: string[] = [];
    while (!end.includes(tokens[0])) {
      const curTok = shiftVar(tokens);
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

function proveParse(env: L_Env, tokens: string[]): ProveNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    let byContradict = false;
    if (tokens[0] === ProveByContradictionKeyword) {
      byContradict = true;
      skip(tokens, ProveByContradictionKeyword);
    } else {
      skip(tokens, ProveKeywords);
    }

    let toProve: null | IfIffNode = null;
    let fixedIfThenOpt: null | OptNode = null;

    if (IfKeywords.includes(tokens[0])) {
      toProve = logicalOptParse(env, tokens);
    } else {
      fixedIfThenOpt = optParseWithNot(env, tokens, true);
    }

    const block: L_Node[] = [];
    skip(tokens, "{");
    while (tokens[0] !== "}") {
      while (["\n", ";"].includes(tokens[0])) {
        tokens.shift();
      }
      if (tokens[0] === "}") break;

      getNodesFromSingleNode(env, tokens, block);
    }

    skip(tokens, "}");

    let contradict: OptNode | undefined = undefined;
    if (byContradict) {
      skip(tokens, ContradictionKeyword);
      contradict = optParseWithNot(env, tokens, true);
      skip(tokens, StdStmtEnds);
    }

    if (toProve !== null) {
      return new ProveNode(toProve, null, block, contradict);
    } else {
      return new ProveNode(null, fixedIfThenOpt, block, contradict);
    }
  } catch (error) {
    handleParseError(env, "Parsing prove", index, start);
    throw error;
  }
}

function haveParse(env: L_Env, tokens: string[]): HaveNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, HaveKeywords);

    const vars: string[] = [];
    while (![...StdStmtEnds, , ":"].includes(tokens[0])) {
      vars.push(shiftVar(tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    if (!vars.every((e) => !L_Keywords.includes(e))) {
      env.newMessage(`Error: ${vars} contain LiTeX keywords.`);
      throw Error();
    }

    if (StdStmtEnds.includes(tokens[0])) {
      skip(tokens, StdStmtEnds);
      return new HaveNode(vars, []);
    } else {
      skip(tokens, ":");
      const facts: OptNode[] = [];

      while (!StdStmtEnds.includes(tokens[0])) {
        const fact = optParseWithNot(env, tokens, true);
        facts.push(fact);
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }
      skip(tokens, StdStmtEnds);

      return new HaveNode(vars, facts);
    }
  } catch (error) {
    handleParseError(env, "have", index, start);
    throw error;
  }
}

// Main Function of parser
function factsParse(
  env: L_Env,
  tokens: string[],
  end: string[],
  skipEnd: boolean = false
): FactNode[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const out: FactNode[] = [];
    while (!end.includes(tokens[0])) {
      const fact = factParse(env, tokens);
      out.push(fact);
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    if (skipEnd) skip(tokens, end);

    return out;
  } catch (error) {
    handleParseError(env, "fact", index, start);
    throw error;
  }
}

function factParse(env: L_Env, tokens: string[]): FactNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    let isT = true;
    if (isCurToken(tokens, "not")) {
      isT = false;
      skip(tokens, "not");
    }

    let fact: FactNode;
    if (LogicalKeywords.includes(tokens[0])) {
      fact = logicalOptParse(env, tokens);
    } else if (tokens[0] === "or") {
      fact = orParse(env, tokens);
    } else if (tokens[0] === "nots") {
      fact = notsParse(env, tokens);
    } else if (tokens[0] === "exist") {
      fact = logicalOptParse(env, tokens);
    } else {
      fact = optParseWithNot(env, tokens, true); // false: When using factsParse, not prefix are already removed.
    }

    fact.isT = isT ? fact.isT : !fact.isT;
    return fact;
  } catch (error) {
    handleParseError(env, "fact", index, start);
    throw error;
  }
}

function logicalOptParse(env: L_Env, tokens: string[]): IfIffNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const type = skip(tokens, [...IfKeywords, ExistKeyword, ...IffKeywords]);
    if (type === undefined) throw Error();
    const separation = LogicalOptPairs[type];

    const symbolsBeforeThenKeyword: string[] = [];
    for (let i = 0; i < tokens.length; i++) {
      if (!separation.includes(tokens[i]))
        symbolsBeforeThenKeyword.push(tokens[i]);
      else break;
    }

    let vars: string[] = [];
    let req: FactNode[] = [];
    if (symbolsBeforeThenKeyword.includes(":")) {
      vars = varLstParse(env, tokens, [":"], false);
      skip(tokens, ":");

      req = factsParse(env, tokens, separation, true);
    } else {
      req = factsParse(env, tokens, separation, true);
    }

    skip(tokens, "{");

    const onlyIfs = factsParse(env, tokens, ["}"], true);

    let byName: string | undefined = undefined;

    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
      byName = shiftVar(tokens);
      skip(tokens, "]");
    }

    if (IfKeywords.includes(type)) {
      return new IfIffNode(vars, req, onlyIfs, true, byName);
    } else if (IffKeywords.includes(type)) {
      return new IfIffNode(vars, req, onlyIfs, true, byName, true);
    } else if (ExistKeyword === type) {
      return new ExistNode(vars, req, onlyIfs, true, byName, false);
    }

    throw Error();
  } catch (error) {
    handleParseError(env, "if-then", index, start);
    throw error;
  }
}

function PostfixProveParse(
  env: L_Env,
  tokens: string[],
  end: string[],
  skipEnd: boolean = false
): PostfixProve {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const facts = factsParse(env, tokens, [...end, ...PostfixProveKeywords]);
    const block: L_Node[] = [];
    if (PostfixProveKeywords.includes(tokens[0])) {
      skip(tokens, PostfixProveKeywords);
      skip(tokens, "{");
      while (tokens[0] !== "}") {
        while (["\n", ";"].includes(tokens[0])) {
          tokens.shift();
        }
        if (tokens[0] === "}") break;

        getNodesFromSingleNode(env, tokens, block);
      }
      skip(tokens, "}");
    }

    if (skipEnd) skip(tokens, end);

    return new PostfixProve(facts, block);
  } catch (error) {
    handleParseError(env, "fact", index, start);
    throw error;
  }
}

function defParse(env: L_Env, tokens: string[]): DeclNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, DefKeywords);

    const opt: OptNode = optParseWithNot(env, tokens, false);

    let req: FactNode[] = [];
    if (isCurToken(tokens, ":")) {
      skip(tokens, ":");
      req = factsParse(env, tokens, ["=>", "<=>", "<=", ...StdStmtEnds], false);
    }

    const separator = shiftVar(tokens);

    skip(tokens, "{");
    const onlyIfs = factsParse(env, tokens, ["}"], false);
    skip(tokens, "}");

    // let req: FactNode[] = [];
    // if (tokens[0] === WhenKeyword) {
    //   skip(tokens, WhenKeyword);
    //   req = factsParse(env, tokens, StdStmtEnds, false);
    // }

    let byName: undefined | string = undefined;
    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
      byName = shiftVar(tokens);
      skip(tokens, "]");
    }

    skip(tokens, StdStmtEnds);

    if (ThenKeywords.includes(separator)) {
      return new IfThenDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
    } else if (IffThenKeywords.includes(separator)) {
      return new IffDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
    } else if (OnlyIfThenKeywords.includes(separator)) {
      return new OnlyIfDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
    }

    throw Error();
  } catch (error) {
    handleParseError(env, "define", index, start);
    throw error;
  }
}

// function defineParse(env: L_Env, tokens: string[]): DeclNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     skip(tokens, DefKeywords);

//     let byName: undefined | string = undefined;
//     if (isCurToken(tokens, "[")) {
//       skip(tokens, "[");
//       byName = shiftVar(tokens);
//       skip(tokens, "]");
//     }

//     const opt: OptNode = optParseWithNot(env, tokens, false);
//     const separator = shiftVar(tokens);

//     const onlyIfs = factsParse(
//       env,
//       tokens,
//       StdStmtEnds.concat(WhenKeyword),
//       false
//     );

//     let req: FactNode[] = [];
//     if (tokens[0] === WhenKeyword) {
//       skip(tokens, WhenKeyword);
//       req = factsParse(env, tokens, StdStmtEnds, false);
//     }

//     skip(tokens, StdStmtEnds);

//     if (ThenKeywords.includes(separator)) {
//       return new IfThenDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
//     } else if (IffThenKeywords.includes(separator)) {
//       return new IffDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
//     } else if (OnlyIfThenKeywords.includes(separator)) {
//       return new OnlyIfDeclNode(opt.fullName, opt.vars, req, onlyIfs, byName);
//     }

//     throw Error();
//   } catch (error) {
//     handleParseError(env, "fact", index, start);
//     throw error;
//   }
// }

function localEnvParse(env: L_Env, tokens: string[]): LocalEnvNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, "{");
    const nodes = parseUntilGivenEnd(env, tokens, "}");
    skip(tokens, "}");
    const out = new LocalEnvNode(nodes);
    return out;
  } catch (error) {
    handleParseError(env, "{}", index, start);
    throw error;
  }
}

function returnParse(env: L_Env, tokens: string[]): ReturnNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, ReturnKeyword);
    const facts = factsParse(env, tokens, StdStmtEnds, true);
    return new ReturnNode(facts);
  } catch (error) {
    handleParseError(env, "return/so", index, start);
    throw error;
  }
}

// function returnExistParse(env: L_Env, tokens: string[]): ReturnExistNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     skip(tokens, ReturnExistKeyword);
//     const names: string[] = [];
//     while (StdStmtEnds.includes(tokens[0])) {
//       names.push(shiftVar(tokens));
//       if (isCurToken(tokens, ",")) {
//         skip(tokens, ",");
//       }
//     }

//     return new ReturnExistNode(names);
//   } catch (error) {
//     handleParseError(env, "return_exist", index, start);
//     throw error;
//   }
// }

// function existParse(env: L_Env, tokens: string[]): ExistNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     skip(tokens, ExistKeywords);
//     const facts: OptNode[] = [];

//     while (!StdStmtEnds.includes(tokens[0])) {
//       const fact = optParseWithNot(env, tokens, true);
//       facts.push(fact);
//       if (isCurToken(tokens, ",")) skip(tokens, ",");
//     }
//     skip(tokens, StdStmtEnds);

//     return new ExistNode(facts);
//   } catch (error) {
//     handleParseError(env, "Exist prove", index, start);
//     throw error;
//   }
// }

function byParse(env: L_Env, tokens: string[]): ByNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, ByKeyword);
    const byName = shiftVar(tokens);
    skip(tokens, "(");
    const vars: string[] = [];
    while (!isCurToken(tokens, ")")) {
      vars.push(shiftVar(tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }
    skip(tokens, ")");

    if (!isCurToken(tokens, "=>")) {
      return new ByNode(byName, vars, []);
    }

    skip(tokens, "=>");

    skip(tokens, "{");

    const facts = factsParse(env, tokens, ["}"], true);

    skip(tokens, StdStmtEnds);

    return new ByNode(byName, vars, facts);
  } catch (error) {
    handleParseError(env, "by", index, start);
    throw error;
  }
}

function stParse(env: L_Env, tokens: string[]): STNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, STKeyword);
    const byName = shiftVar(tokens);
    skip(tokens, "(");
    const vars: string[] = [];
    while (!isCurToken(tokens, ")")) {
      vars.push(shiftVar(tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }
    skip(tokens, ")");

    return new STNode(byName, vars);
  } catch (error) {
    handleParseError(env, "st", index, start);
    throw error;
  }
}

// function parseVanillaOptWithNot(
//   env: L_Env,
//   tokens: string[],
//   withNot: boolean
// ): OptNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     let isT = true;

//     if (isCurToken(tokens, "not") && withNot) {
//       isT = false;
//       skip(tokens, "not");
//     }

//     if (tokens.length >= 2 && tokens[1] === "(") {
//       const fact = optParseWithNot(env, tokens, false);
//       fact.isT = isT;
//       return fact;
//     } else {
//       const varName = shiftVar(tokens);
//       const vars: string[] = [varName];
//       skip(tokens, IsKeywords);

//       if (isCurToken(tokens, "not") && withNot) {
//         skip(tokens, "not");
//         isT = !isT;
//       }

//       const optName = shiftVar(tokens);
//       return new OptNode(optName, vars, isT);
//     }
//   } catch (error) {
//     handleParseError(env, "operator", index, start);
//     throw error;
//   }
// }

// function parseAreIsOpts(env: L_Env, tokens: string[]): OptNode[] {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     const out: OptNode[] = [];
//     let isT = true;

//     if (isCurToken(tokens, "not")) {
//       isT = false;
//       skip(tokens, "not");
//     }

//     const vars: string[] = [];
//     while (!IsAreKeywords.includes(tokens[0])) {
//       vars.push(shiftVar(tokens));
//       if (isCurToken(tokens, ",")) skip(tokens, ",");
//     }
//     const isAre = skip(tokens, IsAreKeywords) as string;

//     if (isCurToken(tokens, "not")) {
//       skip(tokens, "not");
//       isT = !isT;
//     }

//     if (AreKeywords.includes(isAre)) {
//       if (vars.length < 2) {
//         handleParseError(
//           env,
//           "`are` requires more than 1 parameters.",
//           index,
//           start
//         );
//         throw Error();
//       }
//     } else {
//       if (vars.length !== 1) {
//         handleParseError(
//           env,
//           "`is` requires exactly one parameter.",
//           index,
//           start
//         );
//         throw Error();
//       }
//     }

//     const optName = shiftVar(tokens);
//     for (const v of vars) {
//       const fact = new OptNode(optName, [v]);
//       fact.isT = isT;
//       out.push(fact);
//     }

//     return out;
//   } catch (error) {
//     handleParseError(env, "operator", index, start);
//     throw error;
//   }
// }

function orParse(env: L_Env, tokens: string[]): OrNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, OrKeywords);
    skip(tokens, "{");
    const facts = factsParse(env, tokens, ["}"], false);
    skip(tokens, "}");

    return new OrNode(facts, true);
  } catch (error) {
    handleParseError(env, "operator", index, start);
    throw error;
  }
}

function notsParse(env: L_Env, tokens: string[]): OrNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, NotsKeyword);
    skip(tokens, "{");
    const facts = factsParse(env, tokens, ["}"], false);
    for (const f of facts) {
      f.isT = !f.isT;
    }
    skip(tokens, "}");

    return new OrNode(facts, true);
  } catch (error) {
    handleParseError(env, "nots", index, start);
    throw error;
  }
}
