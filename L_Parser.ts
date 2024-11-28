import {
  ByNode,
  DefNode,
  ExistNode,
  HaveNode,
  IfDefNode,
  IffNode,
  IfNode,
  KnowNode,
  L_Node,
  LetNode,
  LocalEnvNode,
  LogicNode,
  MacroNode,
  OptNode,
  OrNode,
  PostfixProve,
  ProveNode,
  ReturnNode,
  SpecialNode,
  ToCheckNode,
} from "./L_Nodes.ts";
import { L_Env } from "./L_Env.ts";
import {
  AreKeywords,
  ByKeyword,
  ClearKeyword,
  ContradictionKeyword,
  DefKeywords,
  ExistKeyword,
  HaveKeywords,
  IffKeywords,
  IfKeywords,
  IsKeywords,
  KnowTypeKeywords,
  L_Ends,
  L_Keywords,
  LetKeywords,
  LogicalKeywords,
  LogicalOptPairs,
  MacroKeywords,
  NotKeywords,
  NotsKeyword,
  OrKeywords,
  PostProveKeywords,
  ProveByContradictionKeyword,
  ProveKeywords,
  ReturnKeyword,
  RunKeyword,
  UseKeyword,
} from "./L_Common.ts";

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

function isCurToken(tokens: string[], s: string | string[]) {
  if (!Array.isArray(s)) {
    return s === tokens[0];
  } else {
    return s.includes(tokens[0]);
  }
}

function handleParseError(
  env: L_Env,
  m: string,
  index: number,
  start: string = "",
) {
  env.newMessage(`At ${start}[${index * -1}]: ${m}`);
}

export function parseUntilGivenEnd(
  env: L_Env,
  tokens: string[],
  end: string | null,
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
  [key: string]: Function;
} = {
  know: knowParse,
  let: letParse,
  "{": localEnvParse,
  def: defParse,
  prove: proveParse,
  prove_by_contradiction: proveParse,
  have: haveParse,
  return: returnParse,
  clear: specialParse,
  run: specialParse,
  by: byParse,
  macro: macroParse,
  "[": postfixProveParse,
};

export function getNodesFromSingleNode(
  env: L_Env,
  tokens: string[],
  holder: L_Node[],
): void {
  const start = tokens[0];
  const index = tokens.length;
  try {
    if (tokens.length === 0) return;

    if (L_Ends.includes(tokens[0])) {
      tokens.shift();
      while (tokens.length > 0 && L_Ends.includes(tokens[0])) {
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
      const postProve = postfixProveParse(env, tokens, L_Ends, true);
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

function postfixProveParse(
  env: L_Env,
  tokens: string[],
  end: string[] = [...L_Ends],
  skipEnd: boolean = false,
): PostfixProve {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const names: string[] = [];
    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
      while (!isCurToken(tokens, "]")) {
        names.push(shiftVar(tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }
      skip(tokens, "]");
    }

    const facts = factsParse(
      env,
      tokens,
      [...end, ...PostProveKeywords],
      false,
      true,
    );
    const block: L_Node[] = [];
    if (PostProveKeywords.includes(tokens[0])) {
      skip(tokens, PostProveKeywords);
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

    return new PostfixProve(facts, block, names);
  } catch (error) {
    handleParseError(env, "fact", index, start);
    throw error;
  }
}

function knowParse(env: L_Env, tokens: string[]): KnowNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, KnowTypeKeywords);

    const names: string[] = [];
    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
      while (!isCurToken(tokens, "]")) {
        names.push(shiftVar(tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }
      skip(tokens, "]");
    }

    let facts: ToCheckNode[] = [];
    // const strict = keyword === "know" ? false : true;

    // const knowNode: KnowNode = new KnowNode([], []);
    while (!L_Ends.includes(tokens[0])) {
      facts = factsParse(env, tokens, [...L_Ends, ","], false, true);
      // knowNode.facts = knowNode.facts.concat(outs);

      if (tokens[0] === ",") skip(tokens, ",");
    }
    skip(tokens, L_Ends);

    return new KnowNode(facts, names);
    // return knowNode;
  } catch (error) {
    handleParseError(env, "know", index, start);
    throw error;
  }
}

function letParse(env: L_Env, tokens: string[]): LetNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, LetKeywords);

    const names: string[] = [];
    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
      while (!isCurToken(tokens, "]")) {
        names.push(shiftVar(tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }
      skip(tokens, "]");
    }

    const vars: string[] = [];
    while (![...L_Ends, , ":"].includes(tokens[0])) {
      vars.push(shiftVar(tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    if (vars.some((e) => L_Keywords.includes(e))) {
      env.newMessage(`Error: ${vars} contain LiTeX keywords.`);
      throw Error();
    }

    if (L_Ends.includes(tokens[0])) {
      skip(tokens, L_Ends);
      return new LetNode(vars, [], names);
    } else {
      skip(tokens, ":");
      const facts = factsParse(env, tokens, L_Ends, true, true);
      return new LetNode(vars, facts, names);
    }
  } catch (error) {
    handleParseError(env, "let", index, start);
    throw error;
  }
}

function optParseWithNot(
  env: L_Env,
  tokens: string[],
  parseNot: boolean,
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

    let checkVars: string[][] | undefined = undefined;

    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
      checkVars = [];
      while (!isCurToken(tokens, "]")) {
        const currentLayerVars = varLstParse(env, tokens, [";", "]"]);
        checkVars.push(currentLayerVars);
        if (isCurToken(tokens, ";")) skip(tokens, ";");
      }
      skip(tokens, "]");
    }

    return new OptNode(name, vars, isT, undefined, checkVars);
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
  separation: string = ",",
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

    let toProve: null | LogicNode = null;
    let fixedIfThenOpt: null | OptNode = null;

    if (IfKeywords.includes(tokens[0])) {
      toProve = logicParse(env, tokens, false);
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
      skip(tokens, L_Ends);
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

// Main Function of parser
function factsParse(
  env: L_Env,
  tokens: string[],
  end: string[],
  skipEnd: boolean,
  includeDefName: boolean,
): ToCheckNode[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    let out: ToCheckNode[] = [];

    while (!end.includes(tokens[0])) {
      // Start of former singleNodeFacts logic
      const factStart = tokens[0];
      const factIndex = tokens.length;

      try {
        let isT = true;
        if (isCurToken(tokens, "not")) {
          isT = false;
          skip(tokens, "not");
        }

        let fact: ToCheckNode;
        if (LogicalKeywords.includes(tokens[0])) {
          fact = logicParse(env, tokens, includeDefName);
          fact.isT = isT ? fact.isT : !fact.isT;
          out = [...out, fact];
        } else if (tokens[0] === "or") {
          fact = orParse(env, tokens, includeDefName);
          fact.isT = isT ? fact.isT : !fact.isT;
          out = [...out, fact];
        } else if (tokens[0] === "nots") {
          fact = notsParse(env, tokens, includeDefName);
          fact.isT = isT ? fact.isT : !fact.isT;
          out = [...out, fact];
        } // else if (tokens[0] === "exist") {
        //   fact = logicParse(env, tokens, includeDefName);
        //   fact.isT = isT ? fact.isT : !fact.isT;
        //   out = [...out, fact];
        // }
        else if (tokens[0] === "exist") {
          fact = existParse(env, tokens, includeDefName);
          fact.isT = isT ? fact.isT : !fact.isT;
          out = [...out, fact];
        } else {
          const facts = optParseWithNotAre(env, tokens, true, includeDefName);
          facts.forEach((e) => (e.isT = isT ? e.isT : !e.isT));
          out = [...out, ...facts];
        }
      } catch (error) {
        handleParseError(env, "fact", factIndex, factStart);
        throw error;
      }
      // End of former singleNodeFacts logic

      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    if (skipEnd) skip(tokens, end);

    return out;
  } catch (error) {
    handleParseError(env, "fact", index, start);
    throw error;
  }
}

function optParseWithNotAre(
  env: L_Env,
  tokens: string[],
  parseNot: boolean,
  _includeDefName: boolean,
): OptNode[] {
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

      // let defName: undefined | string = undefined;
      // if (includeDefName && isCurToken(tokens, "[")) {
      //   skip(tokens, "[");
      //   defName = shiftVar(tokens);
      //   skip(tokens, "]");
      // }

      let checkVars: string[][] | undefined = undefined;
      if (isCurToken(tokens, "[")) {
        skip(tokens, "[");
        checkVars = [];
        while (!isCurToken(tokens, "]")) {
          const currentLayerVars = varLstParse(env, tokens, [";", "]"], false);
          checkVars.push(currentLayerVars);
          if (isCurToken(tokens, ";")) skip(tokens, ";");
        }
        skip(tokens, "]");
      }

      return [new OptNode(name, vars, isT, undefined, checkVars)];
    } else {
      while (![...AreKeywords, ...IsKeywords].includes(tokens[0])) {
        const v = shiftVar(tokens);
        vars.push(v);
        if (tokens[0] === ",") skip(tokens, ",");
      }

      skip(tokens, [...AreKeywords, ...IsKeywords]);

      if (parseNot && NotKeywords.includes(tokens[0])) {
        isT = !isT;
        skip(tokens, NotKeywords);
      }

      name = shiftVar(tokens);

      // let defName: undefined | string = undefined;
      // if (includeDefName && isCurToken(tokens, "[")) {
      //   skip(tokens, "[");
      //   defName = shiftVar(tokens);
      //   skip(tokens, "]");
      // }

      let checkVars: string[][] | undefined = undefined;
      if (isCurToken(tokens, "[")) {
        skip(tokens, "[");
        checkVars = [];
        while (!isCurToken(tokens, "]")) {
          const currentLayerVars = varLstParse(env, tokens, [";", "]"]);
          checkVars.push(currentLayerVars);
          if (isCurToken(tokens, ";")) skip(tokens, ";");
        }
        skip(tokens, "]");
      }

      const outs = vars.map(
        (e) => new OptNode(name, [e], isT, undefined, checkVars),
      );
      // outs[outs.length - 1].defName = undefined;
      return outs;
    }
  } catch (error) {
    handleParseError(env, `${start} is invalid operator.`, index, start);
    throw error;
  }
}

function logicParse(
  env: L_Env,
  tokens: string[],
  includeDefName: boolean,
): LogicNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const type = skip(tokens, [...IfKeywords, ExistKeyword, ...IffKeywords]);
    if (type === undefined) throw Error();
    const separation = LogicalOptPairs[type];

    const symbolsBeforeThenKeyword: string[] = [];
    for (let i = 0; i < tokens.length; i++) {
      if (!separation.includes(tokens[i])) {
        symbolsBeforeThenKeyword.push(tokens[i]);
      } else break;
    }

    let vars: string[] = [];
    let req: ToCheckNode[] = [];
    if (symbolsBeforeThenKeyword.includes(":")) {
      vars = varLstParse(env, tokens, [":"], false);
      skip(tokens, ":");

      req = factsParse(env, tokens, separation, true, includeDefName);
    } else {
      req = factsParse(env, tokens, separation, true, includeDefName);
    }

    let reqName: null | string = null;
    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
      reqName = shiftVar(tokens);
      skip(tokens, "]");
    }

    skip(tokens, "{");

    const onlyIfs = factsParse(env, tokens, ["}"], true, includeDefName);

    let defName: string | undefined = undefined;

    if (includeDefName && isCurToken(tokens, "[")) {
      skip(tokens, "[");
      defName = shiftVar(tokens);
      skip(tokens, "]");
    }

    if (IfKeywords.includes(type)) {
      return new IfNode(vars, req, onlyIfs, true, defName, reqName);
    } else if (IffKeywords.includes(type)) {
      return new IffNode(vars, req, onlyIfs, true, defName, reqName);
    }
    throw Error();
  } catch (error) {
    handleParseError(env, "if-then", index, start);
    throw error;
  }
}

// function defParse(env: L_Env, tokens: string[]): DefNode {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     skip(tokens, DefKeywords);

//     const opt: OptNode = optParseWithNot(env, tokens, false);

//     let req: ToCheckNode[] = [];
//     if (isCurToken(tokens, ":")) {
//       skip(tokens, ":");
//       const ends = ["=>", "<=>", "<=", ...L_Ends, ExistKeyword];
//       req = factsParse(env, tokens, ends, false, false);
//     }

//     if (L_Ends.includes(tokens[0])) {
//       //! MAYBE I SHOULD SIMPLY RETURN DefNode
//       return new IfDefNode(opt.name, opt.vars, [], []);
//     }

//     const separator = shiftVar(tokens);

//     if (
//       ThenKeywords.includes(separator) ||
//       IffThenKeywords.includes(separator) ||
//       OnlyIfThenKeywords.includes(separator)
//     ) {
//       let onlyIfs: ToCheckNode[] = [];

//       if (isCurToken(tokens, "{")) {
//         skip(tokens, "{");
//         onlyIfs = factsParse(env, tokens, ["}"], false, true);
//         skip(tokens, "}");
//       }
//       skip(tokens, L_Ends);

//       if (ThenKeywords.includes(separator)) {
//         return new IfDefNode(opt.name, opt.vars, req, onlyIfs);
//       } else if (IffThenKeywords.includes(separator)) {
//         return new IffDefNode(opt.name, opt.vars, req, onlyIfs);
//       } else {
//         return new OnlyIfDefNode(opt.name, opt.vars, req, onlyIfs);
//       }
//     } else if (ExistKeyword === separator) {
//       const existVars: string[] = [];
//       while (!isCurToken(tokens, "{")) {
//         existVars.push(shiftVar(tokens));
//         if (isCurToken(tokens, ",")) skip(tokens, ",");
//       }
//       // skip(tokens, ":");

//       skip(tokens, "{");
//       const existFacts = factsParse(env, tokens, ["}"], false, true);
//       skip(tokens, "}");

//       skip(tokens, L_Ends);
//       return new ExistDefNode(opt.name, opt.vars, req, existVars, existFacts);
//     }

//     throw Error();
//   } catch (error) {
//     handleParseError(env, "define", index, start);
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
    const facts = factsParse(env, tokens, L_Ends, true, false);
    return new ReturnNode(facts);
  } catch (error) {
    handleParseError(env, "return/so", index, start);
    throw error;
  }
}

function orParse(
  env: L_Env,
  tokens: string[],
  includeDefName: boolean,
): OrNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, OrKeywords);
    skip(tokens, "{");
    const facts = factsParse(env, tokens, ["}"], false, includeDefName);
    skip(tokens, "}");

    let defName: undefined | string = undefined;
    if (includeDefName && isCurToken(tokens, "[")) {
      skip(tokens, "[");
      defName = shiftVar(tokens);
      skip(tokens, "]");
    }

    return new OrNode(facts, true, defName);
  } catch (error) {
    handleParseError(env, "operator", index, start);
    throw error;
  }
}

function notsParse(
  env: L_Env,
  tokens: string[],
  includeDefName: boolean,
): OrNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, NotsKeyword);
    skip(tokens, "{");
    const facts = factsParse(env, tokens, ["}"], false, includeDefName);
    for (const f of facts) {
      f.isT = !f.isT;
    }
    skip(tokens, "}");

    let defName: undefined | string = undefined;
    if (includeDefName && isCurToken(tokens, "[")) {
      skip(tokens, "[");
      defName = shiftVar(tokens);
      skip(tokens, "]");
    }

    return new OrNode(facts, true, defName);
  } catch (error) {
    handleParseError(env, "nots", index, start);
    throw error;
  }
}

function haveParse(env: L_Env, tokens: string[]): HaveNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, HaveKeywords);
    const opt = optParseWithNot(env, tokens, false);
    skip(tokens, ":");
    const vars: string[] = [];
    while (!L_Ends.includes(tokens[0])) {
      vars.push(shiftVar(tokens));
      if (tokens[0] === ",") skip(tokens, ",");
    }

    skip(tokens, L_Ends);
    return new HaveNode(opt, vars);
  } catch (error) {
    handleParseError(env, "have", index, start);
    throw error;
  }
}

function existParse(
  env: L_Env,
  tokens: string[],
  includeDefName: boolean,
): ExistNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, ExistKeyword);
    const vars = varLstParse(env, tokens, ["{"], true);
    const facts = factsParse(env, tokens, ["}"], true, includeDefName);
    let defName: undefined | string = undefined;
    if (includeDefName && isCurToken(tokens, "[")) {
      skip(tokens, "[");
      defName = shiftVar(tokens);
      skip(tokens, "]");
    }

    return new ExistNode(vars, facts, true, defName);
  } catch (error) {
    handleParseError(env, "exist", index, start);
    throw error;
  }
}

function specialParse(env: L_Env, tokens: string[]): SpecialNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const keyword = shiftVar(tokens);
    switch (keyword) {
      case ClearKeyword:
        skip(tokens, L_Ends);
        return new SpecialNode(ClearKeyword, null);
      case RunKeyword: {
        const words: string[] = [];
        while (!L_Ends.includes(tokens[0])) {
          words.push(shiftVar(tokens));
        }
        skip(tokens, L_Ends);
        return new SpecialNode(RunKeyword, words.join());
      }
      default:
        throw Error();
    }
  } catch (error) {
    handleParseError(env, "clear", index, start);
    throw error;
  }
}

function byParse(env: L_Env, tokens: string[]): ByNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, ByKeyword);
    const outs: OptNode[] = [];
    while (!isCurToken(tokens, L_Ends)) {
      const opt = optParseWithNot(env, tokens, true);
      outs.push(opt);
    }
    skip(tokens, L_Ends);

    return new ByNode(outs);
  } catch (error) {
    handleParseError(env, "by", index, start);
    throw error;
  }
}

function macroParse(env: L_Env, tokens: string[]): MacroNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, MacroKeywords);
    const regexString = shiftVar(tokens);
    const varName = shiftVar(tokens);
    const facts = factsParse(env, tokens, L_Ends, true, true);

    return new MacroNode(regexString, varName, facts);
  } catch (error) {
    handleParseError(env, "macro", index, start);
    throw error;
  }
}

function defParse(env: L_Env, tokens: string[]): DefNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, DefKeywords);

    const opt: OptNode = optParseWithNot(env, tokens, false);

    let cond: ToCheckNode[] = [];
    if (isCurToken(tokens, ":")) {
      skip(tokens, ":");
      cond = factsParse(env, tokens, L_Ends, false, false);
    }

    const onlyIfs: ToCheckNode[] = [];
    if (isCurToken(tokens, "{")) {
      skip(tokens, "{");
      onlyIfs.push(...factsParse(env, tokens, ["}"], false, false));
      skip(tokens, "}");
    }

    skip(tokens, L_Ends);
    return new IfDefNode(opt.name, opt.vars, cond, onlyIfs);
  } catch (error) {
    handleParseError(env, "define", index, start);
    throw error;
  }
}
