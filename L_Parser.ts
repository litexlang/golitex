import { L_Node, LogicNode, ToCheckNode, OptNode } from "./L_Nodes";
import * as L_Nodes from "./L_Nodes";
import { L_Env } from "./L_Env";
import {
  ClearKeyword,
  DefKeywords,
  HaveKeywords,
  IffKeyword,
  IfKeyword,
  KnowTypeKeywords,
  L_Ends,
  L_Keywords,
  LetKeyword,
  LetKeywords,
  LogicalKeywords,
  MacroKeywords,
  PostProveKeywords,
  ProveByContradictionKeyword,
  ProveKeywords,
  ReturnKeyword,
  RunKeyword,
  SlashKeyword,
} from "./L_Common";
import * as L_Common from "./L_Common";
import {
  CompositeSymbolInIfReq,
  L_Composite,
  L_OptSymbol,
  L_Singleton,
  L_Symbol,
} from "./L_Structs";
import { isBuiltinKeyword, L_BuiltinParsers } from "./L_Builtins";

function arrParse<T>(
  env: L_Env,
  tokens: string[],
  parseFunc: Function,
  begin: string[] | string | undefined,
  end: string[] | string,
  skipEnd: boolean = true
): T[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    if (begin !== undefined) skip(tokens, begin);
    const out: T[] = [];
    while (!isCurToken(tokens, end)) {
      out.push(parseFunc(env, tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }
    if (skipEnd) skip(tokens, end);

    return out;
  } catch (error) {
    handleParseError(env, tokens, `parse an array`, index, start);
    throw error;
  }
}

function singletonParse(env: L_Env, tokens: string[]): L_Singleton {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const value = skip(tokens) as string;
    return new L_Singleton(value);
  } catch (error) {
    handleParseError(env, tokens, "parse singleton", index, start);
    throw error;
  }
}

function optSymbolParse(env: L_Env, tokens: string[]): L_OptSymbol {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const name = skip(tokens) as string;
    return new L_OptSymbol(name);
  } catch (error) {
    handleParseError(env, tokens, "parse singleton", index, start);
    throw error;
  }
}

function compositeParse(env: L_Env, tokens: string[]): L_Composite {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Common.SlashKeyword);
    const name = skip(tokens, tokens);
    skip(tokens, "{");
    const values: L_Symbol[] = [];
    while (!isCurToken(tokens, "}")) {
      values.push(symbolParse(env, tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }
    skip(tokens, "}");
    return new L_Composite(name, values);
  } catch (error) {
    handleParseError(env, tokens, "parse singleton", index, start);
    throw error;
  }
}

function compositeInIfReqParse(
  env: L_Env,
  tokens: string[]
): CompositeSymbolInIfReq {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const composite = compositeParse(env, tokens);
    // TODO IT SEEMS VARS AFTER COMPOSITE IS UNNECESSARY
    const vars = arrParse<L_Singleton>(
      env,
      tokens,
      singletonParse,
      "[",
      "]",
      true
    );
    return new CompositeSymbolInIfReq(composite.name, composite.values, vars);
  } catch (error) {
    handleParseError(env, tokens, "parse singleton", index, start);
    throw error;
  }
}

function symbolParse(env: L_Env, tokens: string[]): L_Symbol {
  const start = tokens[0];
  const index = tokens.length;

  try {
    if (tokens[0] === L_Common.SlashKeyword) {
      return compositeParse(env, tokens);
    } else {
      return singletonParse(env, tokens);
    }
  } catch (error) {
    handleParseError(env, tokens, "parse symbol", index, start);
    throw error;
  }
}

function skip(tokens: string[], s: string | string[] = ""): string {
  try {
    if (typeof s === "string") {
      if (s === "") {
        const out = tokens.shift();
        if (out === undefined) throw Error;
        return out;
      } else if (s === tokens[0]) {
        const out = tokens.shift();
        if (out === undefined) throw Error;
        return out;
      } else {
        throw Error("unexpected symbol: " + tokens[0]);
      }
    } else {
      for (const value of s) {
        if (value === tokens[0]) {
          const out = tokens.shift();
          if (out === undefined) throw Error;
          return out;
        }
      }
      throw Error("unexpected symbol: " + tokens[0]);
    }
  } catch {
    throw Error();
  }
}

//! Not only gets symbol, in the future it will parse $$
function shiftSymbol(tokens: string[]): string {
  if (tokens[0].startsWith("\\")) {
    const name = tokens[0];
    const outs = [tokens[0]];
    tokens.shift();
    let leftBraceNum = 1;
    skip(tokens, "{");
    outs.push("{");
    let rightBraceNum = 0;

    while (leftBraceNum !== rightBraceNum) {
      if (tokens[0] === "{") leftBraceNum++;
      else if (tokens[0] === "}") rightBraceNum++;
      outs.push(tokens[0]);
      tokens.shift();
    }

    if (isCurToken(tokens, "[")) {
      outs.push(tokens[0]);
      let leftBracketNum = 1;
      skip(tokens, "[");
      let rightBracketNum = 0;
      while (leftBracketNum !== rightBracketNum) {
        if (tokens[0] === "[") leftBracketNum++;
        else if (tokens[0] === "]") rightBracketNum++;
        outs.push(tokens[0]);
        tokens.shift();
      }
    }

    const out = outs.join(" ");

    return outs.join(" ");
  } else {
    const token = tokens.shift();
    if (typeof token !== "string") {
      throw new Error("No more tokens");
    }
    return token;
  }
}

function isCurToken(tokens: string[], s: string | string[]) {
  if (!Array.isArray(s)) {
    return s === tokens[0];
  } else {
    return s.includes(tokens[0]);
  }
}

function skipString(tokens: string[]): string {
  try {
    skip(tokens, '"');
    let out = "";
    while (!isCurToken(tokens, '"')) {
      out += tokens[0];
      shiftSymbol(tokens);
    }
    skip(tokens, '"');
    return out;
  } catch {
    throw Error();
  }
}

function handleParseError(
  env: L_Env,
  tokens: string[],
  m: string,
  index: number,
  start: string = ""
) {
  env.newMessage(
    `At ${start}[${index * -1}]: ${tokens.slice(0, 20).join(" ")}`
  );
}

// @end: when parsing local env, } is the end; when parsing source code, node is the end
export function parseNodes(
  env: L_Env,
  tokens: string[],
  end: string | null
): L_Node[] {
  try {
    const out: L_Node[] = [];

    if (end === null) {
      while (tokens.length !== 0) {
        const node = parseNodesFromSingleExpression(env, tokens);
        if (node !== undefined) out.push(...node);
      }
    } else {
      while (tokens[0] !== end) {
        const node = parseNodesFromSingleExpression(env, tokens);
        if (node !== undefined) out.push(...node);
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
  clear: specialParse,
  run: specialParse,
  macro: macroParse,
  def_composite: LetCompositeParse,
};

// The reason why the returned valued is L_Node[] is that when checking, there might be a list of facts.
export function parseNodesFromSingleExpression(
  env: L_Env,
  tokens: string[]
): L_Node[] | undefined {
  const start = tokens[0];
  const index = tokens.length;
  try {
    if (tokens.length === 0) return undefined;

    if (L_Ends.includes(tokens[0])) {
      tokens.shift();
      while (tokens.length > 0 && L_Ends.includes(tokens[0])) {
        tokens.shift();
      }
      if (tokens.length === 0) return undefined;
    }

    const func = KeywordFunctionMap[tokens[0]];
    if (func) {
      const node = func(env, tokens);
      return [node];
    } else {
      const postProve = factsArrParse(env, tokens, L_Ends, true);
      return postProve;
    }
  } catch (error) {
    handleParseError(env, tokens, "node", index, start);
    throw error;
  }
}

// function postfixProveParse(
//   env: L_Env,
//   tokens: string[],
//   end: string[] = [...L_Ends],
//   skipEnd: boolean = false
// ): L_Nodes.PostfixProve {
//   const start = tokens[0];
//   const index = tokens.length;

//   try {
//     const names: string[] = [];
//     if (isCurToken(tokens, "[")) {
//       skip(tokens, "[");
//       while (!isCurToken(tokens, "]")) {
//         names.push(shiftSymbol(tokens));
//         if (isCurToken(tokens, ",")) skip(tokens, ",");
//       }
//       skip(tokens, "]");
//     }

//     const facts = factsArrParse(
//       env,
//       tokens,
//       [...end, ...PostProveKeywords],
//       false
//     );
//     const block: L_Node[] = [];
//     if (PostProveKeywords.includes(tokens[0])) {
//       skip(tokens, PostProveKeywords);
//       skip(tokens, "{");
//       while (tokens[0] !== "}") {
//         while (["\n", ";"].includes(tokens[0])) {
//           tokens.shift();
//         }
//         if (tokens[0] === "}") break;

//         getNodesFromSingleNode(env, tokens, block);
//       }
//       skip(tokens, "}");
//     }

//     if (skipEnd) skip(tokens, end);

//     return new L_Nodes.PostfixProve(facts, block, names);
//   } catch (error) {
//     handleParseError(env, tokens, "fact", index, start);
//     throw error;
//   }
// }

function knowParse(env: L_Env, tokens: string[]): L_Nodes.KnowNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, KnowTypeKeywords);

    const names: string[] = [];

    let facts: ToCheckNode[] = [];
    // const strict = keyword === "know" ? false : true;

    // const knowNode: L_Nodes.KnowNode = new L_Nodes.KnowNode([], []);
    while (!L_Ends.includes(tokens[0])) {
      facts = factsArrParse(env, tokens, [...L_Ends, ","], false);
      // knowNode.facts = knowNode.facts.concat(outs);

      if (tokens[0] === ",") skip(tokens, ",");
    }
    skip(tokens, L_Ends);

    return new L_Nodes.KnowNode(facts, names);
    // return knowNode;
  } catch (error) {
    handleParseError(env, tokens, "know", index, start);
    throw error;
  }
}

function letParse(env: L_Env, tokens: string[]): L_Nodes.LetNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const whichLet = skip(tokens, LetKeywords) as string;

    const names: string[] = [];
    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
      while (!isCurToken(tokens, "]")) {
        names.push(shiftSymbol(tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }
      skip(tokens, "]");
    }

    const vars: string[] = [];
    while (![...L_Ends, , ":"].includes(tokens[0])) {
      vars.push(shiftSymbol(tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    if (vars.some((e) => L_Keywords.includes(e) || e.startsWith("\\"))) {
      env.newMessage(`Error: ${vars} contain LiTeX keywords.`);
      throw Error();
    }

    if (L_Ends.includes(tokens[0])) {
      skip(tokens, L_Ends);
      if (whichLet === LetKeyword) {
        return new L_Nodes.LetNode(vars, [], names);
      } else {
        throw Error();
      }
    } else {
      skip(tokens, ":");
      const facts = factsArrParse(env, tokens, L_Ends, true);
      if (whichLet === LetKeyword) {
        return new L_Nodes.LetNode(vars, facts, names);
      } else {
        throw Error();
      }
    }
  } catch (error) {
    handleParseError(env, tokens, "let", index, start);
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
      const curTok = shiftSymbol(tokens);
      out.push(curTok);
      if (isCurToken(tokens, separation)) skip(tokens, separation);
    }

    if (skipEnd) skip(tokens, end);

    return out;
  } catch (error) {
    handleParseError(env, tokens, "Parsing variables", index, start);
    throw error;
  }
}

function proveParse(env: L_Env, tokens: string[]): L_Nodes.ProveNode {
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

    const toProve = factParse(env, tokens);

    const block: L_Node[] = [];
    skip(tokens, "{");
    while (tokens[0] !== "}") {
      while (["\n", ";"].includes(tokens[0])) {
        tokens.shift();
      }
      if (tokens[0] === "}") break;

      const node = parseNodesFromSingleExpression(env, tokens);
      if (node !== undefined) block.push(node);
      else {
        throw Error();
      }
    }

    skip(tokens, "}");

    if (byContradict) {
      const contradict = optParse(env, tokens, true);
      skip(tokens, L_Ends);
      return new L_Nodes.ProveContradictNode(toProve, block, contradict);
    } else {
      return new L_Nodes.ProveNode(toProve, block);
    }
  } catch (error) {
    handleParseError(env, tokens, "Parsing prove", index, start);
    throw error;
  }
}

function factParse(env: L_Env, tokens: string[]): L_Nodes.ToCheckNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const factStart = tokens[0];
    const factIndex = tokens.length;

    try {
      let isT = true;
      if (isCurToken(tokens, "not")) {
        isT = false;
        skip(tokens, "not");
      }
      let out: L_Nodes.ToCheckNode;

      if (isBuiltinKeyword(tokens[0])) {
        const parser = L_BuiltinParsers.get(tokens[0]) as Function;
        out = parser(env, tokens);
        out.isT = isT;
      } else if (LogicalKeywords.includes(tokens[0])) {
        out = logicParse(env, tokens);
        out.isT = isT ? out.isT : !out.isT;
      } else {
        out = optParse(env, tokens, true);
        out.isT = isT;
      }

      return out;
    } catch (error) {
      handleParseError(env, tokens, "fact", factIndex, factStart);
      throw error;
    }
  } catch (error) {
    handleParseError(env, tokens, "fact", index, start);
    throw error;
  }
}

// Main Function of parser
function factsArrParse(
  env: L_Env,
  tokens: string[],
  end: string[],
  skipEnd: boolean
): ToCheckNode[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    let out: ToCheckNode[] = [];

    while (!end.includes(tokens[0])) {
      const cur = factParse(env, tokens);
      out.push(cur);
      // End of former singleNodeFacts logic

      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    if (skipEnd) skip(tokens, end);

    return out;
  } catch (error) {
    handleParseError(env, tokens, "facts", index, start);
    throw error;
  }
}

function optParse(env: L_Env, tokens: string[], parseNot: boolean): OptNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    // TODO use builtin to implement not
    let isT = true;

    // if (tokens[0] === ExistKeyword) {
    //   skip(tokens, ExistKeyword);

    //   return optsParse(env, tokens, parseNot) as ExistNode[];
    // } else
    if (tokens.length >= 2 && tokens[1] === "(") {
      //TODO CheckVars not implemented

      const optSymbol: L_OptSymbol = optSymbolParse(env, tokens);
      const vars = arrParse<L_Symbol>(env, tokens, symbolParse, "(", ")");

      let checkVars = checkVarsParse();

      return new OptNode(optSymbol, vars, isT, checkVars);
    } else {
      const var1 = symbolParse(env, tokens);

      switch (tokens[0]) {
        case "is": {
          skip(tokens, "is");
          const optName = skip(tokens);
          const optSymbol = new L_OptSymbol(optName);
          const checkVars = checkVarsParse();
          const out = new OptNode(optSymbol, [var1], isT, checkVars);
          return out;
        }
        default: {
          const optName = skip(tokens);
          const optSymbol = new L_OptSymbol(optName);
          const var2 = symbolParse(env, tokens);
          const checkVars = checkVarsParse();
          const out = new OptNode(optSymbol, [var1, var2], isT, checkVars);
          return out;
        }
      }
    }
  } catch (error) {
    handleParseError(
      env,
      tokens,
      `${start} is invalid operator.`,
      index,
      start
    );
    throw error;
  }

  function checkVarsParse(): L_Symbol[][] | undefined {
    if (isCurToken(tokens, "[")) {
      skip(tokens, "[");
      const checkVars: L_Symbol[][] = [];
      checkVars.push([]);
      while (!isCurToken(tokens, "]")) {
        checkVars[checkVars.length - 1].push(
          ...arrParse<L_Symbol>(
            env,
            tokens,
            symbolParse,
            undefined,
            [";", "]"],
            false
          )
        );
        if (isCurToken(tokens, ";")) {
          checkVars.push([]);
          skip(tokens, ";");
        }
      }
      skip(tokens, "]");
      return checkVars;
    } else {
      return undefined;
    }
  }
}

function logicParse(env: L_Env, tokens: string[]): LogicNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const type = skip(tokens, [IfKeyword, IffKeyword]);
    if (type === undefined) throw Error();
    const vars: L_Symbol[] = [];

    while (!isCurToken(tokens, [":", "{"])) {
      if (isCurToken(tokens, SlashKeyword)) {
        const s = compositeInIfReqParse(env, tokens);
        vars.push(s);
      } else {
        const singleton = singletonParse(env, tokens);
        vars.push(singleton);
      }
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }

    const req: ToCheckNode[] = [];
    if (isCurToken(tokens, ":")) {
      skip(tokens, ":");
      while (!isCurToken(tokens, "{")) {
        const facts = factsArrParse(env, tokens, [",", "{"], false);
        req.push(...facts);
        if (isCurToken(tokens, [","])) skip(tokens, [","]);
      }
    }

    skip(tokens, "{");

    const onlyIfs: ToCheckNode[] = [];
    while (!isCurToken(tokens, "}")) {
      // const facts = factsArrParse(env, tokens, [",", ";", "}"], false);
      const fact = factParse(env, tokens);
      onlyIfs.push(fact);
      if (isCurToken(tokens, [";", ","])) skip(tokens, [";", ","]);
    }
    skip(tokens, "}");

    if (type === IfKeyword) {
      return new L_Nodes.IfNode(vars, req, onlyIfs, true); //! By default isT = true
    } else if (type === IffKeyword) {
      return new L_Nodes.IffNode(vars, req, onlyIfs, true);
    } else {
      throw Error();
    }
  } catch (error) {
    handleParseError(env, tokens, "if-then", index, start);
    throw error;
  }
}

function localEnvParse(env: L_Env, tokens: string[]): L_Nodes.LocalEnvNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, "{");
    const nodes = parseNodes(env, tokens, "}");
    skip(tokens, "}");
    const out = new L_Nodes.LocalEnvNode(nodes);
    return out;
  } catch (error) {
    handleParseError(env, tokens, "{}", index, start);
    throw error;
  }
}

function haveParse(env: L_Env, tokens: string[]): L_Nodes.HaveNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, HaveKeywords);
    const vars: string[] = [];
    while (!isCurToken(tokens, ":")) {
      vars.push(shiftSymbol(tokens));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }
    skip(tokens, ":");

    const opts = factsArrParse(env, tokens, L_Ends, true) as OptNode[];

    return new L_Nodes.HaveNode(opts, vars);
  } catch (error) {
    handleParseError(env, tokens, "have", index, start);
    throw error;
  }
}

function specialParse(env: L_Env, tokens: string[]): L_Nodes.SpecialNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const keyword = shiftSymbol(tokens);
    switch (keyword) {
      case ClearKeyword:
        skip(tokens, L_Ends);
        return new L_Nodes.SpecialNode(ClearKeyword, null);
      case RunKeyword: {
        const words: string[] = [];
        while (!L_Ends.includes(tokens[0])) {
          words.push(shiftSymbol(tokens));
        }
        skip(tokens, L_Ends);
        return new L_Nodes.SpecialNode(RunKeyword, words.join());
      }
      default:
        throw Error();
    }
  } catch (error) {
    handleParseError(env, tokens, "clear", index, start);
    throw error;
  }
}

function macroParse(env: L_Env, tokens: string[]): L_Nodes.MacroNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, MacroKeywords);
    const regexString = skipString(tokens);
    const varName = shiftSymbol(tokens);
    const facts = factsArrParse(env, tokens, L_Ends, true);

    return new L_Nodes.MacroNode(regexString, varName, facts);
  } catch (error) {
    handleParseError(env, tokens, "macro", index, start);
    throw error;
  }
}

function defParse(env: L_Env, tokens: string[]): L_Nodes.DefNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, DefKeywords);

    const opt: OptNode = optParse(env, tokens, false);

    let cond: ToCheckNode[] = [];
    if (isCurToken(tokens, ":")) {
      skip(tokens, ":");
      cond = factsArrParse(env, tokens, L_Ends, false);
    }

    const onlyIfs: ToCheckNode[] = [];
    if (isCurToken(tokens, "{")) {
      skip(tokens, "{");
      onlyIfs.push(...factsArrParse(env, tokens, ["}"], false));
      skip(tokens, "}");
      return new L_Nodes.DefNode(opt, cond, onlyIfs);
    } else {
      skip(tokens, L_Ends);
      return new L_Nodes.DefNode(opt, cond, onlyIfs);
    }
  } catch (error) {
    handleParseError(env, tokens, "define", index, start);
    throw error;
  }
}

// --------------------------------------------------------
export function LetCompositeParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.DefCompositeNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Common.LetCompositeKeyword);
    const composite = compositeParse(env, tokens);
    if (isCurToken(tokens, L_Ends)) {
      skip(tokens, L_Ends);
      return new L_Nodes.DefCompositeNode(composite, []);
    }

    skip(tokens, ":");
    const facts: ToCheckNode[] = [];
    while (!isCurToken(tokens, L_Ends)) {
      facts.push(...factsArrParse(env, tokens, [",", ...L_Ends], false));
      if (isCurToken(tokens, ",")) skip(tokens, ",");
    }
    skip(tokens, L_Ends);

    return new L_Nodes.DefCompositeNode(composite, facts);
  } catch (error) {
    handleParseError(env, tokens, "define", index, start);
    throw error;
  }
}

export function isPropertyParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.BuiltinCheckNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Common.isFormKeyword);
    skip(tokens, "(");
    const name = skip(tokens);
    skip(tokens, ")");

    return new L_Nodes.IsPropertyNode(name, true);
  } catch (error) {
    handleParseError(env, tokens, "is_property", index, start);
    throw error;
  }
}
export function orParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.BuiltinCheckNode {
  throw Error();
}

export function isFormParse(
  env: L_Env,
  tokens: string[]
): L_Nodes.BuiltinCheckNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, L_Common.isFormKeyword);
    skip(tokens, "(");
    const given = symbolParse(env, tokens);
    skip(tokens, ",");
    const composite = compositeParse(env, tokens);

    if (isCurToken(tokens, ",")) {
      skip(tokens, ",");
      skip(tokens, "{");
      const facts: ToCheckNode[] = [];
      while (!isCurToken(tokens, "}")) {
        facts.push(factParse(env, tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }
      skip(tokens, "}");
      skip(tokens, ")");
      return new L_Nodes.IsFormNode(given, composite, facts, true);
    } else {
      skip(tokens, ")");
      return new L_Nodes.IsFormNode(given, composite, [], true);
    }
  } catch (error) {
    handleParseError(env, tokens, "is_property", index, start);
    throw error;
  }
}
