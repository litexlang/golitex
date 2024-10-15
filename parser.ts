import {
  FactNode,
  // CallOptsNode,
  InferNode,
  ExistNode,
  KnowNode,
  L_Node,
  LetNode,
  DefNode,
  TNode,
  DollarMarkNode,
  ProveNode,
  HaveNode,
  ByNode,
  ThmNode,
} from "./ast";
import { L_Env } from "./env";
import {
  KnowTypeKeywords,
  TemplateDeclarationKeywords,
  specialChars,
  DefBlockDeclareAndCall,
  SymbolsFactsSeparator,
  ProveKeywords,
  redefineTemplateDeclarationKeywords,
  suchThats,
  byLBracket,
  byRBracket,
  StdStmtEnds,
} from "./common";
import { on } from "events";

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

function isCurToken(s: string, tokens: string[]) {
  return s === tokens[0];
}

function handleParseError(
  // tokens: string[],
  env: L_Env,
  m: string,
  index: number,
  start: string = "",
  addErrorDepth: Boolean = true
) {
  const errorIndex = index;
  env.newMessage(`At ${start}[${errorIndex * -1}]: ${m}`, addErrorDepth);
}

const KeywordFunctionMap: {
  [key: string]: Function; // (env: L_Env, tokens: string[]) => any;
} = {
  ";": (env: L_Env, tokens: string[]) => {
    tokens.shift();
  },
  "(": reqOnlyIfFactParse,
  "\n": (env: L_Env, tokens: string[]) => {
    tokens.shift();
  },
  know: knowParse,
  "@": knowParse,
  have: haveParse,
  // not: notParse,
  // or: orParse,
  let: letParse,
  def: templateParse,
  re_def: templateParse,
  ":": templateParse,
  exist: existParse,
  "?": templateParse,
  know_everything: (env: L_Env, tokens: string[]) => {
    const node = knowParse(env, tokens);
    node.isKnowEverything = true;
    return node;
  },
  "!": (env: L_Env, tokens: string[]) => {
    const node = knowParse(env, tokens);
    node.isKnowEverything = true;
    return node;
  },
  prove: yaProveParse,
  "&": yaProveParse,
  by: byParse,
  thm: thmParse,
};

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
      let node: L_Node;
      switch (tokens[0]) {
        case ":":
        case "def":
          node = templateParse(env, tokens);
          knowNode.facts.push(node as TNode);
          break;
        default:
          node = callOptParse(env, tokens, true, true);
          knowNode.facts.push(node as FactNode);
      }

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
function freeVarsAndTheirFactsParse(
  env: L_Env,
  tokens: string[],
  begin: string = "(",
  end: string[] = [")"],
  optWithReqAndOnlyIf: Boolean = false
): { freeVars: string[]; properties: FactNode[] } {
  const requirements: FactNode[] = [];
  const freeVars: string[] = [];

  skip(tokens, begin);

  if (!end.includes(tokens[0])) {
    while (1) {
      const freeVar = tokens.shift() as string;
      freeVars.push(freeVar);
      if (tokens[0] === ",") tokens.shift();
      else if (tokens[0] === SymbolsFactsSeparator) break;
      else if (end.includes(tokens[0])) break;
      else throw Error("infer parameters");
    }
    if (!end.includes(tokens[0])) {
      skip(tokens, SymbolsFactsSeparator);
      while (!end.includes(tokens[0])) {
        let node: FactNode;
        if (optWithReqAndOnlyIf) node = callOptParse(env, tokens, true, true);
        else node = callOptParse(env, tokens);
        if (node) requirements.push(node as FactNode);

        if (tokens[0] === ",") tokens.shift();
        if (end.includes(tokens[0])) break;
      }
    }
  }

  skip(tokens, end);

  return { freeVars: freeVars, properties: requirements };
}

function questionMarkParse(env: L_Env, tokens: string[]): DollarMarkNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, DefBlockDeclareAndCall);
    tokens.unshift(":");
    const template = templateParse(env, tokens);
    return new DollarMarkNode(template);
  } catch (error) {
    handleParseError(env, "?", index, start);
    throw error;
  }
}

function blockParse(env: L_Env, tokens: string[]): L_Node[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const result: L_Node[] = [];
    skip(tokens, "{"); // skip {

    while (!isCurToken("}", tokens)) {
      if (isCurToken(DefBlockDeclareAndCall, tokens)) {
        const node = questionMarkParse(env, tokens);
        if (node) result.push(node);
        continue;
      } else LiTexStmtParse(env, tokens, result);
    }

    skip(tokens, "}"); // skip }

    return result;
  } catch (error) {
    handleParseError(env, "{}", index, start);
    throw error;
  }
}

function callOptParse(
  env: L_Env,
  tokens: string[],
  // the followings all false means vanilla callOpt
  withReq: Boolean = false,
  withOnlyIf: Boolean = false,
  withByName: Boolean = false
): FactNode {
  const index = tokens.length;
  const start = tokens[0];

  try {
    const opts: [string, string[]][] = [];
    const requirements: FactNode[][] = [];

    /**
     * There are 2 ways to parse here
     * 1. fun(X):fun2(Y)..
     * 2. X:Y.. is fun:fun2
     */
    if (tokens.length >= 1 && tokens[1] === "(") {
      while (1) {
        const name = shiftVar(tokens) as string;

        if (!withReq) {
          const params: string[] = [];

          skip(tokens, "(");
          if (!isCurToken(")", tokens)) {
            while (1) {
              params.push(shiftVar(tokens));
              if (isCurToken(",", tokens)) skip(tokens, ",");
              else if (isCurToken(")", tokens)) {
                skip(tokens, ")");
                break;
              } else throw Error("");
            }
          } else {
            skip(tokens, ")");
          }

          opts.push([name, params]);
        } else {
          const freeVarsAndFacts = freeVarsAndTheirFactsParse(env, tokens);
          opts.push([name, freeVarsAndFacts.freeVars]);
          requirements.push(freeVarsAndFacts.properties);
        }

        if (isCurToken(":", tokens)) {
          skip(tokens, ":");
        } else {
          break;
        }
      }
    } else {
      // suchThat version of callOpt only works when !withReq
      let n = 0;
      const vars: string[][] = [[]];
      const optNames: string[] = [];

      if (!withReq) {
        while (!suchThats.includes(tokens[0])) {
          vars[n].push(shiftVar(tokens));
          if (isCurToken(",", tokens)) skip(tokens, ",");
          else if (isCurToken(":", tokens)) {
            skip(tokens, ":");
            vars.push([]);
            n++;
          }
        }
      }
      skip(tokens, suchThats);

      optNames.push(shiftVar(tokens));
      for (let i = 1; i < n + 1; i++) {
        skip(tokens, ":");
        optNames.push(shiftVar(tokens));
      }

      vars.forEach((v, i) => opts.push([optNames[i], v]));
    }

    let out: FactNode;
    if (!withOnlyIf || !isCurToken("=>", tokens))
      out = new FactNode(opts, requirements);
    else {
      skip(tokens, "=>");
      skip(tokens, "{");

      const onlyIfs: FactNode[] = [];
      callOptsParse(env, tokens, onlyIfs, ["}"]);

      out = new FactNode(opts, requirements, onlyIfs);
    }

    if (!withByName) return out;
    else {
      if (!isCurToken("[", tokens)) return out;
      else {
        skip(tokens, "[");
        out.byName = shiftVar(tokens);
        skip(tokens, "]");
        return out;
      }
    }
  } catch (error) {
    handleParseError(env, "operator", index, start);
    throw error;
  }
}

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
      callOpts.push(callOptParse(env, tokens));
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

function templateParse(env: L_Env, tokens: string[]): TNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const defName = skip(tokens, TemplateDeclarationKeywords);
    const name = shiftVar(tokens);

    const freeVarsFact: { freeVars: string[]; properties: FactNode[] } =
      freeVarsAndTheirFactsParse(env, tokens);

    // skip(tokens, ")");

    let result: L_Node;
    switch (tokens[0]) {
      case "=>":
        skip(tokens, "=>");
        if (!isCurToken("{", tokens)) {
          result = new InferNode(
            name,
            freeVarsFact.freeVars,
            freeVarsFact.properties
          );
          const facts: FactNode[] = [];
          callOptsParse(env, tokens, facts);
          for (let i = 0; i < facts.length; i++) {
            (result as InferNode).onlyIfs.push(facts[i]);
          }
        } else {
          const blockArrow = blockParse(env, tokens);
          result = new InferNode(
            name,
            freeVarsFact.freeVars,
            freeVarsFact.properties
          );
          (result as InferNode).onlyIfs = blockArrow;
        }

        break;

      case "{":
        const blockBrace = blockParse(env, tokens);
        result = new InferNode(
          name,
          freeVarsFact.freeVars,
          freeVarsFact.properties
        );
        (result as DefNode).onlyIfs = blockBrace;
        break;

      case "<=>":
        skip(tokens, "<=>");
        if (!isCurToken("{", tokens)) {
          result = new DefNode(
            name,
            freeVarsFact.freeVars,
            freeVarsFact.properties
          );
          callOptsParse(env, tokens, (result as DefNode).onlyIfs);
        } else {
          const blockDoubleArrow = blockParse(env, tokens);
          result = new DefNode(
            name,
            freeVarsFact.freeVars,
            freeVarsFact.properties
          );
          (result as DefNode).onlyIfs = blockDoubleArrow;
        }

        break;

      default:
        // no arrow, no block
        result = new DefNode(name, freeVarsFact.freeVars, []);
        (result as TNode).requirements = freeVarsFact.properties;
        break;
    }

    if (redefineTemplateDeclarationKeywords.includes(defName as string)) {
      (result as TNode).isRedefine = true;
    }
    return result as TNode;
  } catch (error) {
    handleParseError(env, "declare template", index, start);
    // env.returnToSnapShot(snapShot);
    throw error;
  }
}

function letParse(env: L_Env, tokens: string[]): LetNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    return new LetNode(
      freeVarsAndTheirFactsParse(env, tokens, "let", StdStmtEnds, true)
    );
  } catch (error) {
    handleParseError(env, "let", index, start);
    throw error;
  }
}

function yaProveParse(env: L_Env, tokens: string[]): ProveNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, ProveKeywords);
    let name = "";
    if (isCurToken(byLBracket, tokens)) {
      skip(tokens, byLBracket);
      name = shiftVar(tokens);
      skip(tokens, byRBracket);
    }
    const relatedOpt = callOptParse(env, tokens, true, true);
    const blockBrace = blockParse(env, tokens);
    const result = new ProveNode(relatedOpt, blockBrace, name);
    return result;
  } catch (error) {
    handleParseError(env, "prove", index, start);
    throw error;
  }
}

function existParse(env: L_Env, tokens: string[]): ExistNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    /** Copy code from templateParse */
    skip(tokens, "exist") as string; // KnowTypeKeywords

    const name = shiftVar(tokens);

    const freeVarsFact: { freeVars: string[]; properties: FactNode[] } =
      freeVarsAndTheirFactsParse(env, tokens);

    let result: ExistNode;

    result = new ExistNode(
      name,
      freeVarsFact.freeVars,
      freeVarsFact.properties
    );

    return result;
  } catch (error) {
    handleParseError(env, "exist", index, start);
    throw error;
  }
}

function haveParse(env: L_Env, tokens: string[]): HaveNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, "have");

    const vars: string[] = [];
    while (!isCurToken(SymbolsFactsSeparator, tokens)) {
      vars.push(shiftVar(tokens));
      if (isCurToken(",", tokens)) skip(tokens, ",");
    }
    skip(tokens, SymbolsFactsSeparator);

    const opt = callOptParse(env, tokens, false, false);

    skip(tokens, StdStmtEnds);

    return new HaveNode(vars, opt);
  } catch (error) {
    handleParseError(env, "have", index, start);
    throw error;
  }
}

function byParse(env: L_Env, tokens: string[]): ByNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, "by");

    const name = shiftVar(tokens);
    const opt = callOptParse(env, tokens);

    skip(tokens, StdStmtEnds);
    return new ByNode(name, opt);
  } catch (error) {
    handleParseError(env, "by", index, start);
    throw error;
  }
}

function thmParse(env: L_Env, tokens: string[]): ThmNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, "thm");

    const opt = callOptParse(env, tokens, true, true);

    // opt.optName should not have ':'
    if (opt.optNameAsLst.length > 1 || opt.optParams.length > 1) {
      handleParseError(
        env,
        `operator in thm should not have concatenated name ${opt.optName}`,
        index,
        start
      );
    }

    const block = blockParse(env, tokens);

    return new ThmNode(opt, block);
  } catch (error) {
    handleParseError(env, "thm", index, start);
    throw error;
  }
}

// all facts here are vanilla, which means they are of form opt(...)
function reqOnlyIfFactParse(env: L_Env, tokens: string[]): FactNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const req: FactNode[] = [];
    skip(tokens, "(");
    while (!isCurToken(")", tokens)) {
      req.push(callOptParse(env, tokens, false, false));
      if (isCurToken(",", tokens)) skip(tokens, ",");
    }
    skip(tokens, ")");

    skip(tokens, "=>");
    skip(tokens, "{");

    const onlyIf: FactNode[] = [];
    while (!isCurToken("}", tokens)) {
      onlyIf.push(callOptParse(env, tokens, false, false));
      if (isCurToken(",", tokens)) skip(tokens, ",");
    }

    skip(tokens, "}");

    return new FactNode([], [req], onlyIf);
  } catch (error) {
    handleParseError(env, "fact", index, start);
    throw error;
  }
}
