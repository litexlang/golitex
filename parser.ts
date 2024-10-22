import {
  KnowNode,
  L_Node,
  LetNode,
  OrNode,
  ShortCallOptNode,
  IfThenNode,
  DeclNode,
  DefDeclNode,
  IfThenDeclNode,
  FactNode,
  ByNode,
  ProveNode,
} from "./ast";
import { L_Env } from "./env";
import {
  KnowTypeKeywords,
  specialChars,
  StdStmtEnds,
  IfKeywords,
  DefKeywords,
  LetKeywords,
  ThenKeywords,
  ProveKeywords,
} from "./common";

export namespace parser {
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
        result.push(NodeParse(env, tokens));
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
    prove: proveParse,
    // exist: existParse,
    // prove: proveParse,
    // by: byParse,
    // thm: thmParse,
  };

  export function NodeParse(env: L_Env, tokens: string[]): L_Node {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const func = KeywordFunctionMap[tokens[0]];
      const funcName = tokens[0];
      if (func) {
        const node = func(env, tokens);
        return node;
      } else {
        const node = factParse(env, tokens);
        skip(tokens, [",", ";"]);
        return node;
      }
    } catch (error) {
      handleParseError(env, "node", index, start);
      throw error;
    }
  }

  // export function LiTexStmtParse(
  //   env: L_Env,
  //   tokens: string[],
  //   putInto: L_Node[]
  // ) {
  //   const start = tokens[0];
  //   const index = tokens.length;

  //   try {
  //     if (func) {
  //       const node = func(env, tokens);
  //       if (KnowTypeKeywords.includes(funcName)) {
  //         skip(tokens, StdStmtEnds);
  //       }
  //       if (node) {
  //         putInto.push(node);
  //       } else {
  //         return;
  //       }
  //     } else {
  //       callOptsParse(env, tokens, putInto);
  //       return;
  //     }
  //   } catch (error) {
  //     handleParseError(env, "Stmt", index, start);
  //     throw error;
  //   }
  // }

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
        skip(tokens, "by");
        skip(tokens, "{");
        const bys = listParse<FactNode>(env, tokens, factParse, ["}"]);
        return new ByNode(out, bys);
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
          if (addHash && env.varsAreNotDeclared(curTok)) {
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
        if (addHash && env.varsAreNotDeclared(curTok)) {
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

      if (IfKeywords.includes(tokens[0])) {
        nodeType = shiftVar(tokens);
      }

      const vars = varLstParse(env, tokens, ["|", ...StdStmtEnds], false, true);

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

      if (IfKeywords.includes(nodeType)) {
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

  function proveParse(env: L_Env, tokens: string[]): ProveNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, ProveKeywords);

      const toProve = yaIfThenParse(env, tokens, false);

      skip(tokens, "{");

      const nodes = listParse<L_Node>(env, tokens, NodeParse, ["}"]);

      // TODO Unfold FactsNode

      return new ProveNode(toProve, nodes);
    } catch (error) {
      handleParseError(env, "Parsing prove", index, start);
      throw error;
    }
  }
}
