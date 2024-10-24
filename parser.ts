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
  ExistNode,
  HaveNode,
  AssumeByContraNode,
  OnlyIfDeclNode,
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
  ExistKeywords,
  HaveKeywords,
  AssumeByContraKeywords,
  OnlyIfKeywords,
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

  export function L_StmtsParse(env: L_Env, tokens: string[]): L_Node[] {
    try {
      const result: L_Node[] = [];
      while (tokens.length > 0) {
        while (tokens.length > 0 && ["\n", ";"].includes(tokens[0])) {
          tokens.shift();
        }
        if (tokens.length === 0) return result;

        result.push(NodeParse(env, tokens));
      }
      return result;
    } catch (error) {
      env.newMessage(`Error: Syntax Error.`);
      throw error;
    }
  }

  const KeywordFunctionMap: {
    [key: string]: Function; // (env: L_Env, tokens: string[]) => any;
  } = {
    // ";": (env: L_Env, tokens: string[]) => {
    //   tokens.shift();
    // },
    // "\n": (env: L_Env, tokens: string[]) => {
    //   tokens.shift();
    // },
    know: knowParse,
    "@": knowParse,
    // have: haveParse,
    let: letParse,
    def: DeclNodeParse,
    ":": DeclNodeParse,
    prove: proveParse,
    exist: existParse,
    have: haveParse,
    assume_by_contradiction: assumeByContraParse,
    // prove: proveParse,
    // by: byParse,
    // thm: thmParse,
  };

  export function NodeParse(env: L_Env, tokens: string[]): L_Node {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const func = KeywordFunctionMap[tokens[0]];
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
          out = shortCallOptParse(env, tokens);
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
    if: ifThenParse,
    "?": ifThenParse,
  };

  function factParse(env: L_Env, tokens: string[]): FactNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const relParser: Function | undefined = factParserSignals[tokens[0]];
      let out: FactNode;
      if (relParser === undefined) {
        out = shortCallOptParse(env, tokens);
      } else {
        out = relParser(env, tokens);
      }

      if (isCurToken(tokens, "by")) {
        skip(tokens, "by");
        skip(tokens, "{");
        const bys = listParse<FactNode>(env, tokens, factParse, ["}"]);
        return new ByNode([out], bys);
      }

      return out;
    } catch (error) {
      handleParseError(env, "fact", index, start);
      throw error;
    }
  }

  // parse p1:p2:p3(x1,x2:x3:x4,x5,x6)
  function shortCallOptParse(env: L_Env, tokens: string[]): ShortCallOptNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      let nameAsParam: string = shiftVar(tokens);

      const vars: string[] = [];
      skip(tokens, "(");

      const curParams: string[] = [];
      while (!isCurToken(tokens, ")")) {
        vars.push(shiftVar(tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }

      skip(tokens, ")");

      return new ShortCallOptNode(nameAsParam, vars);
    } catch (error) {
      handleParseError(env, `${start} is invalid operator.`, index, start);
      throw error;
    }
  }

  // At parsing stage, not is "executed"
  function notParse(env: L_Env, tokens: string[]): FactNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, "not");
      const fact = factParse(env, tokens);
      fact.isT = false;
      return fact;
    } catch (error) {
      handleParseError(env, "not", index, start);
      throw error;
    }
  }

  function orParse(env: L_Env, tokens: string[]): OrNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, "or");

      skip(tokens, "{");

      const facts: FactNode[] = [];
      while (!isCurToken(tokens, "}")) {
        facts.push(factParse(env, tokens));
        if (isCurToken(tokens, ",")) skip(tokens, ",");
      }

      skip(tokens, "}");
      return new OrNode(facts);
    } catch (error) {
      handleParseError(env, "or", index, start);
      throw error;
    }
  }

  function ifThenParse(
    env: L_Env,
    tokens: string[],
    ends: string[] = StdStmtEnds,
    skipEnd = true
  ): IfThenNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, IfKeywords);

      const vars = varLstParse(env, tokens, ["|", ...ThenKeywords], false);

      let req: FactNode[] = [];
      if (ThenKeywords.includes(tokens[0])) {
        skip(tokens, ThenKeywords);
      } else {
        skip(tokens, "|");
        req = listParse<FactNode>(env, tokens, factParse, ["=>", "then"], true);
      }

      let onlyIfs: ShortCallOptNode[];

      const facts = listParse<FactNode>(env, tokens, factParse, ends, skipEnd);
      if (facts.every((e) => e instanceof ShortCallOptNode)) {
        onlyIfs = facts as ShortCallOptNode[];
      } else {
        throw Error(`Not all onlyIfs are operator-type fact.`);
      }

      const out = new IfThenNode(vars, req, onlyIfs);
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
    separation: string = ","
  ): T[] {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const out: T[] = [];
      while (!end.includes(tokens[0])) {
        out.push(parseFunc(env, tokens));
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
    separation: string = ","
  ): string[] {
    const start = tokens[0];
    const index = tokens.length;

    try {
      const out: string[] = [];
      while (!end.includes(tokens[0])) {
        let curTok = shiftVar(tokens);
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

      if ([...IfKeywords, ...OnlyIfKeywords].includes(tokens[0])) {
        nodeType = shiftVar(tokens);
      }

      const vars = varLstParse(env, tokens, ["|"], true);

      // if (StdStmtEnds.includes(tokens[0])) {
      //   skip(tokens, StdStmtEnds);
      //   return new DefDeclNode(name, vars);
      // } else {
      //   skip(tokens, "|");
      // }

      const req = listParse<FactNode>(
        env,
        tokens,
        factParse,
        [...StdStmtEnds, "=>"],
        false
      );

      let onlyIfs: ShortCallOptNode[] = [];
      if (StdStmtEnds.includes(tokens[0])) {
        skip(tokens, StdStmtEnds);
      } else if (isCurToken(tokens, "=>")) {
        skip(tokens, "=>");

        onlyIfs = listParse<ShortCallOptNode>(
          env,
          tokens,
          shortCallOptParse,
          StdStmtEnds,
          true
        );
      }

      if (IfKeywords.includes(nodeType)) {
        return new IfThenDeclNode(name, vars, req, onlyIfs);
      } else if (DefKeywords.includes(nodeType)) {
        return new DefDeclNode(name, vars, req, onlyIfs);
      } else if (OnlyIfKeywords.includes(nodeType)) {
        return new OnlyIfDeclNode(name, vars, req, onlyIfs);
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

      let toProve: null | IfThenNode = null;
      let fixedIfThenOpt: null | ShortCallOptNode = null;

      if (IfKeywords.includes(tokens[0])) {
        toProve = ifThenParse(env, tokens, ["{"], false);
      } else {
        fixedIfThenOpt = shortCallOptParse(env, tokens);
      }

      const block: L_Node[] = [];
      skip(tokens, "{");
      while (tokens[0] !== "}") {
        while (["\n", ";"].includes(tokens[0])) {
          tokens.shift();
        }
        if (tokens[0] === "}") continue;

        block.push(NodeParse(env, tokens));
      }

      skip(tokens, "}");

      if (toProve !== null) {
        return new ProveNode(toProve, null, block);
      } else {
        return new ProveNode(null, fixedIfThenOpt, block);
      }
    } catch (error) {
      handleParseError(env, "Parsing prove", index, start);
      throw error;
    }
  }

  function existParse(env: L_Env, tokens: string[]): ExistNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, ExistKeywords);
      const name = shiftVar(tokens);
      const vars = varLstParse(env, tokens, ["|", ...StdStmtEnds], false);

      if (StdStmtEnds.includes(tokens[0])) {
        skip(tokens, StdStmtEnds);
        return new ExistNode(name, vars, []);
      } else {
        skip(tokens, "|");
      }

      const req = listParse<FactNode>(
        env,
        tokens,
        factParse,
        [...StdStmtEnds],
        true
      );

      return new ExistNode(name, vars, req);
    } catch (error) {
      handleParseError(env, "Exist prove", index, start);
      throw error;
    }
  }

  function haveParse(env: L_Env, tokens: string[]): HaveNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, HaveKeywords);
      const vars = listParse<string>(
        env,
        tokens,
        (env, e) => shiftVar(e),
        [...StdStmtEnds, "|"],
        false
      );

      if (StdStmtEnds.includes(tokens[0])) {
        skip(tokens, StdStmtEnds);
        return new HaveNode(vars, []);
      } else {
        skip(tokens, "|");
        const facts = listParse<FactNode>(
          env,
          tokens,
          factParse,
          StdStmtEnds,
          true
        );
        return new HaveNode(vars, facts);
      }
    } catch (error) {
      handleParseError(env, "have", index, start);
      throw error;
    }
  }

  function assumeByContraParse(
    env: L_Env,
    tokens: string[]
  ): AssumeByContraNode {
    const start = tokens[0];
    const index = tokens.length;

    try {
      skip(tokens, AssumeByContraKeywords);
      const assume = factParse(env, tokens);
      skip(tokens, "{");
      const block: L_Node[] = [];
      while (!isCurToken(tokens, "}")) {
        block.push(NodeParse(env, tokens));
      }
      skip(tokens, "}");
      skip(tokens, "{");
      const contradict = factParse(env, tokens);
      skip(tokens, "}");
      return new AssumeByContraNode(assume, block, contradict);
    } catch (error) {
      handleParseError(env, "assume_by_contradiction", index, start);
      throw error;
    }
  }
}
