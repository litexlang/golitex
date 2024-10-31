import {
  KnowNode,
  L_Node,
  LetNode,
  OptNode,
  IfThenNode,
  FactNode,
  DeclNode,
  IfThenDeclNode,
  ProveNode,
  HaveNode,
  AssumeByContraNode,
  ByNode,
} from "./ast";
import { L_Env } from "./L_Env";
import { checker } from "./L_Checker";
import { L_Storage } from "./L_Storage";

export enum RType {
  Error,
  True, // not only used as True for callInferExec, but also as a generic type passed between subFunctions.
  KnowUndeclared,
  False,
  Unknown,
  HaveFailed,
  ProveFailed,
  ThmFailed,
}

export const RTypeMap: { [key in RType]: string } = {
  [RType.Error]: "error",
  [RType.False]: "check: false",
  [RType.True]: "check: true",
  [RType.Unknown]: "check: unknown",
  [RType.KnowUndeclared]: "know: undeclared opt",
  [RType.HaveFailed]: "have: failed",
  [RType.ProveFailed]: "prove: failed",
  [RType.ThmFailed]: "thm: failed",
};

function handleExecError(env: L_Env, out: RType, m: string = "") {
  env.newMessage(m);
  return out;
}

/**
 * Guideline of what execute functions do
 * 1. return RType thing
 * 2. env.newMessage()
 */
export namespace L_Executor {
  const nodeExecMap: { [key: string]: (env: L_Env, node: any) => RType } = {
    IffDeclNode: declExec,
    IfThenDeclNode: declExec,
    ExistNode: declExec,
    OnlyIfDeclNode: declExec,
    KnowNode: knowExec,
    LetNode: letExec,
    ProveNode: proveExec,
    HaveNode: haveExec,
    AssumeByContraNode: assumeByContraExec,
    ByNode: _byExec,
  };

  export function nodeExec(env: L_Env, node: L_Node): RType {
    try {
      const nodeType = node.constructor.name;
      const execFunc = nodeExecMap[nodeType];

      if (execFunc && execFunc(env, node) === RType.True)
        return successMesIntoEnv(env, node);
      else if (node instanceof FactNode) {
        try {
          // const out = factExec(env, node as FactNode);
          // return out;

          const out = factExec(env, node as FactNode);
          // const out = yaFactExec(env, node as FactNode);
          if (out === RType.True) {
            env.newMessage(`OK! ${node}`);
          } else if (out === RType.Unknown) {
            env.newMessage(`Unknown ${node}`);
          } else if (out === RType.Error) {
            env.newMessage(`Error ${node}`);
          }
          return out;
        } catch (error) {
          throw Error(`${node as FactNode}`);
        }
      }
      return RType.Error;
    } catch (error) {
      if (error instanceof Error) env.newMessage(`Error: ${error.message}`);
      return RType.Error;
    }
  }

  function successMesIntoEnv(env: L_Env, node: L_Node): RType {
    env.newMessage(`OK! ${node.toString()}`);
    return RType.True;
  }

  function haveExec(env: L_Env, node: HaveNode): RType {
    try {
      // Check duplicate variable declarations
      node.vars.forEach((e) => env.newVar(e, e));

      for (const fact of node.facts) {
        if (fact instanceof OptNode) {
          //! TODO checker.checkOptInHave now returns RType.Unknown
          const out = checker.checkOptInHave(env, fact);
          if (out !== RType.True) {
            env.newMessage(`Unknown: ${node.toString()}`);
            return out;
          }
        } else {
          //! For the time being, if-then can not be checked when have
          env.newMessage(`Error: ${node.toString()}`);
          return RType.Error;
        }
      }

      knowExec(env, new KnowNode(node.facts));

      return RType.True;
    } catch (error) {
      env.newMessage(`Error: ${node.toString()}`);
      return RType.Error;
    }
  }

  function letExec(env: L_Env, node: LetNode): RType {
    try {
      // ya ya: put new vars into env
      node.vars.forEach((e) => env.newVar(e, e));

      // Check duplicate variable declarations
      // const noErr = env.declareNewVar(node.vars);
      // if (!noErr) {
      //   env.newMessage(
      //     `Error: Variable(s) ${node.vars.join(", ")} already declared in this scope.`
      //   );
      //   return RType.Error;
      // }

      knowExec(env, new KnowNode(node.facts));

      return RType.True;
    } catch (error) {
      env.newMessage(`Error: ${node.toString()}`);
      return RType.Error;
    }
  }

  /**
   * Main Function of whole project. Not only used at assume expression, other expressions which introduces new fact into environment calls this function.
   *
   * know Opt: store directly
   * know if-then: if then is Opt, store it bound with if as req; if then is if-then, inherit father req and do knowExec again.
   */
  //! This one of the functions in which new facts are generated.
  //! In order to unify interface, after checking a fact, we use KnowExec to emit new fact
  export function knowExec(env: L_Env, node: KnowNode | FactNode): RType {
    try {
      if (node instanceof FactNode) {
      } else if (node instanceof KnowNode) {
        for (const fact of node.facts) {
          L_Storage.L_Store(env, fact, []);
        }
      }

      return RType.True;
    } catch (error) {
      let m = `'${node.toString()}'`;
      if (error instanceof Error) m += ` ${error.message}`;
      env.newMessage(m);
      throw error;
    }
  }

  function declExec(env: L_Env, node: DeclNode): RType {
    try {
      if (env.isOptDeclared(node.name)) {
        throw Error(`${node.name} already declared.`);
      }

      env.setDeclFact(node.name, node);

      // new new storage system
      L_Storage.declNewFact(env, node);
      // L_Storage;

      return RType.True;
    } catch (error) {
      let m = `'${node.toString()}'`;
      if (error instanceof Error) m += ` ${error.message}`;
      env.newMessage(m);
      throw error;
    }
  }

  function proveExec(env: L_Env, node: ProveNode): RType {
    return RType.True;
  }

  /**
   * Steps
   * 1. open new Env
   * 2. assume node.assume
   * 3. run block
   * 4. check node.contradict, not node.contradict
   * 5. emit the reverse of node.assume
   */
  function assumeByContraExec(env: L_Env, node: AssumeByContraNode): RType {
    try {
      const newEnv = new L_Env(env);
      knowExec(newEnv, new KnowNode([node.assume]));
      for (const subNode of node.block) {
        const out = nodeExec(newEnv, subNode);
        if (out !== RType.True) {
          return handleExecError(
            env,
            out,
            `Proof Block Expression ${subNode} Failed.`
          );
        }
      }

      let out = checker.L_Check(newEnv, node.contradict);
      //! TODO
      // if (!(out.type === RType.True)) {
      //   return handleExecError(
      //     env,
      //     out.type,
      //     `assume_by_contradiction failed to prove ${node.contradict}. Proof by contradiction requires checking both the statement and its negation.`
      //   );
      // }

      node.contradict.isT = !node.contradict.isT;
      out = checker.L_Check(newEnv, node.contradict);
      //! TODO
      // if (!(out.type === RType.True)) {
      //   return handleExecError(
      //     env,
      //     out.type,
      //     `assume_by_contradiction failed to prove ${node.contradict}. Proof by contradiction requires checking both the statement and its negation.`
      //   );
      // }

      node.assume.isT = !node.assume.isT;
      knowExec(env, new KnowNode([node.assume]));
      return RType.True;
    } catch (error) {
      env.newMessage(`${node}`);
      return RType.Error;
    }
  }

  function _byExec(env: L_Env, node: ByNode): RType {
    const newEnv = new L_Env(env);
    for (const subNode of node.block) {
      const out = nodeExec(newEnv, subNode);
      if (out !== RType.True) return out;
    }
    for (const fact of node.facts) {
      const out = nodeExec(newEnv, fact);
      if (out !== RType.True) return out;
    }
    knowExec(env, new KnowNode(node.facts));
    return RType.True;
  }

  function factExec(env: L_Env, toCheck: FactNode): RType {
    try {
      let out = checker.L_Check(env, toCheck);
      if (out === RType.True) {
        L_Storage.L_Store(env, toCheck, []);
      }
      return out;
    } catch (error) {
      env.newMessage(`failed to check ${toCheck}`);
      return RType.Error;
    }
  }
}
