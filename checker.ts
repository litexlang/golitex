import { fail } from "assert";
import {
  FactNode,
  IffNode,
  IfThenNode,
  KnowNode,
  L_Node,
  OnlyIfNode,
  OptNode,
} from "./ast";
import { L_Env, StoredFactValue } from "./env";
import { executor, RType } from "./executor";
import { L_Storage } from "./L_Storage";
export class CheckerOut {
  constructor(
    public type: RType,
    public checkedByOpt: Boolean = false
  ) {}
}

function checkAndMsg(env: L_Env, r: RType, n: L_Node): Boolean {
  if (r === RType.Unknown) env.newMessage(`Unknown ${n}`);
  if (r === RType.Error) env.newMessage(`Error ${n}`);
  return r === RType.True;
}

export namespace checker {
  export function check(env: L_Env, node: FactNode): CheckerOut {
    if (node instanceof OptNode) {
      const out = checkOpt(env, node);
      return out;
    } else if (node instanceof IfThenNode) {
      const out = checkLogicalOpt(env, node.vars, node.req, node.onlyIfs);
      return new CheckerOut(out);
    } else if (node instanceof IffNode) {
      let out = checkLogicalOpt(env, node.vars, node.req, node.onlyIfs);
      if (!(out === RType.True)) return new CheckerOut(out);
      out = checkLogicalOpt(env, node.vars, node.onlyIfs, node.req);
      return new CheckerOut(out);
    } else if (node instanceof OnlyIfNode) {
      const out = checkLogicalOpt(env, node.vars, node.onlyIfs, node.req);
      return new CheckerOut(out);
    }

    return new CheckerOut(RType.Error);
  }

  /**
   * Main function of checker
   * @param env the environment we are working at
   * @param opt the fact (OptFact) we wanna prove
   * @param ignore  which fact (Opt) to ignore in order to avoid "req => itself, itself => req"-kind loop
   * @returns RType Error, True, False
   */
  export function checkOpt(env: L_Env, opt: OptNode): CheckerOut {
    // get related fact from itself and its ancestors
    const facts: StoredFactValue[] | undefined = env.getOptFact(opt.fullName);
    if (facts === undefined) {
      if (env.getDeclFact(opt.fullName)) {
        return new CheckerOut(RType.Unknown);
      } else {
        env.newMessage(`${opt.fullName} not declared.`);
        return new CheckerOut(RType.Error);
      }
    }

    const varsNotDeclared = env.varsAreNotDeclared(opt.vars);
    if (varsNotDeclared) {
      env.newMessage(`Not all of ${opt.vars} are declared.`);
      return new CheckerOut(RType.Error);
    }

    for (const storedFact of facts) {
      /**
       * Main Logic of Checking Steps:
       * 1. literally correct and stored.isT === opt.isT
       * 2. req correct
       * 2.1 locally correct
       * 2.2 correctness is given by father
       */
      if (
        storedFact.isT === opt.isT &&
        storedFact.vars.every((s, j) => checkSingleVar(s, opt.vars[j]))
      ) {
        /**
         * check current opt by replacing potential hashed var with current var
         */
        //! I think the following fixing is buggy
        const freeToFixMap = new Map<string, string>();
        storedFact.vars.forEach((s, j) => freeToFixMap.set(s, opt.vars[j]));

        if (
          storedFact.req.every((e) => {
            let out: RType = RType.Error;
            if (e instanceof OptNode) {
              out = checkByFactsWithNoReq(env, fixFree(e, freeToFixMap));
            } else if (e instanceof IfThenNode) {
              out = checkLogicalOpt(env, e.vars, e.req, e.onlyIfs);
            }
            return out === RType.True;
          })
        ) {
          env.newMessage(`${opt} is true, by ${storedFact}`);
          if (storedFact.req.length === 0)
            return new CheckerOut(RType.True, true);
          else return new CheckerOut(RType.True);
        }
      }
    }
    return new CheckerOut(RType.Unknown);
  }

  /**
   * Steps
   * 1. open a new Env
   * 2. emit var and req defined in if-then to new env
   * 3. check onlyIfs of if-then
   */
  export function checkLogicalOpt(
    env: L_Env,
    vars: string[],
    knowWhat: FactNode[],
    checkWhat: FactNode[]
  ): RType {
    const newEnv = new L_Env(env);
    newEnv.declareNewVar(vars);
    executor.knowExec(newEnv, new KnowNode(knowWhat));

    for (const fact of checkWhat) {
      const out = check(newEnv, fact);
      if (out.type === RType.Error) return RType.Error;
      else if ([RType.False, RType.Unknown].includes(out.type)) return out.type;
    }

    return RType.True;
  }

  export function checkByFactsWithNoReq(env: L_Env, node: FactNode): RType {
    if (node instanceof OptNode) {
      return checkOptByFactsWithNoReq(env, node);
    } else if (node instanceof IfThenNode) {
      return checkIfThenByFactsWithNoReq(env, node);
    }

    return RType.Error;
  }

  function checkOptByFactsWithNoReq(env: L_Env, opt: OptNode): RType {
    const facts = env.getOptFact(opt.fullName);
    if (!facts) return RType.Error;

    for (const storedFact of facts) {
      if (
        storedFact.isT === opt.isT &&
        storedFact.vars.every((s, j) => checkSingleVar(s, opt.vars[j])) &&
        storedFact.req.length === 0
      ) {
        return RType.True;
      }
    }

    return RType.Unknown;
  }

  export function checkOptInHave(env: L_Env, opt: OptNode): RType {
    const facts = env.getOptFact(opt.fullName);
    if (!facts) return RType.Error;

    for (const storedFact of facts) {
      if (
        storedFact.vars.every((s, j) => !s.startsWith("#")) &&
        storedFact.req.length === 0 &&
        storedFact.isT === opt.isT
      ) {
        return RType.True;
      }
    }

    return RType.Unknown;
  }

  function checkIfThenByFactsWithNoReq(env: L_Env, node: IfThenNode): RType {
    const newEnv = new L_Env(env);
    newEnv.declareNewVar(node.vars);
    executor.knowExec(newEnv, new KnowNode(node.req));

    for (const fact of node.onlyIfs) {
      const out = checkByFactsWithNoReq(newEnv, fact);
      if (out === RType.Error) return RType.Error;
      else if ([RType.False, RType.Unknown].includes(out)) return out;
    }

    return RType.True;
  }

  function checkSingleVar(trueFact: string, toCheck: string): Boolean {
    return trueFact.startsWith("#") || trueFact === toCheck;
  }

  function fixFree(e: FactNode, freeToFixMap: Map<string, string>): FactNode {
    if (e instanceof IfThenNode) {
      return new IfThenNode(
        e.vars.map((s) => {
          const out = freeToFixMap.get(s);
          if (out === undefined) return s;
          else return out;
        }),
        [...e.req],
        [...e.onlyIfs]
      );
    } else if (e instanceof OptNode) {
      return new OptNode(
        e.fullName,
        e.vars.map((s) => {
          const out = freeToFixMap.get(s);
          if (out === undefined) return s;
          else return out;
        })
      );
    }
    throw Error("fact should be if-then or Opt");
  }

  /** -------------------------------------------------------------- */
  //! PRINCIPLE: STORE FACTS WITH FREE VAR AS KEY, REPLACE FREE VAR WITH FIXED VAR WHEN CHECKING.
  export function checkFactFully(env: L_Env, toCheck: FactNode): RType {
    const newEnv = new L_Env(env);

    if (toCheck instanceof OptNode) {
      const facts = env.getStoredFacts(toCheck.fullName);
      if (!facts) return RType.Error;

      for (const storedFact of facts) {
        for (const req of storedFact.req) {
          const ok = newEnv.fixFrees(storedFact.vars, toCheck.vars);
          if (!ok) return RType.Error;
          if (req instanceof OptNode) {
            const out = checkOptLiterally(newEnv, req);
            if (out === RType.Error) {
              newEnv.getAllMessages().forEach((e) => env.newMessage(e));
              return RType.Error;
            } else if (out === RType.Unknown) {
              continue;
            }
          } else if (req instanceof IfThenNode) {
            req.vars.forEach((e, i) => newEnv.newVar(e, toCheck.vars[i]));
            const out = checkIfThen(newEnv, req);
            if (out === RType.Error) {
              newEnv.getAllMessages().forEach((e) => env.newMessage(e));
              return RType.Error;
            } else if (out === RType.Unknown) {
              continue;
            }
          }
        }

        return RType.True;
      }
    } else if (toCheck instanceof IfThenNode) {
      toCheck.vars.forEach((e) => newEnv.newVar(e, e));
      const out = checkIfThen(newEnv, toCheck);
      return out;
    }

    return RType.Error;
  }

  // the env here is already the env where all check happens. the reason why we don't create the env where everything happens in checkIfThen() is that I think it's better to bind free var with fixed var at higher env
  function checkIfThen(env: L_Env, toCheck: IfThenNode): RType {
    toCheck.vars.forEach((e) => env.newVar(e, e));

    for (const r of toCheck.req) {
      if (r instanceof OptNode) {
        // if (r.vars.every((e) => !toCheck.vars.includes(e))) {
        // notice check in env not newEnv because all facts are declared at higher env
        // notice we check opt literally here to avoid prove-loop when p(x) <=> q(x)
        //   const out = checkOptLiterally(env, r);
        //   checkAndMsg(env, out, r);
        // } else {
        env.storeFact(r.fullName, r.vars, [], r.isT, []);
        // }
      } else if (r instanceof IfThenNode) {
        const newEnv = new L_Env(env);
        r.vars.forEach((e) => newEnv.newVar(e, e));
        const out = checkIfThen(newEnv, r);
        checkAndMsg(env, out, r);
      }
    }

    for (const onlyIf of toCheck.onlyIfs) {
      const out = checkFactFully(env, onlyIf);

      if (out === RType.Unknown) return RType.Unknown;
      if (out === RType.Error) return RType.Error;
    }

    env.newMessage(`OK! ${toCheck} <= ${toCheck}`);
    return RType.True;
  }

  export function checkOptLiterally(env: L_Env, toCheck: OptNode): RType {
    const facts = env.getStoredFacts(toCheck.fullName);
    if (facts === undefined) return RType.Unknown;
    for (const fact of facts) {
      // .map here is necessary
      const vars = toCheck.vars.map((s) => env.getVar(s) as string);
      const out = fact.checkLiterally(vars, toCheck.isT);
      if (out === RType.True) return RType.True;
      else if (out === RType.Error) return RType.Error;
    }

    if (env.getFather() !== undefined)
      return checkOptLiterally(env.getFather() as L_Env, toCheck);
    else return RType.Unknown;
  }
}
