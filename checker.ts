import {
  ByNode,
  FactNode,
  FactType,
  IfThenNode,
  KnowNode,
  ShortCallOptNode,
} from "./ast";
import { L_Env, StoredFactValue } from "./env";
import { executor, RType } from "./executor";

export namespace checker {
  /**
   * Main function of checker
   * @param env the environment we are working at
   * @param opt the fact (ShortCallOptFact) we wanna prove
   * @param ignore  which fact (ShortCallOpt) to ignore in order to avoid "req => itself, itself => req"-kind loop
   * @returns RType Error, True, False
   */
  export function checkShortOpt(
    env: L_Env,
    opt: ShortCallOptNode,
    ignore: string[] = []
  ): RType {
    const facts = env.getShortOptFact(opt.fullName);
    if (!facts) return RType.Error;

    for (const storedFact of facts) {
      /**
       * Main Logic of Checking Steps:
       * 1. literally correct
       * 2. req correct
       * 2.1 locally correct
       * 2.2 correctness is given by father
       */
      if (
        storedFact.vars.every((ls, i) =>
          ls.every((s, j) => checkSingleVar(s, opt.params[i][j]))
        )
      ) {
        /**
         * check current opt by replacing potential hashed var with current var
         */
        //! I think the following fixing is buggy
        const freeToFixMap = new Map<string, string>();
        storedFact.vars.forEach((lst, i) =>
          lst.forEach((s, j) => freeToFixMap.set(s, opt.params[i][j]))
        );

        if (
          storedFact.req.every((e) => {
            if (e instanceof ShortCallOptNode) {
              const out = checkShortOptByFactsWithNoReq(
                env,
                fixFree(e, freeToFixMap) as ShortCallOptNode
              );
              return out === RType.True;
            }
            //  else if (e instanceof IfThenNode) {
            //   //! I FORBID IF-THEN AS STORED REQ TO AVOID DEAD-LOCK AND TOO-LONG SEARCHING
            //   return false;
            // }

            // const out = checker.check(env, fixFree(e, freeToFixMap));
            // switch (out) {
            //   case RType.True:
            //     return true;
            //   case RType.Unknown: {
            //     const father = env.getFather();
            //     return father ? checkShortOpt(father, opt) : false;
            //   }
            //   default:
            //     return false;
            // }
          })
        ) {
          env.newMessage(`${opt} is true, by ${storedFact}`);
          return RType.True;
        }
      }
    }

    return RType.Unknown;
  }

  function checkSingleVar(trueFact: string, toCheck: string) {
    return trueFact.startsWith("#") || trueFact === toCheck;
  }

  export function check(env: L_Env, node: FactNode): RType {
    if (node instanceof ShortCallOptNode) {
      return checkShortOpt(env, node);
    } else if (node instanceof IfThenNode) {
      return checkIfThen(env, node);
    } else if (node instanceof ByNode) {
      return checkBy(env, node);
    }

    return RType.Error;
  }

  /**
   * Steps
   * 1. open a new Env
   * 2. emit var and req defined in if-then to new env
   * 3. check onlyIfs of if-then
   */
  export function checkIfThen(env: L_Env, node: IfThenNode): RType {
    const newEnv = new L_Env(env);
    newEnv.declareNewVar(node.freeVars);
    executor.knowExec(newEnv, new KnowNode(node.req));

    for (const fact of node.onlyIfs) {
      const out = check(newEnv, fact);
      if (out === RType.Error) return RType.Error;
      else if ([RType.False, RType.Unknown].includes(out)) return out;
    }

    return RType.True;
  }

  function checkBy(env: L_Env, node: ByNode): RType {
    return RType.Error;
  }

  function fixFree(e: FactNode, freeToFixMap: Map<string, string>): FactNode {
    if (e instanceof IfThenNode) {
      return new IfThenNode(
        e.freeVars.map((s) => {
          const out = freeToFixMap.get(s);
          if (out === undefined) return s;
          else return out;
        }),
        [...e.req],
        [...e.onlyIfs]
      );
    } else if (e instanceof ShortCallOptNode) {
      return new ShortCallOptNode(
        e.fullName,
        e.params.map((ls) =>
          ls.map((s) => {
            const out = freeToFixMap.get(s);
            if (out === undefined) return s;
            else return out;
          })
        )
      );
    }
    throw Error("fact should be if-then or shortOpt");
  }

  function checkShortOptByFactsWithNoReq(env: L_Env, opt: ShortCallOptNode) {
    const facts = env.getShortOptFact(opt.fullName);
    if (!facts) return RType.Error;

    for (const storedFact of facts) {
      if (
        storedFact.vars.every((ls, i) =>
          ls.every((s, j) => checkSingleVar(s, opt.params[i][j]))
        ) &&
        storedFact.req.length === 0 &&
        storedFact.isT
      ) {
        return RType.True;
      }
    }

    return RType.Unknown;
  }
}
