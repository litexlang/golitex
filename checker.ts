import { FactNode, ShortCallOptNode } from "./ast";
import { L_Env, StoredFactValue } from "./env";
import { RType } from "./executor";

class Checker {
  constructor() {

  }

  private literallyCheckShortOpt(env: L_Env, opt: ShortCallOptNode): RType {
    const facts = env.shortOptFacts.get(opt.fullName)
    if (!facts) return RType.Error
    
    for (const storedFact of facts) {
      if (storedFact.vars.every((ls,i) => ls.every((s,j) => checkSingleVar(s, opt.params[i][j])))) {
        return RType.True
      }
    }

    return RType.Unknown

    function checkSingleVar(trueFact:string, toCheck: string) {
      return (trueFact.startsWith("#") || trueFact === toCheck) 
    }
  }

  private checkOpt(env: L_Env, opt: ShortCallOptNode): RType {
    // TODO
    return this.literallyCheckShortOpt(env,opt)
  }
  
  check(env: L_Env, node: FactNode): RType {
    if (node instanceof ShortCallOptNode) {
      return this.checkOpt(env, node)
    } 

    return RType.Error
  }

}

export const checker = new Checker();