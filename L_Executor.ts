import { L_Env } from "./L_Env";
import * as L_Checker from "./L_Checker";
import * as L_Memory from "./L_Memory";
import { checkFact } from "./L_Checker";
import * as L_Nodes from "./L_Nodes";
import * as L_Report from "./L_Report";
import { L_Out, L_Singleton, L_Symbol } from "./L_Structs";

export const DEBUG_DICT = {
  newFact: true,
  def: true,
  check: true,
  storeBy: true,
  let: true,
  checkCompositeVar: true,
};

export const CheckFalse = true;

export function L_Exec(env: L_Env, node: L_Nodes.L_Node): L_Out {
  try {
    if (node instanceof L_Nodes.ToCheckNode) {
      return factExec(env, node);
    } else if (node instanceof L_Nodes.LetNode) {
      return letExec(env, node);
    } else if (node instanceof L_Nodes.KnowNode) {
      return knowExec(env, node);
    } else if (node instanceof L_Nodes.ProveNode) {
      return proveExec(env, node);
    } else if (node instanceof L_Nodes.ProveContradictNode) {
      return proveContradictExec(env, node);
    } else if (node instanceof L_Nodes.LocalEnvNode) {
      return localEnvExec(env, node);
    }
    //  else if (node instanceof L_Nodes.SpecialNode) {
    //   return specialExec(env, node);
    // }

    throw new Error(`${node} can not be executed at runtime.`);
  } catch (error) {
    return L_Report.L_ReportErr(env, L_Exec, node, error);
  }
}

// function letExec(env: L_Env, node: L_Nodes.LetNode): L_Out {
//   try {
//     // examine whether some vars are already declared. if not, declare them.
//     for (const e of node.vars) {
//       const ok = env.newSingletonVar(e);
//       if (!ok) return L_Out.Error;
//     }

//     if (!optsVarsDeclaredInFacts(env, node.facts)) {
//       throw Error();
//     }

//     // store new facts
//     for (const onlyIf of node.facts) {
//       const ok = L_Memory.newFact(env, onlyIf);
//       if (!ok) {
//         L_Report.reportStoreErr(env, knowExec.name, onlyIf);
//         throw new Error();
//       }
//     }

//     env.report(`[let] ${node}`);
//     return L_Out.True;
//   } catch {
//     return L_Report.L_ReportErr(env, letExec, node);
//   }
// }

export function knowExec(env: L_Env, node: L_Nodes.KnowNode): L_Out {
  try {
    // examine whether all facts are declared.
    // ! NEED TO IMPLEMENT EXAMINE ALL VARS ARE DECLARED.
    if (!node.facts.every((e) => env.factDeclaredOrBuiltin(e))) throw Error();
    // if (!L_Nodes.ToCheckNode.optsDeclared(env, node.facts)) {
    //   throw Error();
    // }

    // store new knowns
    for (const onlyIf of node.facts) {
      const ok = L_Memory.newFact(env, onlyIf);
      if (!ok) {
        L_Report.reportStoreErr(env, knowExec.name, onlyIf);
        throw new Error();
      }
    }

    // for (const [i, v] of node.names.entries()) {
    //   const ok = env.newNamedKnownToCheck(v, node.facts[i]);
    //   if (!ok) throw new Error();
    // }

    return L_Out.True;
  } catch {
    return L_Report.L_ReportErr(env, knowExec, node);
  }
}

// function defExec(env: L_Env, node: L_Nodes.DefNode): L_Out {
//   try {
//     // declare new opt
//     const ok = declNewFact(env, node);
//     if (!ok) {
//       env.report(`Failed to store ${node}`);
//       return L_Out.Error;
//     }

//     if (!optsVarsDeclaredInFacts(env, node.onlyIfs)) {
//       throw Error();
//     }

//     return L_Out.True;
//   } catch {
//     return L_Messages.L_ReportErr(env, defExec, node);
//   }

//   function declNewFact(env: L_Env, node: L_Nodes.DefNode): boolean {
//     let ok = true;
//     // if (node instanceof L_Nodes.DefExistNode) {
//     //   ok = env.newDef(node.opt.optSymbol.name, node);
//     //   ok = env.newExistDef(node.opt.optSymbol.name, node);
//     // } else {
//     ok = env.newDef(node.opt.optSymbol.name, node);
//     // }
//     for (const onlyIf of node.onlyIfs) {
//       const ok = L_Memory.newFact(env, onlyIf);
//       if (!ok) return env.errMesReturnBoolean(`Failed to store ${onlyIf}`);
//     }
//     return ok;
//   }
// }

function factExec(env: L_Env, toCheck: L_Nodes.ToCheckNode): L_Out {
  try {
    // TODO: Implement check whether the given toCheck exists and given var exists.

    const out = L_Checker.checkFact(env, toCheck);

    if (out === L_Out.True) {
      // Store Fact
      const ok = L_Memory.newFact(env, toCheck);
      if (!ok) {
        env.report(`Failed to store ${toCheck}`);
        return L_Out.Error;
      }
    }

    return L_Report.reportL_Out(env, out, toCheck);
  } catch {
    return L_Report.L_ReportErr(env, factExec, toCheck);
  }
}

function localEnvExec(env: L_Env, localEnvNode: L_Nodes.LocalEnvNode): L_Out {
  try {
    env.report(`[new local environment]\n`);
    let out = L_Out.True;
    for (let i = 0; i < localEnvNode.nodes.length; i++) {
      const ok = L_Exec(localEnvNode.localEnv, localEnvNode.nodes[i]);
      localEnvNode.localEnv.getMessages().forEach((e) => env.report(e));
      localEnvNode.localEnv.clearMessages();
      if (L_Out.True !== ok) {
        out = ok;
        if (L_Out.Error === out) return L_Out.Error;
      }
    }
    env.report(`\n[end of local environment]`);

    return out;
  } catch {
    return L_Report.L_ReportErr(env, localEnvExec, localEnvExec);
  }
}

// function specialExec(env: L_Env, node: L_Nodes.SpecialNode): L_Out {
//   try {
//     switch (node.keyword) {
//       case L_Keywords.ClearKeyword:
//         env.clear();
//         return L_Out.True;
//       case L_Keywords.RunKeyword: {
//         runFileWithLogging(env, node.extra as string, true, false);
//         return L_Out.True;
//       }
//     }

//     return L_Out.Error;
//   } catch {
//     return L_Report.L_ReportErr(env, specialExec, node);
//   }
// }

// function letsExec(env: L_Env, node: L_Nodes.LetsNode): L_Out {
//   try {
//     env.newLetsSymbol(node);
//     for (const fact of node.facts) {
//       L_Memory.newFact(env, fact);
//     }
//     env.report(`<lets OK!> ${node.toString()}`);
//     return L_Out.True;
//   } catch {
//     return L_Report.L_ReportErr(env, letsExec, node);
//   }
// }

function proveContradictExec(
  env: L_Env,
  proveNode: L_Nodes.ProveContradictNode
): L_Out {
  try {
    const newEnv = new L_Env(env);
    const negativeToProve = proveNode.toProve.copyWithIsTReverse();
    L_Memory.newFact(newEnv, negativeToProve);

    // TODO Must check all opt and vars in toProve is declared in env instead of in env
    for (const node of proveNode.block) {
      const out = L_Exec(newEnv, node);
      if (out !== L_Out.True) {
        env.report(`failed to run ${node}`);
        throw Error();
      }
    }

    const out = factExec(newEnv, proveNode.contradict);
    const out2 = factExec(newEnv, proveNode.contradict.copyWithIsTReverse());

    if (out === L_Out.True && out2 === L_Out.True) {
      L_Memory.newFact(env, proveNode.toProve);
      env.report(`[prove_by_contradict] ${proveNode.toProve}`);
      return L_Out.True;
    } else {
      env.report(
        `failed: ${proveNode.contradict} is supposed to be both true and false`
      );
      return L_Out.Unknown;
    }
  } catch {
    return L_Report.L_ReportErr(env, proveContradictExec, proveNode);
  }
}

function proveExec(env: L_Env, proveNode: L_Nodes.ProveNode): L_Out {
  try {
    const newEnv = new L_Env(env);
    if (proveNode.toProve instanceof L_Nodes.IfNode) {
      return proveIfExec(env, proveNode);
    } else if (proveNode.toProve instanceof L_Nodes.OptNode) {
      return proveOptExec(env, proveNode);
    }

    throw Error();
  } catch {
    return L_Report.L_ReportErr(env, proveExec, proveNode);
  }
}

function proveOptExec(env: L_Env, proveNode: L_Nodes.ProveNode): L_Out {
  try {
    const newEnv = new L_Env(env);

    // TODO Must check all opt and vars in toProve is declared in env instead of in env
    for (const node of proveNode.block) {
      const out = L_Exec(newEnv, node);
      if (out !== L_Out.True) {
        env.report(`failed to run ${node}`);
        throw Error();
      }
    }

    const out = L_Checker.checkFact(newEnv, proveNode.toProve);
    if (out === L_Out.True) {
      const ok = L_Memory.newFact(env, proveNode.toProve);
      if (ok) return L_Out.True;
      else throw Error();
    } else {
      env.report(`[prove failed] ${proveNode.toProve}`);
      return L_Out.Unknown;
    }
  } catch {
    return L_Report.L_ReportErr(env, proveOptExec, proveNode);
  }
}

function proveIfExec(env: L_Env, proveNode: L_Nodes.ProveNode): L_Out {
  try {
    const newEnv = new L_Env(env);
    const toProve = proveNode.toProve as L_Nodes.IfNode;

    let ok = true;
    for (const v of toProve.vars) {
      //TODO how to composite?
      if (v instanceof L_Singleton) {
        ok = env.safeNewPureSingleton(v.value);
        if (!ok) {
          L_Report.L_ReportErr(
            env,
            proveIfExec,
            `The variable "${v}" is already declared in this environment or its parent environments. Please use a different name.`
          );
          throw Error();
        }
      }
    }

    for (const node of toProve.req) {
      ok = L_Memory.newFact(newEnv, node);
      if (!ok) {
        throw Error();
      }
    }

    // TODO Must check all opt and vars in toProve is declared in env instead of in env
    for (const node of proveNode.block) {
      const out = L_Exec(newEnv, node);
      if (out !== L_Out.True) {
        env.report(`failed to run ${node}`);
        throw Error();
      }
    }

    for (const onlyIf of toProve.onlyIfs) {
      const out = factExec(newEnv, onlyIf);
      if (out !== L_Out.True) {
        env.report(`Failed to check ${onlyIf}`);
        throw Error();
      }
    }

    const out = L_Memory.newFact(env, toProve);
    if (out) {
      env.report(`[prove] ${proveNode}`);
      return L_Out.True;
    } else {
      throw Error();
    }
  } catch {
    return L_Report.L_ReportErr(env, proveIfExec, proveNode);
  }
}

function letExec(env: L_Env, node: L_Nodes.LetNode): L_Out {
  try {
    if (!node.facts.every((e) => env.factDeclaredOrBuiltin(e))) {
      throw Error();
    }

    for (const e of node.vars) {
      const ok = env.safeNewPureSingleton(e);
      if (!ok) return L_Out.Error;
    }

    // store new facts
    for (const onlyIf of node.facts) {
      const ok = L_Memory.newFact(env, onlyIf);
      if (!ok) {
        L_Report.reportStoreErr(env, letExec.name, onlyIf);
        throw new Error();
      }
    }

    env.report(`[let] ${node}`);
    return L_Out.True;
  } catch {
    return L_Report.L_ReportErr(env, letExec, node);
  }
}

// function defCompositeExec(env: L_Env, node: L_Nodes.DefCompositeNode): L_Out {
//   try {
//     if (!env.newCompositeVar(node.composite.name, node)) throw Error();
//     return env.report(`[new def_composite] ${node}`);
//   } catch {
//     return L_Messages.L_ReportErr(env, defCompositeExec, node);
//   }
// }

// function macroExec(env: L_Env, node: L_Nodes.MacroNode): L_Out {
//   try {
//     if (!env.newMacro(node)) throw Error();
//     return env.report(`[new macro] ${(node as L_Nodes.MacroNode).toString()}`);
//   } catch {
//     return L_Report.L_ReportErr(env, macroExec, node);
//   }
// }

// function haveExec(env: L_Env, node: L_Nodes.HaveNode): L_Out {
//   try {
//     let existSymbolNum = 0;
//     for (const v of node.fact.vars) {
//       if (v instanceof L_Singleton) {
//         if (v.value === L_Keywords.ExistSymbol) existSymbolNum += 1;
//       }
//     }

//     if (node.vars.length !== existSymbolNum) throw Error();

//     const out = L_Checker.checkFact(env, node.fact);

//     if (out !== L_Out.True) return out;

//     for (const v of node.vars) {
//       const ok = env.newLetSymbol(v.value);
//       if (!ok) throw Error();
//     }

//     const newVars: L_Symbol[] = [];
//     let existSymbolAlreadyGot = 0;
//     for (const v of node.fact.vars) {
//       if (v instanceof L_Singleton && v.value === L_Keywords.ExistSymbol) {
//         newVars.push(node.vars[existSymbolAlreadyGot]);
//         existSymbolAlreadyGot += 1;
//       } else {
//         newVars.push(v);
//       }
//     }

//     const opt = new L_Nodes.OptNode(
//       node.fact.optSymbol,
//       newVars,
//       node.fact.isT,
//       node.fact.checkVars
//     );

//     const ok = L_Memory.newFact(env, opt);
//     if (ok) return L_Out.True;
//     else throw Error();
//   } catch {
//     return L_Report.L_ReportErr(env, haveExec, node);
//   }
// }
