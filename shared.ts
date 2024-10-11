import { findIndex } from "lodash";
import { CallOptNode } from "./ast";
import { L_Env } from "./env";

export type L_Out<T> = {
  value: T | null;
  errStr: string;
};

export function cL_Out<T>(value: T, errStr: string = ""): L_Out<T> {
  return { value, errStr };
}
export function isL_OutErr<T>(out: L_Out<T>) {
  return out.value === null ? true : false;
}

export function cErr_Out(err: string = "Error") {
  return { value: null, errStr: err };
}

export function cNoRelTErr_Out(opt: CallOptNode) {
  return { value: null, errStr: `${opt.optName} undeclared.` };
}

export function freeFixMap(
  free: string[][],
  fix: string[][],
  ignoreHash: Boolean = true
): L_Out<Map<string, string>> {
  try {
    if (free.length !== fix.length) return cErr_Out("");
    if (!free.every((e, i) => e.length === fix[i].length)) cErr_Out("");

    const flatFree = free.flat();
    const fixedFree = fix.flat();

    const result = new Map<string, string>();

    if (ignoreHash)
      flatFree.forEach((e, i) => {
        if (result.has(e)) {
          if (result.get(e) !== fixedFree[i]) {
            /** If the same free var is valued by 2 literally different vars, error. */
            //! TODO: When Alias and symbolically eq introduced, extra logic will be added here.
            throw Error;
          }
        } else {
          if (e.startsWith("#")) result.set(e.slice(1), fixedFree[i]);
          else result.set(e, fixedFree[i]);
        }
      });
    else flatFree.forEach((e, i) => result.set(e, fixedFree[i]));

    return cL_Out<Map<string, string>>(result);
  } catch (error) {
    return cErr_Out("");
  }
}

export function fixOpt(
  env: L_Env,
  fixedOpt: CallOptNode,
  free: string[][],
  fixWhats: CallOptNode[]
): L_Out<CallOptNode[]> {
  const relT = env.getRelT(fixedOpt);
  if (!relT) return cNoRelTErr_Out(fixedOpt);

  const temp = freeFixMap(free, fixedOpt.optParams);
  if (isL_OutErr(temp)) return cErr_Out("");
  const mapping = temp.value;

  const res: CallOptNode[] = [];
  for (let fixWhat of fixWhats) {
    let hasError = false;
    const fixedParams = fixWhat.optParams.map((ls) =>
      ls.map((s) => {
        const fixedS = mapping?.get(s);
        if (fixedS === undefined) hasError = true;
        else {
          return fixedS;
        }
      })
    );
    if (hasError) return cErr_Out();
    else
      res.push(CallOptNode.create(fixWhat.optName, fixedParams as string[][]));
  }

  return cL_Out(res);
}
