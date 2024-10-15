import { FactNode } from "./ast";
import { L_Env } from "./env";
import { hRunErr, RType } from "./executor";

export const UdfErr = undefined;
export type UdfErr = undefined;
export const isUdf = (s: any) => s === undefined;
export const notUdf = (s: any) => s !== undefined;
export const L_OutErrV = null;
export type L_OutErrV = null;

export type L_Out<T> = {
  v: T | null; // v === null works as signal of err
  err: string;
};

export const ErrL_Out = { v: null, err: "" };

export function cL_Out<T>(v: T | null, err: string = ""): L_Out<T> {
  return { v, err };
}

export function isL_OutErr<T>(out: L_Out<T>) {
  return out.v === null ? true : false;
}

export function cErr_Out(err: string = "Error") {
  return { v: null, err: err };
}

// export function cNoRelTErr_Out(opt: FactNode) {
//   return { v: null, err: `${opt.optName} undeclared.` };
// }

export function cEnvRType(
  env: L_Env,
  t: RType = RType.Error,
  m: string = ""
): RType {
  hRunErr(env, t, m);
  return t;
}

export function relTNotFoundEnvErr(env: L_Env, node: FactNode): RType {
  return cEnvRType(env, RType.Error, `${FactNode.toString()} undeclared`);
}

export type RL_Out = L_Out<RType> | L_Out<null>;

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
  fixedOpt: FactNode | string[][],
  free: string[][],
  fixWhats: FactNode[]
): L_Out<FactNode[]> {
  let fixedParams: string[][];
  if (Array.isArray(fixedOpt)) {
    fixedParams = fixedOpt;
  } else {
    fixedParams = fixedOpt.optParams;
  }

  const temp = freeFixMap(free, fixedParams);
  if (isL_OutErr(temp)) return cErr_Out("");
  const mapping = temp.v;

  const res: FactNode[] = [];
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
    else res.push(FactNode.create(fixWhat.optName, fixedParams as string[][]));
  }

  return cL_Out(res);
}

export function hRemoveHashPrefix(arr: string[][]): string[][] {
  return (arr as string[][]).map((ls) =>
    ls.map((s) => (s.startsWith("#") ? s.slice(1) : s))
  );
}

export function isRTypeErr(r: RType) {
  return r === RType.Error;
}

export function isRTypeTrue(r: RType) {
  return r === RType.True;
}
