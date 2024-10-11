export type L_Out<T> = {
  value: T | null;
  error: string | null;
};

export function cL_Out<T>(value: T, error: string | null = null): L_Out<T> {
  return { value, error };
}

export function cErr_Out(err: string) {
  return { value: null, error: err };
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
