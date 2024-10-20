export const setTheory = [
  `def obj x; // Everything is an object.`,
  `: set x;`,
  `know set(#x)  // Everything is a set.`,
  "let y; set(y);",
  `: item x,A | set(A)  => {} ;`,
  `: eq A,B| set(A), B is set, if x | item(x,A) => item(x,B), if x | item(x,B) => item(x,A);`,
  `let EMPTY_SET |  if x => not item(x,EMPTY_SET); ; `,
  "know if A,B| eq(EMPTY_SET, A), eq(EMPTY_SET, B) => {eq(A,B)};",
];