export const setTheory = {
  version1: `
: obj(x)  // Everything is an object.
: set(x) => {}  
know set(#x)  // Everything is a set.
: item(x,A| set(A)) => {}
: setEqual(A,B| set(A), set(B), if x | item(x,A) => item(x,B) [p], :p(B,A:#x) ) 
`,
};
