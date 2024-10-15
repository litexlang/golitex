export const setTheory = {
  version1: `
: obj(x)  // Everything is an object.
: set(x) => {}  
know set(#x)  // Everything is a set.
: item(x,A| set(A)) => {}
: setEqual(A,B: set(A), set(B)) => {item(#x, A) => item(x, B); item(#x, B) => item(x, A);}  // 理论上写成 :setEqual(A,B: set(A), set(B), item(#x, A) => item(x, B), item(#x, B) => item(x, A)) 也行
`,
};
