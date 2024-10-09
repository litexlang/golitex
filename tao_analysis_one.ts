export const setTheory = {
  Define_object: ": object(x)",
  Sets_are_objects: ": set(x) {:item(y) }; know object(#x: set(#x));",
  Try_sets_are_objects: "let y: set(y); object(y);",
  Equality_of_sets:
    "def equality_of_sets(A,B: set(A), set(B)) <=> {set(A), set(B); $ inIff(y: set(A):item(y)) <=> set(B):item(y) ;}",
  A_equals_B: "@ set(A), set(B), equality_of_sets(A,B);",
};
