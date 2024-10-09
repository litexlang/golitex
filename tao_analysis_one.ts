export const setTheory = {
  Define_object: ": object(x);",
  Sets_are_objects: ": set(x) {:item(y) }; know object(#x: set(#x));",
  Try_sets_are_objects: "let y: set(y); object(y);",
  Item_of_set: ": item(A,x: set(A));",
  In_both_set: ": inBoth(A,B,y: set(A), set(B) item(A,y)) <=> item(B,y);",
  Equality_of_sets:
    "def equality_of_sets(A,B: set(A), set(B)) <=> {set(A); set(B); inBoth(A,B,#y) ;}",
  A_equals_B: "let A,B: set(A), set(B), equality_of_sets(A,B);",
};
