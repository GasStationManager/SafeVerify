def solveAdd (a b : Int) : {c : Int // a + c = b} :=
  ⟨b - a, by omega⟩
