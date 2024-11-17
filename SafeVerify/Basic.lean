def hello := "world"



theorem ppp (P:Prop): P ∨ P ∨ ¬ P:=by
  simp
  exact Classical.em P

def solveAdd (a b:Int):{c:Int//a+c=b}
:=⟨ b-a, by omega⟩
