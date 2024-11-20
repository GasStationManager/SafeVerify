

theorem ppp (P:Prop): P ∨ P ∨ ¬ P:=by
  simp
  exact Classical.em P
