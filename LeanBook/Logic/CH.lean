/-- 1 + 1 = 2 という命題の証明 -/
theorem one_add_one_eq_two : 1 + 1 = 2 := by
  rfl

#check one_add_one_eq_two
#check (by rfl : 1 + 1 = 2)

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

/-- Nat 上の恒等関数 -/
def idOnNat : Nat → Nat := by?
  intro n
  exact n

#eval idOnNat 42

/-- tactic を使わず、証明項を構成することで証明する -/
example (P Q : Prop) (hp : P) : Q → P :=
  fun _hq => hp
