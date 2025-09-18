import LeanBook.NatCommMonoid.AcRfl

#check MyNat.rec

/-- MyNat 用の帰納法の原理を書き直したもの -/
def MyNat.recAux.{u} {motive : MyNat → Sort u} 
  (zero : motive 0) 
  (succ : (n : MyNat) → motive n → motive (n + 1))
  (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

attribute [induction_eliminator] MyNat.recAux

example (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    guard_target =ₛ m + 0 = 0 + m
    simp
  | succ n ih =>
    guard_target =ₛ m + (n + 1) = (n + 1) + m
    ac_rfl

/-- 1 つ前の自然数を返す関数 -/
private def MyNat.pred (n : MyNat) : MyNat := 
  match n with
  | 0 => 0
  | n + 1 => n

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    ac_rfl
