import LeanBook.NatOrder.PartialOrder

example : 0 ≤ 1 := by
  apply MyNat.le_step
  apply MyNat.le_refl

example : 0 ≤ 3 := by
  apply MyNat.le_step
  apply MyNat.le_step
  apply MyNat.le_step
  apply MyNat.le_refl

deriving instance DecidableEq for MyNat

example : 32 + 13 ≠ 46 := by
  decide

#eval 1 ≠ 2

def MyNat.ble (a b : MyNat) : Bool :=
  match a, b with
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => MyNat.ble a b

#eval MyNat.ble 0 1
#eval MyNat.ble 4 3
#eval MyNat.ble 3 12

instance (a b : MyNat) : Decidable (a ≤ b) := by
  apply decidable_of_iff (MyNat.ble a b = true)
  guard_target =ₛ MyNat.ble a b = true ↔ a ≤ b
  sorry

#check MyNat.ble.induct

@[simp]
theorem MyNat.ble_zero_left (n : MyNat) : MyNat.ble 0 n = true := by
  rfl

@[simp]
theorem MyNat.ble_zero_right (n : MyNat) : MyNat.ble (n + 1) 0 = false := by
  rfl

@[simp]
theorem MyNat.ble_succ (m n : MyNat) : MyNat.ble (m + 1) (n + 1) = MyNat.ble m n := by
  rfl

def MyNat.ble.inductAux (motive : MyNat → MyNat → Prop)
    (case1 : ∀ (n : MyNat), motive 0 n)
    (case2 : ∀ (n : MyNat), motive (n + 1) 0)
    (case3 : ∀ (m n : MyNat), motive m n → motive (m + 1) (n + 1))
    (m n : MyNat) : motive m n := by
  induction m, n using MyNat.ble.induct with
  | case1 n => apply case1
  | case2 n => apply case2
  | case3 m n h => apply case3; assumption

theorem MyNat.le_impl (m n : MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
  induction m, n using MyNat.ble.inductAux with
  | case1 n =>
    -- m = 0 のケースなので明らか
    simp
  | case2 n =>
    -- n = 0 のケースなので MyNat.ble m n は偽になる
    dsimp [MyNat.ble]
    -- したがって ¬ n + 1 ≤ 0 を示せばよい
    suffices ¬ n + 1 ≤ 0 from by simp_all
    -- 仮に n + 1 ≤ 0 だったとする
    intro h
    -- このとき n + 1 = 0 であるが
    -- 足して 0 になることはないので矛盾
    simp_all
  | case3 m n ih =>
    -- m = m' + 1 および n = n' + 1 のケースなので帰納法の仮定が使える
    -- m ≤ n ↔ m + 1 ≤ n + 1 を示せばよいがこれはすでに示した
    dsimp [MyNat.ble]
    simp [ih]

/-- 広義の順序関係を決定可能にする -/
instance : DecidableLE MyNat := fun n m =>
  decidable_of_iff (MyNat.ble n m = true) (MyNat.le_impl n m)

#eval 1 ≤ 3
#eval 12 ≤ 13
example : 1 ≤ 9 := by
  decide
example : 32 ≤ 47 := by
  decide

theorem MyNat.lt_impl (m n : MyNat) : MyNat.ble (m + 1) n ↔ m < n := by
  rw [MyNat.le_impl]
  rfl

/-- 狭義の順序関係を決定可能にする -/
instance : DecidableLT MyNat := fun n m =>
  decidable_of_iff (MyNat.ble (n + 1) m = true) (MyNat.lt_impl n m)

example : 1 < 4 := by
  decide

example : 23 < 32 ∧ 12 ≤ 24 := by
  decide
