import LeanBook.NatOrder.AddCancel

/-- 自然数上の広義の順序関係 -/
inductive MyNat.le (n : MyNat) : MyNat → Prop
  /-- ∀ n, n ≤ n -/
  | refl : MyNat.le n n
  /-- n ≤ m ならば n ≤ m + 1 -/
  | step {m : MyNat} : MyNat.le n m → MyNat.le n (m + 1)

/-- MyNat.le を ≤ で表せるようにする -/
instance : LE MyNat where
  le := MyNat.le

/-- 順序関係についての帰納法の例 -/
example (m n : MyNat) (P : MyNat → MyNat → Prop) (h : m ≤ n) : P m n := by
  induction h with
  | refl =>
    -- m = n の場合
    guard_target =ₛ P m m
    sorry
  | @step n h ih =>
    -- P m n → P m (n + 1) を示す
    guard_hyp ih : P m n
    guard_target =ₛ P m (n + 1)
    sorry

 @[induction_eliminator]
 def MyNat.le.recAux {n b : MyNat}
    {motive : (a : MyNat) → n ≤ a → Prop}
    (refl : motive n MyNat.le.refl)
    (step : ∀ {m : MyNat} (a : n ≤ m),
      motive m a → motive (m + 1) (MyNat.le.step a))
    (t : n ≤ b) :
  motive b t := by
  induction t with
  | refl => exact refl
  | @step c h ih =>
    exact step (a := h) ih

/-- 反射律 -/
theorem MyNat.le_refl (n : MyNat) : n ≤ n := by
  exact MyNat.le.refl

-- m, n, k は MyNat の項とする
variable {m n k : MyNat}

theorem MyNat.le_step (h : n ≤ m) : n ≤ m + 1 := by
  apply MyNat.le.step
  exact h

/-- 推移律 -/
theorem MyNat.le_trans (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  induction hmk with
  | refl => exact hnm
  | @step k hmk ih => exact MyNat.le_step ih

attribute [refl] MyNat.le_refl

theorem MyNat.le_add_one_right (n : MyNat) : n ≤ n + 1 := by
  apply MyNat.le_step
  -- 反射律を rfl で示せる
  rfl

/-- MyNat.le を推移的な二項関係として登録する -/
instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyNat.le_trans

-- calc で推移律を扱える
theorem MyNat.le_add_one_left (n : MyNat) : n ≤ 1 + n := calc
  _ ≤ n + 1 := by apply le_add_one_right
  _ = 1 + n := by ac_rfl

-- n ≤ n, n ≤ n + 1, n ≤ 1 + n を simp で使えるようにする
attribute [simp] MyNat.le_refl MyNat.le_add_one_right MyNat.le_add_one_left

/-- a ≤ b から和の等式を導く -/
theorem MyNat.le.dest (h : n ≤ m) : ∃ k, n + k = m := by
  induction h with
  | refl => exists 0
  | @step l h ih => 
    obtain ⟨k, ih⟩ := ih
    exists k + 1
    rw [← ih]
    ac_rfl

theorem MyNat.le_add_right (n m : MyNat) : n ≤ n + m := by
  induction m with
  | zero => rfl
  | succ k ih => 
    rw [show n + (k + 1) = (n + k) + 1 from by ac_rfl]
    exact MyNat.le.step ih

/-- 和の等式から a ≤ b を導く -/
theorem MyNat.le.intro (h : n + k = m) : n ≤ m := by
  rw [← h]
  induction k with
  | zero => rfl
  | succ k ih => apply MyNat.le_add_right

/-- 順序関係 n ≤ m を足し算で書き換える -/
theorem MyNat.le_iff_add : n ≤ m ↔ ∃ k, n + k = m := by
  constructor <;> intro h
  · exact MyNat.le.dest h
  · obtain ⟨k, hk⟩ := h
    exact MyNat.le.intro hk

  example : 1 ≤ 4 := by
    rw [MyNat.le_iff_add]
    exists 3
