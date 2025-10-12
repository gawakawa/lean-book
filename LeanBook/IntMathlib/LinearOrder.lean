import LeanBook.IntMathlib.DecidableOrd

/-- すべての整数 a に対して 0 ≤ a または 0 ≤ -a のいずれかが成り立つ -/
theorem MyInt.nonnge_or_nonneg_neg {a : MyInt} : 0 ≤ a ∨ 0 ≤ -a := by
  -- a : MyInt の代表元を取る
  induction a using Quotient.inductionOn with
  | h a =>
    -- a = 〚(m, n)〛 と表されているとする
    obtain ⟨m, n⟩ := a

    -- このとき、自然数については全順序であることがすでに示せているので
    -- m ≤ n ∨ n ≤ m が成り立つ
    have : n ≤ m ∨ m ≤ n := by
      exact MyNat.le_total n m

    cases this with
    | inl h =>
      left
      simp [mk_def]
      norm_cast
    | inr h =>
      right
      simp [mk_def]
      norm_cast

/-- 整数は全順序 -/
theorem MyInt.le_total (a b : MyInt) : a ≤ b ∨ b ≤ a := by
  suffices goal : 0 ≤ b - a ∨ 0 ≤ -(b - a) from by
    cases goal with
    | inl h =>
      left
      rw [← MyInt.sub_nonneg]
      assumption
    | inr h =>
      right
      rw [← MyInt.sub_nonneg]
      rw [show -(b - a) = a - b from by abel] at h
      assumption
  exact nonnge_or_nonneg_neg

/-- 整数は線型順序 -/
instance : LinearOrder MyInt where
  toDecidableLE := by infer_instance
  le_total := by exact MyInt.le_total

theorem MyInt.eq_or_lt_of_le {a b : MyInt} (h : a ≤ b) : a = b ∨ a < b := by
  by_cases hor : a = b
  case pos =>
    left
    assumption
  case neg =>
    right
    order

theorem MyInt.le_of_eq_or_lt {a b : MyInt} (h : a = b ∨ a < b) : a ≤ b := by
  cases h with
  | inl h => rw [h]
  | inr h => order

/-- 広義順序 ≤ は等号 = と狭義順序 < で置き換えられる-/
theorem MyInt.le_iff_eq_or_lt {m n : MyInt} : n ≤ m ↔ n = m ∨ n < m := by
  constructor
  case mp => apply MyInt.eq_or_lt_of_le
  case mpr => apply MyInt.le_of_eq_or_lt

example {a b : MyInt} (h : b < a) : ¬ a ≤ b := by
  order

/-- 0 以下の数はマイナスを取ると 0 以上になる -/
example {a : MyInt} (neg : a ≤ 0 ) : -a ≥ 0 := by
  notation_simp at *
  obtain ⟨k, hk⟩ := neg
  use k
  have : 0 + ↑k = -a := calc
    _ = a + ↑k - a := by abel
    _ = 0 - a := by rw [hk]
    _ = -a := by abel
  assumption
