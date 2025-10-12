import LeanBook.IntMathlib.PartialOrder

/-- MyInt の足し算は順序を保つ
MyInt は可換なので、 c + a ≤ c + b が成り立てば
a + c ≤ b + c も自明に成り立つ -/
theorem MyInt.add_le_add_left (a b : MyInt) (h : a ≤ b) (c : MyInt)
    : c + a ≤ c + b := by
  -- ≤ の定義より、 a + ↑m = b となる自然数 m : MyNat が存在する
  -- このとき、 ∃ k, c + a + ↑k = c + b を示せばよい
  notation_simp at *
  obtain ⟨m, hm⟩ := h

  -- ここで、 k = m とすればよい
  use m

  -- 正当化は、結合法則と m の定義から従う
  have : c + a + ↑m = c + b := calc
    _ = c + (a + ↑m) := by ac_rfl
    _ = c + b := by rw [hm]
  assumption

/-- MyInt は順序群 -/
instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := MyInt.add_le_add_left

/-- 非負の整数は自然数に対応する -/
example {a : MyInt} (nneg : 0 ≤ a) : ∃ k : MyNat, a = ↑k := by
  notation_simp at nneg
  obtain ⟨k, hk⟩ := nneg
  use k
  have : a = ↑k := calc
    _ = a := rfl
    _ = 0 + ↑k := by rw [← hk]
    _ = ↑k := by ac_rfl
  assumption
