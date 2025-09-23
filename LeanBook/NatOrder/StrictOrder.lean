import LeanBook.NatOrder.OrderDef

/-- m < n を表す -/
def MyNat.lt (m n : MyNat) : Prop := (m + 1) ≤ n

/-- a < b という書き方ができるようにする -/
instance : LT MyNat where
  lt := MyNat.lt

example (m n : MyNat) : m < n ↔ (m + 1) ≤ n := by
  dsimp [(· < ·), MyNat.lt]
  rfl

@[simp] theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

@[simp] theorem MyNat.zero_neq_one : 0 ≠ 1 := by
  intro h
  injection h

/-- 任意の自然数は 0 以上である -/
@[simp] theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  -- ≤ を和の等式に帰着させる
  rw [MyNat.le_iff_add]
  exists n
  simp

/-- 0 以下の自然数は 0 しかない -/
theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => 
    -- n + 1 ≤ 0 という仮定が得られるがこれはありえない
    -- そこで矛盾を示す
    exfalso

    -- ≤ を和の等式に置き換える
    rw [MyNat.le_iff_add] at h
    obtain ⟨k, hk⟩ := h

    -- n + 1 + k = 0 にはなりえないので矛盾
    simp_all

/-- 0 以下の自然数は 0 しかない -/
@[simp] theorem MyNat.le_zero {n : MyNat} : n ≤ 0 ↔ n = 0 := by
  constructor <;> intro h
  · apply MyNat.zero_of_le_zero h
  · simp [h]

/-- 任意の自然数は 0 または正 -/
theorem MyNat.eq_zero_or_pos (n : MyNat) : n = 0 ∨ 0 < n := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- まず狭義順序を ≤ で置き換える
    dsimp [(· < ·), MyNat.lt] at *
    cases ih with
    | inl ih => simp_all
    | inr ih => simp_all [MyNat.le_step]

theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n ≤ m → n = m ∨ n < m := by
  intro h
  dsimp [(· < ·), MyNat.lt]
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  induction k with
  | zero => simp_all
  | succ k _ =>
    right
    exists k
    rw [← hk]
    ac_rfl

/-- 狭義順序は広義順序よりも強い -/
theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := by
  -- < を≤ で置き換える
  dsimp [(· < ·), MyNat.lt] at h
  have : a ≤ b := calc
    _ ≤ a + 1 := by simp
    _ ≤ b := by assumption
  assumption

theorem MyNat.le_of_eq_or_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
  intro h
  cases h with
  | inl h => rw [h]
  | inr h => exact MyNat.le_of_lt h

/-- 広義順序 ≤ は統合 = と狭義順序 < で置き換えられる -/
theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n ≤ m ↔ n = m ∨ n < m := by
  constructor
  · apply MyNat.eq_or_lt_of_le
  · apply MyNat.le_of_eq_or_lt


theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
  -- < を ≤ で置き換える
  dsimp [(· < ·), MyNat.lt]
  induction a with
  | zero =>
    -- 1 ≤ b ∨ b ≤ 0 を示せば十分である
    suffices 1 ≤ b ∨ b ≤ 0 from by simp_all

    -- 任意の自然数は 0 か正であることから
    -- b は 0 か 1 以上である
    have : b = 0 ∨ 0 < b := MyNat.eq_zero_or_pos b
    dsimp [(· < ·), MyNat.lt] at this

    -- b = 0 → b ≥ 0 なので場合分けをすれば示せる
    cases this <;> simp_all

  | succ a ih =>
    cases ih with
    -- b ≤ a のとき
    | inr h =>
      right
      exact le_step h

    -- a + 1 ≤ b のとき
    | inl h =>
      -- このとき a + 1 = b または a + 1 < b のいずれかである
      simp [MyNat.le_iff_eq_or_lt] at h
      cases h with
      -- a + 1 = b のとき
      | inl h =>
        right
        simp_all
      -- a + 1 < b のとき
      | inr h =>
        dsimp [(· < ·), MyNat.lt] at h
        left
        simp_all

theorem MyNat.lt_of_not_le {a b : MyNat} (h : ¬ a ≤ b) : b < a := by
  cases (MyNat.lt_or_ge b a) with
  | inl h => assumption
  | inr h => contradiction

theorem MyNat.not_le_of_lt {a b : MyNat} (h : a < b) : ¬ b ≤ a := by
  -- b ≤ a を仮定して矛盾を導く
  intro hle

  -- 見やすさのために a < b の定義を展開する 
  dsimp [(· < ·), MyNat.lt] at h

  -- 順序関係を和に書き換える
  rw [MyNat.le_iff_add] at *

  -- 仮定の ∃ を外す
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := hle

  -- 仮定 a + 1 + k = b, b + l = a より
  -- a + (k + l + 1) = a が成り立つので
  -- k + l + 1 = 0 となるがこれはありえない
  -- よって矛盾
  have : a + (k + l + 1) = a := calc
    _ = a + 1 + k + l := by ac_rfl
    _ = b + l := by rw [hk]
    _ = a := by rw [hl]
  simp at this

theorem MyNat.lt_iff_le_not_le (a b : MyNat) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor <;> intro h
  case mp => simp_all [MyNat.not_le_of_lt, MyNat.le_of_lt]
  case mpr => simp_all [MyNat.lt_of_not_le]

/-- 任意の自然数は比較可能である -/
theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  cases (MyNat.lt_or_ge a b) <;> simp_all [MyNat.le_of_lt]

example (a : MyNat) : a ≠ a + 1 := by
  simp_all

example (n : MyNat) : ¬ n + 1 ≤ n := by
  intro h
  rw [MyNat.le_iff_add] at h
  obtain ⟨k, hk⟩ := h
  -- 1 + k = 0 が示せれば k が自然数であることから矛盾が示せる
  have : 1 + k = 0 := by 
    have : n + (1 + k) = n + 0 := by
      rw [← MyNat.add_assoc, hk, MyNat.add_zero]
    exact MyNat.add_left_cancel this
  simp_all
