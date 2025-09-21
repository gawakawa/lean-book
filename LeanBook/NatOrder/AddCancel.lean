import LeanBook.NatSemiring.Distrib

/-- MyNat の各コンストラクタの像は重ならない -/
example (n : MyNat) : MyNat.succ n ≠ MyNat.zero := by
  intro h
  injection h

/-- MyNat のコンストラクタは単射 -/
example (m n : MyNat) (h : MyNat.succ m = MyNat.succ n) : m = n := by
  injection h

example (m n : MyNat) (h : m + 1 = n + 1) : m = n := by
  injection h

-- 以降、 l m n は全て MyNat 型の項とする
variable {l m n : MyNat}

/-- 右から足す演算 (· + m) は単射 -/
theorem MyNat.add_right_cancel (h : l + m = n + m) : l = n := by
  induction m with
  | zero =>
    simp_all only [add_zero]
  | succ m ih =>
    have lem : (l + m) + 1 = (n + m) + 1 := calc
      _ = l + (m + 1) := by ac_rfl
      _ = n + (m + 1) := by rw [h]
      _ = (n + m) + 1 := by ac_rfl
    have : l + m = n + m := by 
      injection lem
    exact ih this

/-- 左から足す演算 (l + ·) は単射 -/
theorem MyNat.add_left_cancel (h : l + m = l + n) : m = n := by
  -- 交換法則を使って add_right_cancel に帰着させる
  rw [MyNat.add_comm l m, MyNat.add_comm l n] at h
  exact MyNat.add_right_cancel h

section
  -- ここだけの simp 補題として登録する
  attribute [local simp] MyNat.add_left_cancel

  /-- error: simp made no progress -/
  example : l + m = l + n → m = n := by
    -- 登録したはずだが、 simp に無視されている
    fail_if_success simp
    sorry
end

/-- 右からの足し算のキャンセル -/
@[simp ↓] theorem MyNat.add_right_cancel_iff : l + m = n + m ↔ l = n := by
  constructor
  · apply MyNat.add_right_cancel
  · intro h
    rw [h]

/-- 左からの足し算のキャンセル -/
@[simp ↓] theorem MyNat.add_left_cancel_iff : l + m = l + n ↔ m = n := by
  constructor
  · apply MyNat.add_left_cancel
  · intro h
    rw [h]

example : l + m = l + n → m = n := by
  simp

@[simp] theorem MyNat.add_right_eq_self : m + n = m ↔ n = 0 := by
  constructor <;> intro h
  case mpr => 
    simp_all

  case mp =>
    have : m + n = m + 0 := by
      rw [h]
      simp
    simp_all

  @[simp] theorem MyNat.add_left_eq_self : n + m = m ↔ n = 0 := by
    rw [MyNat.add_comm n m, MyNat.add_right_eq_self]

  @[simp] theorem MyNat.self_eq_add_right : m = m + n ↔ n = 0 := by
    rw [show (m = m + n) ↔ (m + n = m) from by exact eq_comm]
    exact MyNat.add_right_eq_self

  @[simp] theorem MyNat.self_eq_add_left : m = n + m ↔ n = 0 := by
    rw [MyNat.add_comm n m, MyNat.self_eq_add_right]

  /-- 和が 0 なら両方が 0 -/
  theorem MyNat.eq_zero_of_add_eq_zero : m + n = 0 → m = 0 ∧ n = 0 := by
    intro h
    induction n with
    | zero => 
        simp_all
    | succ n ih => 
      exfalso
      rw [show m + (n + 1) = m + n + 1 from by ac_rfl] at h
      injection h

  /-- 両方が 0 なら和も 0 -/
  theorem MyNat.add_eq_zero_of_eq_zero : m = 0 ∧ n = 0 → m + n = 0 := by
    intro h
    simp_all

  /-- 和が 0 であることと両方が 0 であることは同値 -/
  @[simp]
  theorem MyNat.add_eq_zero_iff_eq_zero : m + n = 0 ↔ m = 0 ∧ n = 0 := by
    exact ⟨MyNat.eq_zero_of_add_eq_zero, MyNat.add_eq_zero_of_eq_zero⟩

  /-- 積が 0 であることと片方が 0 であることは同値 -/
  theorem MyNat.mul_eq_zero (m n : MyNat) : m * n = 0 ↔ m = 0 ∨ n = 0 := by
    constructor <;> intro h
    case mpr => 
      cases h <;> simp_all

    case mp => 
      induction n with
      | zero => 
          right
          rfl
      | succ n _ =>
          have : m * n + m = 0 := calc
            _ = m * (n + 1) := by distrib
            _ = 0 := by rw [h]
          -- add_eq_zero_iff_eq_zero より m * n = 0 ∧ m = 0
          -- m = 0 より m = 0 ∨ n = 0 も成り立つ
          simp_all only [MyNat.add_eq_zero_iff_eq_zero, true_or]

  example (n m : MyNat) : n + (1 + m) = n + 2 → m = 1 := by
    intro h
    simp_all
    have : 1 + m = 1 + 1 := by rw [h]; rfl
    simp_all
