import LeanBook.IntMathlib.Mul

/-- 定数関数を返す -/
private def MyInt.const (z : MyInt) : MyInt → MyInt := fun _ => z

#check_failure MyInt.const (0 : MyNat)

/-- 自然数から整数への変換 -/
def MyInt.ofMyNat (n : MyNat) : MyInt := 〚(n, 0)〛

#check MyInt.const (.ofMyNat 0)

/-- MyNat から MyInt への型強制 -/
instance : Coe MyNat MyInt where
  coe := MyInt.ofMyNat

#check MyInt.const (0 : MyNat)

example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  -- 内部実装である MyInt.ofMyNat が見えてしまう
  guard_target =ₛ MyInt.ofMyNat 0 = 0
  sorry

-- MyInt.ofMyNat を型キャストとして認識させる
attribute [coe] MyInt.ofMyNat

@[simp]
theorem MyInt.ofMyNat_zero_eq_zero : MyInt.ofMyNat 0 = (0 : MyInt) := by
  dsimp [MyInt.ofMyNat]
  rfl

example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  guard_target =ₛ ↑(0 : MyNat) = (0 : MyInt)
  simp

/-- 自然数から整数への自然な包含写像は単射である -/
@[norm_cast]
theorem MyInt.ofMyNat_inj {m n : MyNat}
    : (m : MyInt) = (n : MyInt) ↔ m = n := by
  constructor <;> intro h

  -- ↑m = ↑n → m = n を示す
  case mp =>
    -- このとき (m, 0) と (n, 0) は PreInt として同値である
    have : (m, 0) ≈ (n, 0) := by
      exact Quotient.exact h

    -- これは m + 0 = 0 + n と言い換えられる
    notation_simp at this

    simp_all

  -- m = n → ↑m = ↑n を示す
  case mpr =>
    rw [h]

-- norm_cast で型キャストを外す
@[simp]
theorem MyInt.ofMyNat_eq_zero {n : MyNat} : (n : MyInt) = 0 ↔ n = 0 := by
  constructor <;> intro h
  · rw [show (0 : MyInt) = ↑(0 : MyNat) from rfl] at h
    norm_cast at h
  · simp_all

-- push_cast で型キャストを括弧の内側へ移動させる
@[push_cast]
theorem MyInt.ofNat_add (m n : MyNat)
  : ↑(m + n) = (m : MyInt) + (n : MyInt) := by
  rfl

/-- 整数の広義順序 -/
def MyInt.le (m n : MyInt) : Prop :=
  ∃ k : MyNat, m + ↑k = n

instance : LE MyInt where
  le := MyInt.le

@[notation_simp]
theorem MyInt.le_def (m n : MyInt) : m ≤ n ↔ ∃ k : MyNat, m + ↑k = n := by
  rfl

def MyInt.lt (m n : MyInt) : Prop :=
  m ≤ n ∧ ¬ n ≤ m

instance : LT MyInt where
  lt := MyInt.lt

@[notation_simp]
theorem MyInt.lt_def (a b : MyInt) : a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := by
  rfl

@[refl]
theorem MyInt.le_refl (m : MyInt) : m ≤ m := by
  exists 0
  simp

theorem MyInt.le_trans {m n k : MyInt} (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  -- ≤ は和の等式で定義されていたので
  -- n + ↑l = k を満たす l を構成すればよい
  notation_simp at *

  -- 仮定から、ある a と b が存在して
  -- n + ↑a = m と m + ↑b = k が成り立つ
  obtain ⟨a, ha⟩ := hnm
  obtain ⟨b, hb⟩ := hmk

  -- このとき a + b が求める条件を満たす
  use a + b

  -- これを正当化するには n + ↑(a + b) = k を示せばよいが
  -- これは n + ↑a + ↑b = k と同じ
  push_cast

  -- 仮定から計算すれば示せる
  have : n + (↑a + ↑b) = k := calc
    _ = (n + ↑a) + ↑b := by ac_rfl
    _ = m + ↑b := by rw [ha]
    _ = k := by rw [hb]
  assumption

instance : Trans (· ≤ · : MyInt → MyInt → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyInt.le_trans

instance : Preorder MyInt where
  le_refl := MyInt.le_refl
  le_trans := by
    intro a b c hab hbc
    apply MyInt.le_trans hab hbc

example (a b c : MyInt) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  order

example (a b : MyInt) (h1 : a ≤ b) (h2 : ¬ (a < b)) : b ≤ a := by
  order
