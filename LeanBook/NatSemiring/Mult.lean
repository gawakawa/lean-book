import LeanBook.NatCommMonoid.BetterInduction

/-- MyNat についての掛け算 -/
def MyNat.mul (m n : MyNat) : MyNat := 
  match n with
  | 0 => 0
  | n + 1 => MyNat.mul m n + m

/-- MyNat の掛け算を * で表せるように型クラス Mul のインスタンスにする -/
instance : Mul MyNat where
  mul := MyNat.mul

#eval 2 * 3
#eval 3 * 5

/-- 右のオペランドにある (· + 1) の除去 -/
theorem MyNat.mul_add_one (m n : MyNat) : m * (n + 1) = m * n + m := by
  rfl

/-- 左のオペランドにある (· + 1) の除去 -/
theorem MyNat.add_one_mul (m n : MyNat) : (m + 1) * n = m * n + n := by
  induction n with
  | zero => rfl
  | succ n ih => calc
    _ = (m + 1) * (n + 1) := by rfl
    _ = (m + 1) * n + (m + 1) := by rw [MyNat.mul_add_one]
    _ = m * n + n + (m + 1) := by rw [ih]
    _ = m * n + m + (n + 1) := by ac_rfl
    _ = m * (n + 1) + (n + 1) := by rw [MyNat.mul_add_one]

/-- 右から 0 を掛けても 0 -/
@[simp] theorem MyNat.mul_zero (m : MyNat) : m * 0 = 0 := by
  rfl

/-- 左から 0 を掛けても 0 -/
@[simp] theorem MyNat.zero_mul (n : MyNat) : 0 * n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [MyNat.mul_add_one, ih]

/-- 右から 1 を掛けても変わらない -/
@[simp] theorem MyNat.mul_one (n : MyNat) : n * 1 = n := calc
  _ = n * (0 + 1) := by simp
  _ = n * 0 + n := by rw [MyNat.mul_add_one]
  _ = n := by simp

/-- 左から 1 を掛けても変わらない -/
@[simp] theorem MyNat.one_mul (n : MyNat) : 1 * n = n := calc
  _ = (0 + 1) * n := by simp
  _ = 0 * n + n := by rw [MyNat.add_one_mul]
  _ = n := by simp

/-- 掛け算の交換法則 -/
theorem MyNat.mul_comm (m n : MyNat) : m * n = n * m := by
  induction n with
  | zero => simp
  | succ n ih => calc
    _ = m * (n + 1) := by rfl
    _ = m * n + m := by rw [MyNat.mul_add_one]
    _ = n * m + m := by rw [ih]
    _ = (n + 1) * m := by rw [MyNat.add_one_mul]

/-- 右から掛けたときの分配法則 -/
theorem MyNat.add_mul (l m n : MyNat) : (l + m) * n = l * n + m * n := by
  induction n with
  | zero => rfl
  | succ n ih => calc
    _ = (l + m) * (n + 1) := by rfl
    _ = (l + m) * n + (l + m) := by rw [MyNat.mul_add_one]
    _ = l * n + m * n + (l + m) := by rw [ih]
    _ = (l * n + l) + (m * n + m) := by ac_rfl
    _ = (l * (n + 1)) + (m * n + m) := by rw [MyNat.mul_add_one]
    _ = l * (n + 1) + m * (n + 1) := by rw [← MyNat.mul_add_one]

/-- 右から掛けたときの分配法則 -/
theorem MyNat.mul_add (l m n : MyNat) : l * (m + n) = l * m + l * n := calc
  _ = (m + n) * l := by rw [MyNat.mul_comm]
  _ = m * l + n * l := by rw [MyNat.add_mul]
  _ = l * m + l * n := by simp [MyNat.mul_comm]

/-- 掛け算の結合法則 -/
theorem MyNat.mul_assoc (l m n : MyNat) : (l * m) * n = l * (m * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [MyNat.mul_add, ih]

-- 掛け算の結合法則を登録する
instance : Std.Associative (α := MyNat) (· * ·) where
  assoc := MyNat.mul_assoc

-- 掛け算の交換法則を登録する
instance : Std.Commutative (α := MyNat) (· * ·) where
  comm := MyNat.mul_comm

example (m n : MyNat) : m * n * n * m = m * m * n * n := by
  ac_rfl

example (m n : MyNat) : (m + n) * (m + n) = m * m + 2 * m * n + n * n := calc
  _ = (m + n) * m + (m + n) * n := by rw [MyNat.mul_add]
  _ = m * m + n * m + (m * n + n * n) := by simp [MyNat.add_mul]
  _ = m * m + (m * n + m * n) + n * n := by ac_rfl
  _ = m * m + ((m + m) * n) + n * n := by rw [MyNat.add_mul]
  _ = m * m + ((1 * m + 1 * m) * n) + n * n := by rw [MyNat.one_mul]
  _ = m * m + ((1 + 1) * m * n) + n * n := by rw [← MyNat.add_mul]
  _ = m * m + (2 * m * n) + n * n := by rfl
  _ = m * m + 2 * m * n + n * n := by rw [MyNat.add_assoc]
