/-- 自前で実装した自然数 -/
inductive MyNat where
  | zero
  | succ (n : MyNat)

/-- MyNat どうしの足し算 -/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n => succ (add m n)

/-- MyNat.add を足し算として登録する -/
instance : Add MyNat where
  add := MyNat.add

/-- Nat の項から対応する MyNat の項を得る -/
def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => MyNat.zero
  | n + 1 => MyNat.succ (MyNat.ofNat n)

/-- OfNat のインスタンスを実装する -/
@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

@[simp, grind =]
theorem MyNat.zero_eq_zero_lit : MyNat.zero = 0 := by
  rfl

@[simp, grind =]
theorem MyNat.succ_eq_add_one (n : MyNat) : .succ n = n + 1 := by
  rfl

/-- MyNat 用の帰納法の原理を書き直す -/
@[induction_eliminator]
def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n : MyNat) → motive n → motive (n + 1)) (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

/-- 0 を右から足しても変わらない -/
@[simp, grind =]
theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by rfl

/-- 右のオペランドについた .succ は外側に出せる -/
@[simp, grind =]
theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by
  rfl

/-- 右のオペランドについた (· + 1) は外側に出せる -/
@[grind =]
theorem MyNat.add_add_one (m n : MyNat) : m + (n + 1) = (m + n) + 1 := by
  rfl

/-- 0 を左から足しても変わらない -/
@[simp, grind =]
theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n with grind

/-- 左のオペランドについた .succ は外側に出せる -/
@[simp, grind =]
theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with grind

/-- 左のオペランドについた (· + 1) は外側に出せる -/
@[grind =]
theorem MyNat.add_one_add (m n : MyNat) : (m + 1) + n = (m + n) + 1 := by
  induction n with grind

/-- 足し算の交換法則 -/
@[grind _=_]
theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with grind

/-- 足し算の結合法則 -/
@[grind _=_]
theorem MyNat.add_assoc (l m n : MyNat) : l + m + n = l + (m + n) := by
  induction n with grind

/-- MyNat の足し算が結合法則を満たすことを登録する -/
instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc

/-- MyNat の足し算が交換法則を満たすことを登録する -/
instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm

/-- MyNat についての掛け算 -/
def MyNat.mul (m n : MyNat) : MyNat := 
  match n with
  | 0 => 0
  | n + 1 => MyNat.mul m n + m

/-- MyNat の掛け算を型クラス Mul のインスタンスにする -/
instance : Mul MyNat where
  mul := MyNat.mul

/-- 右から 0 を掛けても 0 -/
@[simp, grind =]
theorem MyNat.mul_zero (m : MyNat) : m * 0 = 0 := by
  rfl

/-- 右のオペランドにある · * 1 の消去 -/
@[grind _=_]
theorem MyNat.mul_add_one (m n : MyNat) : m * (n + 1) = m * n + m := by
  rfl

/-- 左から 0 を掛けても 0 -/
@[simp, grind =]
theorem MyNat.zero_mul (n : MyNat) : 0 * n = 0 := by
  induction n with grind

/-- 左のオペランドにある · + 1 の消去 -/
@[grind _=_]
theorem MyNat.add_one_mul (m n : MyNat) : (m + 1) * n = m * n + n := by
  induction n with grind

/-- 右から 1 を掛けても変わらない -/
@[simp, grind =]
theorem MyNat.mul_one (n : MyNat) : n * 1 = n := by
  induction n with grind

/-- 左から 1 を掛けても変わらない -/
@[simp, grind =]
theorem MyNat.one_mul (n : MyNat) : 1 * n = n := by
  induction n with grind

/-- 掛け算の交換法則 -/
@[grind =]
theorem MyNat.mul_comm (m n : MyNat) : m * n = n * m := by
  induction n with grind

/-- 右から掛けたときの分配法則 -/
@[grind _=_]
theorem MyNat.add_mul (l m n : MyNat) : (l + m) * n = l * n + m * n := by
  induction n with grind

/-- 左から掛けたときの分配法則 -/
@[grind _=_]
theorem MyNat.mul_add (l m n : MyNat) : l * (m + n) = l * m + l * n := by
  grind

/-- 掛け算の結合法則 -/
@[grind _=_]
theorem MyNat.mul_assoc (l m n : MyNat) : l * m * n = l * (m * n) := by
  induction n with grind

-- 掛け算の結合法則を登録する
instance : Std.Associative (α := MyNat) (· * ·) where
  assoc := MyNat.mul_assoc

-- 掛け算の交換法則を登録する
instance : Std.Commutative (α := MyNat) (· * ·) where
  comm := MyNat.mul_comm

variable {l m n : MyNat}

@[grind →]
theorem MyNat.add_one_right_cancel (h : l + 1 = n + 1) : l = n := by
  injection h

/-- 右から足す演算 (· + m) は単射 -/
@[grind →]
theorem MyNat.add_rght_cancel (h : l + m = n + m) : l = n := by
  induction m with grind

/-- 左から足す演算 (l + ·) は単射 -/
@[grind →]
theorem MyNat.add_left_cancel (h : l + m = l + n) : m = n := by
  grind
