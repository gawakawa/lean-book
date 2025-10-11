import LeanBook.NatOrder.DecidableOrd

/-- 自然数を 2 つペアにしたもの
(a, b) ↦ a - b という対応で PreInt の項を構成する -/
abbrev PreInt := MyNat × MyNat

/-- PreInt の重複 (e,g, (0, 1) と (1, 2)) をなくすために
PreInt 上の二項関係 x₁ - y₁ = x₂ - y₂ を定義する -/
def PreInt.r (m n : PreInt) : Prop :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => m₁ + n₂ = m₂ + n₁

/-- 反射律 -/
theorem PreInt.r.refl : ∀ (m : PreInt), r m m := by
  intro (m₁, m₂)
  dsimp [r]
  ac_rfl

/-- 対称律 -/
theorem PreInt.r.symm: ∀ {m n : PreInt}, r m n → r n m := by
  intro (m₁, m₂) (n₁, n₂) h
  dsimp [r] at *
  have : n₁ + m₂ = n₂ + m₁ := calc
    _ = m₂ + n₁ := by ac_rfl
    _ = m₁ + n₂ := by rw [← h]
    _ = n₂ + m₁ := by ac_rfl
  exact this

/-- 推移律 -/
theorem PreInt.r.trans: ∀ {l m n : PreInt}, r l m → r m n → r l n := by
  intro (l₁, l₂) (m₁, m₂) (n₁, n₂) hlm hmn
  dsimp [r] at *
  have : m₁ + (l₁ + n₂) = m₁ + (l₂ + n₁) := calc
    _ = m₁ + n₂ + l₁ := by ac_rfl
    _ = m₂ + n₁ + l₁ := by rw [hmn]
    _ = l₁ + m₂ + n₁ := by ac_rfl
    _ = l₂ + m₁ + n₁ := by rw [hlm]
    _ = m₁ + (l₂ + n₁) := by ac_rfl
  simp_all

/-- PreInt.r は同値関係 -/
theorem PreInt.r.equiv : Equivalence r :=
  { refl := r.refl, symm := r.symm, trans := r.trans }

/-- PreInt 上の同値関係 -/
@[instance] def PreInt.sr : Setoid PreInt := ⟨r, r.equiv⟩

/-- MyNat × MyNat を同値関係で割ることで構成した整数 -/
abbrev MyInt := Quotient PreInt.sr

#check
  let a : PreInt := (1, 3)
  (Quotient.mk PreInt.sr a : MyInt)

#check
  let a : PreInt := (1, 3)
  Quotient.mk _ a

/-- 同値類を表す記法 -/
notation:arg (priority := low) "〚" a "〛" => Quotient.mk _ a

#check (〚(1, 3)〛 : MyInt)

def MyInt.ofNat (n : Nat) : MyInt := 〚(MyNat.ofNat n, 0)〛

instance {n : Nat} : OfNat MyInt n where
  ofNat := MyInt.ofNat n

#check (4 : MyInt)

#check_failure (-4 : MyInt)

def PreInt.neg : PreInt → MyInt
  | (m, n) => 〚(n, m)〛

@[notation_simp]
theorem MyInt.sr_def (m n : PreInt) : m ≈ n ↔ m.1 + n.2 = m.2 + n.1 := by
  rfl

def MyInt.neg : MyInt → MyInt := Quotient.lift PreInt.neg <| by
  -- PreInt.neg が同値関係を保つことを示したい
  -- (a₁, a₂) : PreInt と (b₁, b₂) : PreInt が同値だと仮定する
  intro (a₁, a₂) (b₁, b₂) hab

  -- このとき neg (a₁, a₂) = neg (b₁, b₂) を示せばよいのだが
  -- 商空間における neg の定義により (a₂, a₁) ≈ (b₂, a₂) を示せばよい
  suffices (a₂, a₁) ≈ (b₂, b₁) from by
    dsimp [PreInt.neg]
    rw [Quotient.sound]
    assumption

  -- しかしこれは同値性の定義と仮定より明らか
  notation_simp at *
  simp_all

instance : Neg MyInt where
  neg := MyInt.neg

@[simp]
theorem MyInt.neg_def (x y : MyNat) : - 〚(x, y)〛 = (〚(y, x)〛 : MyInt) := by
  dsimp [Neg.neg, MyInt.neg, PreInt.neg]
  rfl

-- マイナス記号が使えるようになった
#check (-4 : MyInt)

-- 生のままだと使えない
#check_failure -4

#check Setoid

-- r は α 上の二項関係とする
variable {α : Type} {r : α → α → Prop}

private theorem Ex.symm (refl : ∀ x, r x x) (h : ∀ x y z, r x y → r y z → r z x)
    : ∀ {x y : α}, r x y → r y x := by
  intro x y hxy
  have hxx : r x x := by exact refl x
  exact h x x y hxx hxy

private theorem Ex.equiv (refl : ∀ x, r x x)
    (h : ∀ x y z, r x y → r y z → r z x) : Equivalence r := by
  constructor

  case refl =>
    apply refl

  case symm =>
    exact Ex.symm refl h

  case trans =>
    intro x y z hxy hyz
    have hzx : r z x := by exact h x y z hxy hyz
    exact Ex.symm refl h hzx
