variable {α : Type} {a₁ a₂ : α}

example (f : α → α) (h : a₁ = a₂) : f (f a₁) = f (f a₂) := by
  grind

set_option trace.grind.assert true in
set_option trace.grind.eqc true in
theorem easy_proof (P : Prop) (h : P) : P := by
  grind
#print axioms easy_proof

/-- 自然数上の広義の順序関係を再定義する -/
inductive Nat.myle (n : Nat) : Nat → Prop
  /-- ∀ n, n ≤ n -/
  | refl : Nat.myle n n
  /-- n ≤ m ならば n ≤ m + 1 -/
  | step {m : Nat} : Nat.myle n m → Nat.myle n (m + 1)

/-- myle を表す記号 -/
infix:50 "≤?" => Nat.myle

attribute [grind →] Nat.myle.step

variable {m n a b k : Nat}

/-- 推移律 -/
theorem Nat.myle_trans (hnm : n ≤? m) (hmk : m ≤? k) : n ≤? k := by
  induction hmk with grind

/-- 群 -/
class Group (G : Type) [One G] [Mul G] [Inv G] where
  /-- 単位元を右から掛けても変わらない -/
  mul_one : ∀ g : G, g * 1 = g
  /-- 単位元を左から掛けても変わらない -/
  one_mul : ∀ g : G, 1 * g = g
  /-- 元と逆元を掛けると単位元になる -/
  mul_inv : ∀ g : G, g * g⁻¹ = 1
  /-- 逆元と元を掛けると単位元になる -/
  inv_mul : ∀ g : G, g⁻¹ * g = 1
  /-- 掛け算は結合的である -/
  mul_assoc : ∀ g₁ g₂ g₃ : G, g₁ * (g₂ * g₃) = (g₁ * g₂) * g₃

variable {G : Type} [One G] [Mul G] [Inv G] [Group G]

attribute [grind =>]
  Group.mul_one Group.one_mul
  Group.mul_inv Group.inv_mul Group.mul_assoc

@[grind =>]
theorem mul_right_inv {g h : G} (hy : g * h = 1) : h = g⁻¹ := calc
  _ = 1 * h := by grind
  _ = g⁻¹ := by grind

theorem inv_inv (g : G) : g⁻¹⁻¹ = g := by
  grind
