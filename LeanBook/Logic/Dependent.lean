-- Lean では依存型を扱えるので
-- 項に依存する型を定義することができる
-- ここでは Nat.add_zero の型は n : Nat に依存している
#check Nat.add_zero

#check Nat.add_zero 0

#check Nat.add_zero 42

-- 依存関数型 (a : α) → β a
-- 返り値の型が入力値に依存する関数の型
#check (Nat.add_zero : (n : Nat) → n + 0 = n)

/-- 全称量化された命題を依存関数型で表現することができる -/
example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by
  rfl

set_option pp.foralls false in
#check (∀ n : Nat, n + 0 = n)

-- List α の型は要素数の情報を持たない
example : List Nat := [0, 1, 2, 3]
example : List Nat := [0, 1]

/-- 要素数の情報を含む連結リスト -/
inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons {n : Nat} (a : α) (v : Vect α n) : Vect α (n + 1)

example : Vect Nat 0 := Vect.nil
example : Vect Nat 1 := Vect.cons 42 Vect.nil

-- 依存ペア型 (a : α) × β a
-- 直積 (a : α) × (b : β) と異なり b の型 β が a に依存して良い
example : (α : Type) × α := ⟨Nat, 1⟩
example : (α : Type) × α := ⟨Bool, true⟩
example : (α : Type) × α := ⟨Prop, True⟩

example : List ((α : Type) × α) := [⟨Nat, 1⟩, ⟨Bool, true⟩, ⟨Prop, True⟩]

example : List ((α : Type) × α) := [⟨Nat, 42⟩, ⟨Bool, false⟩]

example : {α : Type} → {n : Nat} → 
    (a : α) → (v : Vect α n) → Vect α (n + 1) := Vect.cons
