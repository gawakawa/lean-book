import LeanBook.NatOrder.StrictOrder
import LeanBook.NatOrder.NotationSimpTag

theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  rfl

section
  /- ## simp で展開するテスト -/

  -- この section の中でのみ simp に登録する 
  attribute [local simp] MyNat.lt_def

  example (m n : MyNat) : m < n := by
    simp
    guard_target =ₛ m + 1 ≤ n
    sorry

end

section

open Lean Parser Tactic

/-- + や ≤ など演算子や記法を定義に展開する -/
syntax "notation_simp" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp only [notation_simp, $args,*] $[at $location]?)

end

-- < の定義を展開する定理に [notation_simp] 属性を付与する
attribute [notation_simp] MyNat.lt_def

example (m n : MyNat) : m < n := by
  notation_simp
  guard_target =ₛ m + 1 ≤ n
  sorry

example (m n : MyNat) (h : m < n) : m + 1 ≤ n := by
  notation_simp at *
  assumption

example (m n : MyNat) : m < n := by
  -- simp の挙動には変化がない
  fail_if_success simp
  sorry

section
open Lean Parser Tactic

/-- + や ≤ など演算子や記法を定義に展開する -/
syntax "notation_simp?" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)
end

-- 展開に使用された定義を教えてくれる
example (m n : MyNat) : m < n := by
  notation_simp?
  sorry

example (a b : MyNat) (h1 : a < b) (h2 : b < a) : False := by
  notation_simp at *
  have : a + 1 ≤ b + 1 := by apply MyNat.le_step h1
  have : a + 1 ≤ a := by apply MyNat.le_trans this h2
  exact MyNat.not_succ_le_self a this
