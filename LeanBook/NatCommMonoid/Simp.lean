import LeanBook.NatCommMonoid.Induction

example (n : MyNat) : 0 + (n + 0) = n := by
  -- 最初は simp で証明できない
  fail_if_success simp

  -- 明示的に rw で証明する
  rw [MyNat.add_zero, MyNat.zero_add]

attribute [simp] MyNat.add_zero MyNat.zero_add

example (n : MyNat) : 0 + (n + 0) = n := by
  simp

/-- MyNat において 0 は zero だと解釈される -/
theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := by
  rfl

example : MyNat.zero = 0 := by
  simp [MyNat.ctor_eq_zero]

-- MyNat.add_succ を simp tactic に登録する
attribute [simp] MyNat.add_succ

example (m n : MyNat) (h : m + n + 0 = n + m) : m + n = n + m := by
  simp at h
  guard_hyp h : m + n = n + m
  rw [h]

-- simp at * でローカルコンテキストのすべての仮定とゴールを単純化する
example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp at *

  guard_hyp h : m = n
  guard_target =ₛ m = n

  rw [h]

-- simp_all でローカルコンテキストのすべての仮定とゴールを
-- これ以上単純化できなくなるまで単純化する
example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp_all

-- @[simp] タグで証明された命題を自動的に simp に登録する
/-- 左のオペランドについた .succ は外側に出せる -/
@[simp] theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [ih]

example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp? [ih]

-- calc で途中経過を明示する
example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih => calc
    _ = (m.succ + n').succ := by rw [MyNat.add_succ]
    _ = (m + n').succ.succ := by rw [MyNat.succ_add]
    _ = (m + n'.succ).succ := by rw [MyNat.add_succ] 

example (n : MyNat) : 1 + n = n + 1 := calc
  _ = .succ 0 + n := by rfl -- 1 は定義から .succ 0 に等しい 
  _ = .succ (0 + n) := by rw [MyNat.succ_add] -- .succ を外に出す
  _ = .succ n := by rw [MyNat.zero_add] -- 0 + n = n を用いて単純化
  _ = n + 1 := by rfl -- n + 1 は定義から .succ n に等しい

example (n : MyNat) : 2 + n = n + 2 := calc
  _ = .succ (.succ 0) + n := by rfl
  _ = .succ (.succ 0 + n) := by rw [MyNat.succ_add]
  _ = .succ (.succ (0 + n)) := by rw [MyNat.succ_add]
  _ = .succ (.succ n) := by rw [MyNat.zero_add]
  _ = .succ (.succ (n + 0)) := by rw [MyNat.add_zero]
  _ = .succ (n + .succ 0) := by rw [MyNat.add_succ] 
  _ = (n + .succ (.succ 0)) := by rw [← MyNat.add_succ]
  _ = (n + 2) := by rfl
