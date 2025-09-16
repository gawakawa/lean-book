import LeanBook.NatCommMonoid.TypeClass

set_option pp.fieldNotation.generalized false in

/-- 右のオペランドについた .succ は外側に出せる -/
theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by
  rfl

/-- 0 を左から足しても変わらない -/
theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  -- n についての帰納法で証明する
  induction n with

  -- n = 0 のケース
  | zero =>
    guard_target =ₛ 0 + MyNat.zero = MyNat.zero
    rfl

  -- n = succ n' のケース
  | succ n' ih =>
    guard_target =ₛ 0 + MyNat.succ n' = MyNat.succ n'

    -- 帰納法の仮定 ih が手に入る
    guard_hyp ih : 0 + n' = n'

    -- 帰納法の仮定 0 + n' = n' を使いたいので、
    -- 0 + MyNat.succ n' を MyNat.succ (0 + n') に変形する
    rw [MyNat.add_succ]

    -- 帰納法の仮定より、示せた
    rw [ih]

#reduce fun (n : MyNat) => n + 0

#reduce fun (n : MyNat) => 0 + n

/-- 0 を右から足しても変わらない -/
theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [MyNat.add_zero]

/-- add_zero の等式の順序が逆のバージョン -/
theorem MyNat.add_zero_rev (n : MyNat) : n = n + 0 := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [← MyNat.add_zero_rev]

example (m n : MyNat) (h : m + 0 = n) : n + m = m + n := by
  -- 仮定の h を簡略化して m = n を得る
  rw [MyNat.add_zero] at h
  rw [h]

example (n : MyNat) : 1 + n = .succ n := by
  induction n with
  | zero =>
    rfl
  | succ n' ih =>
    rw [MyNat.add_succ]
    rw [ih]
