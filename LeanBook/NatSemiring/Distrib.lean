import LeanBook.NatSemiring.Mult

/-- 数値リテラルを 1 + 1 + … + 1 に分解するための補題 -/
theorem unfoldNatLit (x : Nat)
    : (OfNat.ofNat (x + 2) : MyNat) = (OfNat.ofNat (x + 1) : MyNat) + 1 :=
  rfl

/-- 自然数を 1 + 1 + … + 1 に分解する -/
macro "expand_num" : tactic => `(tactic| focus
  -- 標準の Nat の和を簡単な形にする
  try simp only [unfoldNatLit, Nat.reduceAdd]

  -- OfNat.ofNat を消す
  try dsimp only [OfNat.ofNat]
  try simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl,
  ]
)

/-- expand_num tactic のテスト -/
example (n : MyNat) : 3 * n = 2 * n + 1 * n := by
  expand_num
  guard_target =ₛ (1 + 1 + 1) * n = (1 + 1) * n + 1 * n
  simp only [MyNat.add_mul]

/-- 分配法則を適用して足し算を式の外側に持ってくる tactic -/
macro "distrib" : tactic => `(tactic| focus
  expand_num
  try simp only [
    MyNat.mul_add,
    MyNat.add_mul,
    MyNat.mul_zero,
    MyNat.zero_mul,
    MyNat.mul_one,
    MyNat.one_mul
  ]
  try ac_rfl
)

/-- distrib tactic のテスト -/
example (m n : MyNat) : (m + 4) * n + n = m * n + 5 * n := by
  distrib

/-- simp で progress がない場合にエラーを起こさない -/
example (m n : MyNat) : m * n + n * n = (m + n) * n := by
  distrib

/-- st = n² + 8n + 16 を満たす自然数 s, t が存在する -/
example (n : MyNat) : ∃ s t : MyNat, s * t = n * n + 8 * n + 16 := by
  exists n + 4, n + 4
  distrib
