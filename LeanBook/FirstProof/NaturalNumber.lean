/-- 帰納型として自然数を自前で定義 -/
inductive MyNat where
  | zero
  | succ (n : MyNat)

/-- 自作の自然数における 1 と 2 を定義 -/
def MyNat.one := MyNat.succ .zero
def MyNat.two := MyNat.succ .one

/-- MyNat どうしの足し算を定義 -/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n => succ (add m n)

/-- 1 + 1 = 2 の照明 -/
example : MyNat.add .one .one = .two := by
  rfl

/-- n + 0 = n の証明 -/
example (n : MyNat) : MyNat.add n .zero = n := by
  rfl
