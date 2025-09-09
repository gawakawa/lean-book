-- 命題全体の型 
#check Prop

-- 命題の例
#check (1 + 1 = 3 : Prop)

-- 自由変数 n が含まれるのでこれは命題ではない ( 命題への関数 )
#check (fun n => n + 3 = 39 : Nat → Prop)

#check True
#check False

/-- True は無条件で示せる -/
example : True := by trivial

/-- 
仮定を使って証明する 
P が命題で、 h が P の証明であるとき、P は h を使えば示せる
-/
example (P : Prop) (h : P) : P := by
  exact h

/-- 仮定を使ってゴールを直接証明するタクティク -/
example (P : Prop) (h : P) : P := by
  assumption

/-- 矛盾からは何でも示せる -/
example (h : False) : 0 = 1 := by
  trivial

/-- -> は右結合 -/
example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

#eval True → True
#eval True → False
#eval False → True
#eval False → False

/-- apply tactic で含意を除去できる -/
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  apply hp

/-- exact で → を除去できる -/
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

/-- intro tactic で → を導入できる -/
example (P Q : Prop) (hq : Q) : P → Q := by
  intro hp
  exact hq

#eval ¬ True
#eval ¬ False

/-- 否定は含意で定義される -/
example (P : Prop) : (¬ P) = (P → False) := by
  rfl

/-- 
¬ P と P を同時に仮定すると矛盾する

P → False   P 
-------------- →E
    False
-/
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  exact hnp hp

/-- 対偶が元の命題と同値になることの片方のケース -/
example (P Q : Prop) (h : P → ¬ Q) : Q → ¬ P := by
  -- Goal が含意を含むので、 Q を仮定する
  intro hq

  -- Goal の ¬ P はまだ含意を含むので、P を仮定する
  intro hp

  -- 仮定 P → Q → False に hp, hq を適用して False を得る
  exact h hp hq

/-- 矛盾からは何でも示せることを示す tactic -/
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  contradiction

/-- 矛盾があるとき、証明のどの時点でもゴールを ⊢ False に置き換えられる -/
example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  -- 矛盾を示せばよい
  exfalso

  -- 爆発律
  contradiction

#eval True ↔ True
#eval True ↔ False
#eval False ↔ True
#eval False ↔ False

/-- 同値性を示すときは constructor tactic を使う -/
example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor

  -- → の証明
  case mp =>
    intro h
    exact h hq

  -- ← の証明
  case mpr =>
    intro hp hq
    exact hp

/-- <;> tactic の用法 -/ 
example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h

  case mp =>
    exact h hq

  case mpr =>
    intro hq
    exact h

/-- rw tactic で同値な命題を置き換える -/
example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- 仮定 P ↔ Q を使って、Goal を Q に置き換える
  rw [h]
  exact hq

/-- 同値な命題は等しい ( 命題外延性 ) -/
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]

#eval True ∧ True
#eval True ∧ False
#eval False ∧ True
#eval False ∧ False

/-- constructor tactic で ∧ を導入する -/
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

/-- .left と.right で ∧ を除去する -/
example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

/-- left tactic と right tactic で ∨ を導入する -/
example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

/-- cases tactic で ∨ を除去する -/
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

/-- 練習問題 -/
example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h
  intro hp
  cases h with
  | inl hnp =>
    exfalso
    contradiction
  | inr hq =>
    exact hq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor <;> intro h

  case mp =>
    constructor
    · intro hp
      apply h
      left
      exact hp
    · intro hq
      apply h
      right
      exact hq

  case mpr =>
    intro hpq
    cases hpq with
    | inl hp =>
      exact h.left hp
    | inr hq => 
      exact h.right hq
