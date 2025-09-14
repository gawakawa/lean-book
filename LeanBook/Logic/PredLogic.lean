/-- 自然数上の述語 -/
def P (n : Nat) : Prop := n = n

/-- ∀ の導入を intro で行う -/
example : ∀ a : Nat, P a := by
  -- x : Nat が任意に与えられたとする
  intro x

  -- P を展開すれば明らか
  dsimp [P]

/-- ∀ の除去を exact で行う -/
example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  exact h 0

def even (n : Nat) : Prop := ∃ m : Nat, n = m + m

/-- ∃ の導入を exists で行う -/
example : even 4 := by
  exists 2

/-- ∃ の除去を obtain で行う -/
example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x)
    : ∃ x : α, Q x := by
  -- 仮定 h が存在を主張している y を取り出す
  obtain ⟨y, hy⟩ := h

  -- y が求めるものである
  exists y

  exact hy.right

/-- 人間の集合 -/
opaque Human : Type

/-- 愛の関係 -/
opaque Love : Human → Human → Prop

@[inherit_doc] infix:50 "-♥->" => Love

/-- すべての人に愛されているアイドルが存在する -/
def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -♥-> idol

/-- 誰にでも好きな人の 1 人くらいいる -/
def EveryoneLovesSomeone : Prop := ∀ h : Human, ∃ tgt : Human, h -♥-> tgt

#check ∃ philan : Human, ∀ h : Human, philan -♥-> h

def PhilanExisits : Prop := ∃ philan : Human, ∀ h : Human, philan -♥-> h

#check ∀ h : Human, ∃ lover : Human, lover -♥-> h

def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -♥-> h

/-- 博愛主義者が存在するならば、すべての人は誰かに愛されている -/
example : PhilanExisits → EveryoneLoved := by
  -- 博愛主義者の存在を仮定する
  intro h

  -- 存在が主張されている博愛主義者を philan とする
  obtain ⟨philan, h⟩ := h

  -- このとき EveryoneLoved を示したい
  -- すなわち ∀ (h : Human), philan -♥-> h を示したい
  dsimp [EveryoneLoved]

  -- 任意に human : Human が与えられたと仮定する
  intro human

  -- ∃ lover, lover -♥-> human を示したい
  -- lover = philan とする
  exists philan

  -- なぜなら philan -♥-> human が成り立つから
  exact h human

/-- アイドルが存在するならば、すべての人は誰かを愛している -/
example : IdolExists → EveryoneLovesSomeone := by
  -- アイドルの存在を仮定する
  intro h

  -- 存在が仮定されているアイドルを idol とする
  obtain ⟨idol, h⟩ := h

  -- EveryoneLovesSomeone を示したい
  dsimp [EveryoneLovesSomeone]

  -- 任意に human : Human が与えられたと仮定する
  intro human

  -- ここで ∃ tgt, human -♥-> tgt を示したいが、
  -- tgt = idol とすればよい
  exists idol

  -- なぜなら human -♥-> idol が成り立つから
  exact h human
