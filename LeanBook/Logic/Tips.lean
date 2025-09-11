/--- 三重否定の簡略化 -/
example (P : Prop) : ¬¬¬ P → ¬ P := by
  -- ¬¬¬ P と P を仮定する
  intro hn3p hp

  -- ここで ¬¬ P が成り立つ
  have hn2p : ¬¬ P := by
    -- ¬ P を仮定する
    intro hnp
    -- 仮定の P と矛盾
    contradiction

  -- ¬¬ P と ¬¬¬ P が同時に成り立つので矛盾
  contradiction

/-- have で示す証明の名前は省略可能 -/
example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp

  have : ¬¬ P := by
    intro hnp
    contradiction

  contradiction

/-- 排中律の二重否定 -/
example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  intro h

  -- ここで、¬ P を示せば十分である
  suffices hyp : ¬ P from by
    have : P ∨ ¬ P := by
      right
      exact hyp
    contradiction

  -- 以下、 ¬ P を示す
  guard_target =ₛ ¬ P

  intro hp

  have : P ∨ ¬ P := by
    left
    exact hp

  contradiction

/-- exact tactic でライブラリを検索する -/
example (P : Prop) : (P → True) ↔ True := by
  exact?

example (P : Prop) : (True → P) ↔ P := by
  exact?

/-- show .. from 構文で一時的な補題を示す -/
example (P Q : Prop) (h : ¬ P ↔ Q) : (P → False) ↔ Q := by
  rw [show (P → False) ↔ ¬ P from by rfl]
  rw [h]

/-- 練習問題 -/
example (P : Prop) : ¬ (P ↔ ¬ P) := by
  exact iff_not_self
