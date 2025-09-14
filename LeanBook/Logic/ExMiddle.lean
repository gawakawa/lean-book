/-- 二重否定の除去 -/
example (P : Prop) : ¬¬ P → P := by
  -- ¬¬ P だと仮定する
  intro hn2p

  -- 排中律より P ∨ ¬ P が成り立つ
  by_cases h : P

  -- P が成り立つ場合は、自明
  · exact h

  -- P が成り立たない場合、 ¬¬ P と矛盾
  · contradiction

/-- ドモルガンの法則 -/
example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  · intro hnpq
    by_cases hp : P
    · right
      intro hq
      exact hnpq ⟨hp, hq⟩
    · left
      exact hp
  · intro hnpnq hpq
    cases hnpnq with
    | inl hnp =>
      exact hnp hpq.left
    | inr hnq =>
      exact hnq hpq.right

/-- 対偶が元の命題と同値であること -/
example (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor
  · intro hpq hnq hp
    exact hnq $ hpq hp
  · intro hpq hp
    by_cases h : Q
    · exact h
    · exfalso
      exact hpq h hp
