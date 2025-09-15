#check Classical.em

#print axioms Classical.em

#check Classical.choice

/-- 関数の全射性 -/
def Surjective {X Y : Type} (f : X → Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y

/-- 恒等関数は全射 -/
example : Surjective (fun x : Nat => x) := by
  intro y
  exists y

variable {X Y : Type}

/-- 全射であるような関数 f : X → Y に対して、その右逆関数 g : Y → X を返すような高階関数 -/
noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
  -- y : Y が与えられたとする
  intro y

  -- f は全射なので {x // f x = y} は空ではない
  have : Nonempty {x // f x = y} := by
    let ⟨x, hx⟩ := hf y
    exact ⟨⟨x, hx⟩⟩

  -- 選択原理を用いて f x = y なる x : X を構成する
  have x := Classical.choice this
  exact x.val

/-- 対偶が元の命題と同値であることを認めれば、二重否定の除去が導ける -/
theorem double_negation_of_contra_equiv (P : Prop)
    (contra_equiv : ∀ (P Q : Prop), (¬ P → ¬ Q) ↔ (Q → P)) : ¬¬ P → P := by
  -- ¬¬ P を仮定する
  intro h2np

  -- 対偶の同値性を ¬ P → ¬ True に適用
  have h1 : (¬ P → ¬ True) ↔ (True →  P) := contra_equiv P True

  -- 仮定 ¬¬ P より ¬ P → ¬ True が示せる
  have h2 : ¬ P → ¬ True := by
    intro hnp
    rw [not_true_eq_false]
    exact h2np hnp

  -- h1 に h2 を適用することで True → P 
  -- これは恒真なので示せた
  exact h1.mp h2 trivial

-- Classical.choice に依存していないことの確認
#print axioms double_negation_of_contra_equiv
