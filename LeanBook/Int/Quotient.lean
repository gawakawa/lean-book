-- 同値類をとる
section
  variable {α : Type} (sr : Setoid α)
  #check (Quotient.mk sr : α → Quotient sr)
end

-- 同値類の代表元をとる
section
  variable {α : Type} (sr : Setoid α)
  example (a : Quotient sr) : True := by
    induction a using Quotient.inductionOn with
    | h x =>
      guard_hyp x : α
      trivial
end

section
  /- ## 商への関数を作る -/
  variable {α β : Type} (sr : Setoid α)
  variable (f : β → α)

  -- 自然な写像 α → Quotient sr と f を合成することで商への関数が得られる
  #check (Quotient.mk sr ∘ f : β → Quotient sr)
end

section
  /- ## 商からの関数を作る -/
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)

  #check (Quotient.lift f h : Quotient sr → β)
end

section
  /- ## Quotient.lift は元の関数の値を変えない -/
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)

  example : ∀ x, (Quotient.lift f h) (Quotient.mk sr x) = f x := by
    intro x
    rfl
end

section
  /- ## 同値なら商へ送って等しい -/
  variable {α : Type} (sr : Setoid α)
  variable (x y : α) (h : x ≈ y)

  example : Quotient.mk sr x = Quotient.mk sr y := by
    apply Quotient.sound
    exact h
end

section
  /- ## 商に送って等しいなら同値 -/
  variable {α : Type} (sr : Setoid α)
  variable (x y : α)

  example (h : Quotient.mk sr x = Quotient.mk sr y) : x ≈ y := by
    exact Quotient.exact h

end

/-- β 上の二項関係 r : β → β → Prop と関数 f : α → β があるとき
α 上の二項関係を fun x y => r (f x) (f y) で定義できる -/
private def Rel.comap {α β : Type} (f : α → β) (r : β → β → Prop) : α → α → Prop :=
fun x y => r (f x) (f y)

/-- β 上の同値関係 sr : Setoid β と関数 f : α → β があるとき
Rel.comap f (· ≈ ·) も同値関係になる -/
private def Setoid.comap {α β : Type} (f : α → β) (sr : Setoid β)
    : Setoid α where
  r := Rel.comap f (· ≈ ·)
  iseqv := by
    constructor <;> dsimp [Rel.comap]

    case refl =>
      intro x
      apply Setoid.iseqv.refl

    case symm =>
      intro x y
      apply Setoid.iseqv.symm

    case trans =>
      intro x y z
      apply Setoid.iseqv.trans
