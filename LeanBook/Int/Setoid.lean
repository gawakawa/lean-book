import LeanBook.NatOrder.DecidableOrd

/-- 2 次元平面 -/
structure Point where
  x : Int
  y : Int

#check { x := 1, y := 2 : Point }
#check Point.mk
#check Point.mk 1 2
#check Point.x
#check Point.y
#eval
  let p : Point := { x := 1, y := 2 }
  p.x

/-- 同値ならば反射的である -/
example {α : Type} (r : α → α → Prop) (h : Equivalence r) : ∀ x, r x x := by
  exact h.refl

/-- どんな型 α に対しても r x y := x = y なる二項関係 r を定義すると必ず同値関係になる -/
example {α : Type} : Equivalence (fun x y : α => x = y) := by
  constructor
  
  -- まず反射律を示す
  case refl =>
    intro x
    rfl

  -- 次に対称律を示す
  case symm =>
    intro x y h
    rw [h]

  -- 最後に推移律を示す
  case trans =>
    intro x y z hxy hyz
    rw [hxy, hyz]

example {α : Type} (sr : Setoid α) (x y : α) : sr.r x y = (x ≈ y) := by
  rfl

/-- 任意の要素に対して成り立つような二項関係は同値関係である -/
example {α : Type} : Equivalence (fun _x _y : α => True) := by
  constructor
  case refl =>
    intro x
    trivial
  case symm =>
    intro x y
    trivial
  case trans =>
    intro x y z
    trivial
