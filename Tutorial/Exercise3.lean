variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h: p ∨ q =>
     show q ∨ p
     from (Or.elim h
      (fun hp : p =>
       show q ∨ p from (Or.intro_right q hp))
      (fun hq : q =>
       show q ∨ p from (Or.intro_left p hq))))
    (fun h: q ∨ p =>
      show p ∨ q
      from (Or.elim h
        (fun hq : q =>
         show p ∨ q from (Or.intro_right p hq))
        (fun hp : p =>
         show p ∨ q from (Or.intro_left q hp))))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
     have hp : p := And.left (And.left h)
     have hq : q := And.right (And.left h)
     have hr : r := And.right h
     show p ∧ (q ∧ r)
     from (And.intro hp (And.intro hq hr)))
    (fun h : p ∧ (q ∧ r) =>
     have hp : p := And.left h
     have hq : q := And.left (And.right h)
     have hr : r := And.right (And.right h)
     show (p ∧ q) ∧ r
     from (And.intro (And.intro hp hq) hr))
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
