variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro h.right h.left)
    (fun h : q ∧ p =>
     show p ∧ q from And.intro h.right h.left)
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
     show p ∧ (q ∧ r)
     from (And.intro h.left.left (And.intro h.left.right h.right)))
    (fun h : p ∧ (q ∧ r) =>
     show (p ∧ q) ∧ r
     from (And.intro (And.intro h.left h.right.left) h.right.right))
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
     show p ∨ (q ∨ r)
     from (Or.elim h
      (fun hpq : p ∨ q =>
       show p ∨ (q ∨ r)
       from (Or.elim hpq
        (fun hp : p =>
         show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) hp)
        (fun hq : q =>
         show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_left r hq))))
      (fun hr : r =>
       show p ∨ (q ∨ r)
       from (Or.intro_right p (Or.intro_right q hr)))))
    (fun h : p ∨ (q ∨ r) =>
     show (p ∨ q) ∨ r
     from (Or.elim h
      (fun hp : p =>
       show (p ∨ q) ∨ r
       from (Or.intro_left r (Or.intro_left q hp)))
      (fun hqr : q ∨ r =>
       show (p ∨ q) ∨ r
       from (Or.elim hqr
        (fun hq : q =>
         show (p ∨ q) ∨ r
         from (Or.intro_left r (Or.intro_right p hq)))
        (fun hr : r =>
         show (p ∨ q) ∨ r
         from (Or.intro_right (p ∨ q) hr))))))

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
