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
     from (h.elim
      (fun hp : p =>
       show q ∨ p from Or.inr hp)
      (fun hq : q =>
       show q ∨ p from Or.inl hq)))
    (fun h: q ∨ p =>
      show p ∨ q
      from (h.elim
        (fun hq : q =>
         show p ∨ q from Or.inr hq)
        (fun hp : p =>
         show p ∨ q from Or.inl hp)))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
     show p ∧ (q ∧ r)
     from And.intro h.left.left (And.intro h.left.right h.right))
    (fun h : p ∧ (q ∧ r) =>
     show (p ∧ q) ∧ r
     from And.intro (And.intro h.left h.right.left) h.right.right)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
     show p ∨ (q ∨ r)
     from h.elim
      (fun hpq : p ∨ q =>
       show p ∨ (q ∨ r)
       from hpq.elim
        (fun hp : p =>
         show p ∨ (q ∨ r) from Or.inl hp)
        (fun hq : q =>
         show p ∨ (q ∨ r) from Or.inr (Or.inl hq)))
      (fun hr : r =>
       show p ∨ (q ∨ r)
       from (Or.inr (Or.inr hr))))
    (fun h : p ∨ (q ∨ r) =>
     show (p ∨ q) ∨ r
     from (h.elim
      (fun hp : p =>
       show (p ∨ q) ∨ r
       from Or.inl (Or.inl hp))
      (fun hqr : q ∨ r =>
       show (p ∨ q) ∨ r
       from hqr.elim
        (fun hq : q =>
         show (p ∨ q) ∨ r
         from Or.inl (Or.inr hq))
        (fun hr : r =>
         show (p ∨ q) ∨ r
         from Or.inr hr))))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
     show (p ∧ q) ∨ (p ∧ r)
     from h.right.elim
      (fun hq : q => Or.inl (And.intro h.left hq))
      (fun hr : r => Or.inr (And.intro h.left hr)))
    (fun h : (p ∧ q) ∨ (p ∧ r) => h.elim
     (fun hpq : (p ∧ q) =>
      show p ∧ (q ∨ r)
      from And.intro hpq.left (Or.inl hpq.right))
     (fun hpr : (p ∧ r) =>
      show p ∧ (q ∨ r)
      from And.intro hpr.left (Or.inr hpr.right)))
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) => h.elim
     (fun hp : p => And.intro (Or.inl hp) (Or.inl hp))
     (fun hqr : q ∧ r => And.intro (Or.inr hqr.left) (Or.inr hqr.right)))
    (fun h : (p ∨ q) ∧ (p ∨ r) => h.left.elim
     (fun hp : p => Or.inl hp)
     (fun hq : q => h.right.elim
      (fun hp : p => Or.inl hp)
      (fun hr : r => Or.inr (And.intro hq hr))))

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
