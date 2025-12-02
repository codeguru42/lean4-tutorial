variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => And.intro h.right h.left)
    (fun h : q ∧ p => And.intro h.right h.left)
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h: p ∨ q => (h.elim
      (fun hp : p => Or.inr hp)
      (fun hq : q => Or.inl hq)))
    (fun h: q ∨ p => (h.elim
        (fun hq : q => Or.inr hq)
        (fun hp : p => Or.inl hp)))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r => And.intro h.left.left (And.intro h.left.right h.right))
    (fun h : p ∧ (q ∧ r) => And.intro (And.intro h.left h.right.left) h.right.right)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r => h.elim
      (fun hpq : p ∨ q => hpq.elim
        (fun hp : p => Or.inl hp)
        (fun hq : q => Or.inr (Or.inl hq)))
      (fun hr : r => (Or.inr (Or.inr hr))))
    (fun h : p ∨ (q ∨ r) => (h.elim
      (fun hp : p => Or.inl (Or.inl hp))
      (fun hqr : q ∨ r => hqr.elim
        (fun hq : q => Or.inl (Or.inr hq))
        (fun hr : r => Or.inr hr))))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) => h.right.elim
      (fun hq : q => Or.inl (And.intro h.left hq))
      (fun hr : r => Or.inr (And.intro h.left hr)))
    (fun h : (p ∧ q) ∨ (p ∧ r) => h.elim
     (fun hpq : (p ∧ q) => And.intro hpq.left (Or.inl hpq.right))
     (fun hpr : (p ∧ r) => And.intro hpr.left (Or.inr hpr.right)))
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
