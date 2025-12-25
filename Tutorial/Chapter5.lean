section
  section
    -- Prove the following identities, replacing the sorry placeholders with actual proofs.
    variable (p q r : Prop)

    -- commutativity of ∧ and ∨
    example : p ∧ q ↔ q ∧ p := by
      apply Iff.intro
      · intro h
        exact And.intro (And.right h) (And.left h)
      · intro h
        exact And.intro (And.right h) (And.left h)
    example : p ∨ q ↔ q ∨ p := by
      apply Iff.intro
      · intro h
        apply Or.elim h
        case left =>
          exact Or.inr
        case right =>
          exact Or.inl
      · intro h
        apply Or.elim h
        case left =>
          exact Or.inr
        case right =>
          exact Or.inl

    -- associativity of ∧ and ∨
    example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
      apply Iff.intro
      · intro h
        exact And.intro h.left.left (And.intro h.left.right h.right)
      · intro h
        exact And.intro (And.intro h.left h.right.left) h.right.right
    example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
      apply Iff.intro
      · intro h
        cases h with
        | inl hpq =>
          cases hpq with
          | inl hp => exact Or.inl hp
          | inr hq => exact Or.inr (Or.inl hq)
        | inr hr => exact Or.inr (Or.inr hr)
      · intro h
        cases h with
        | inl hp => exact Or.inl (Or.inl hp)
        | inr hqr =>
          cases hqr with
          | inl hq => exact Or.inl (Or.inr hq)
          | inr hr => exact Or.inr hr

    -- distributivity
    example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
      apply Iff.intro
      · intro h
        cases h.right with
        | inl hq => exact Or.inl (And.intro h.left hq)
        | inr hr => exact Or.inr (And.intro h.left hr)
      · intro h
        cases h with
        | inl hpq => exact And.intro hpq.left (Or.inl hpq.right)
        | inr hpr => exact And.intro hpr.left (Or.inr hpr.right)
    example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
      apply Iff.intro
      · intro h
        cases h with
        | inl hp => exact And.intro (Or.inl hp) (Or.inl hp)
        | inr hqr => exact And.intro (Or.inr hqr.left) (Or.inr hqr.right)
      · intro h
        cases h.left with
        | inl hp => exact Or.inl hp
        | inr hq =>
          cases h.right with
          | inl hp => exact Or.inl hp
          | inr hr => exact Or.inr (And.intro hq hr)

    -- other properties
    example : (p → (q → r)) ↔ (p ∧ q → r) := by
      apply Iff.intro
      · intro h hpq
        exact h hpq.left hpq.right
      · intro h hp hq
        exact h (And.intro hp hq)
    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
      apply Iff.intro
      · intro h
        apply And.intro
        · intro hp
          exact h (Or.inl hp)
        · intro hq
          exact h (Or.inr hq)
      · intro h hpq
        cases hpq with
        | inl hp => exact h.left hp
        | inr hq => exact h.right hq
    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
      apply Iff.intro
      · intro h
        apply And.intro
        · intro hp
          exact h (Or.inl hp)
        · intro hq
          exact h (Or.inr hq)
      · intro h hpq
        cases hpq with
        | inl hp => exact h.left hp
        | inr hq => exact h.right hq
    example : ¬p ∨ ¬q → ¬(p ∧ q) := by
      intro h hpq
      cases h with
      | inl hnp => exact hnp hpq.left
      | inr hnq => exact hnq hpq.right
    example : ¬(p ∧ ¬p) := by
      intro h
      exact h.right h.left
    example : p ∧ ¬q → ¬(p → q) := by
      intro h hpq
      exact h.right (hpq h.left)
    example : ¬p → (p → q) := by
      intro hnp hp
      exact absurd hp hnp
    example : (¬p ∨ q) → (p → q) := by
      intro h hp
      cases h with
      | inl hnp => exact absurd hp hnp
      | inr hq => exact hq
    example : p ∨ False ↔ p := by
      apply Iff.intro
      · intro h
        cases h with
        | inl hp => exact hp
        | inr hf => exact hf.elim
      · intro h
        exact Or.inl h
    example : p ∧ False ↔ False := by
      apply Iff.intro
      · intro h
        exact h.right
      · intro h
        exact h.elim
    example : (p → q) → (¬q → ¬p) := by
      intro h hnq hp
      exact hnq (h hp)
  end

  section
    -- Prove the following identities, replacing the sorry placeholders with actual proofs. These require classical reasoning.

    open Classical

    variable (p q r : Prop)

    example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
      intro h
      cases em q with
      | inl hq =>
        apply Or.inl
        intro hp
        exact hq
      | inr hnq =>
        apply Or.inr
        intro hp
        apply (h hp).elim
        · intro hq
          exact absurd hq hnq
        · intro hr
          exact hr
    example : ¬(p ∧ q) → ¬p ∨ ¬q := by
      intro h
      cases (em p) with
      | inl hp =>
        cases (em q) with
        | inl hq =>
          exact absurd (And.intro hp hq) h
        | inr hnq =>
          exact Or.inr hnq
      | inr hnp =>
        exact Or.inl hnp
    example : ¬(p → q) → p ∧ ¬q := by
      intro h
      apply And.intro
      · by_cases hp : p
        · exact hp
        · exfalso
          apply h
          intro hp'
          contradiction
      · intro hq
        apply h
        intro _
        exact hq
    example : (p → q) → (¬p ∨ q) := by
      intro h
      by_cases hp : p
      · exact Or.inr (h hp)
      · exact Or.inl hp
    example : (¬q → ¬p) → (p → q) := by
      intro h hp
      by_cases hq : q
      · exact hq
      · exact absurd hp (h hq)
    example : p ∨ ¬p := sorry
    example : (((p → q) → p) → p) := sorry

  end

  -- Prove ¬(p ↔ ¬p) without using classical logic.
end

section
  section
    -- 1. Prove these equivalences:
    variable (α : Type) (p q : α → Prop)

    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
  end

  section
    /-
    2. It is often possible to bring a component of a formula outside
    a universal quantifier, when it does not depend on the quantified
    variable. Try proving these (one direction of the second of these
    requires classical logic):
    -/

    variable (α : Type) (p q : α → Prop)
    variable (r : Prop)

    example : α → ((∀ x : α, r) ↔ r) := sorry
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
  end

  section
    /-
    3. Consider the “barber paradox,” that is, the claim that in a
    certain town there is a (male) barber that shaves all and
    only the men who do not shave themselves. Prove that this is
    a contradiction:
    -/

    variable (men : Type) (barber : men)
    variable (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
      sorry
  end

  section
    /-
    4. Remember that, without any parameters, an expression of type
    Prop is just an assertion. Fill in the definitions of prime
    and Fermat_prime below, and construct each of the given
    assertions. For example, you can say that there are infinitely
    many primes by asserting that for every natural number n,
    there is a prime number greater than n. Goldbach's weak
    conjecture states that every odd number greater than 5 is
    the sum of three primes. Look up the definition of a Fermat
    prime or any of the other statements, if necessary.
    -/

    def even (n : Nat) : Prop := sorry

    def prime (n : Nat) : Prop := sorry

    def infinitely_many_primes : Prop := sorry

    def Fermat_prime (n : Nat) : Prop := sorry

    def infinitely_many_Fermat_primes : Prop := sorry

    def goldbach_conjecture : Prop := sorry

    def Goldbach's_weak_conjecture : Prop := sorry

    def Fermat's_last_theorem : Prop := sorry
  end

  section
    /-
    5.  Prove as many of the identities listed in the Existential
    Quantifier section as you can.
    -/
  end
end
