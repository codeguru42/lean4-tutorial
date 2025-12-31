section
  section
    -- Prove the following identities, replacing the sorry placeholders with actual proofs.
    variable (p q r : Prop)

    -- commutativity of ∧ and ∨
    example : p ∧ q ↔ q ∧ p := by
      apply Iff.intro
      · intro ⟨hp, hq⟩
        exact And.intro hq hp
      · intro ⟨hq, hp⟩
        exact And.intro hp hq
    example : p ∨ q ↔ q ∨ p := by
      apply Iff.intro
      · intro h
        apply h.elim
        case left =>
          exact Or.inr
        case right =>
          exact Or.inl
      · intro h
        apply h.elim
        case left =>
          exact Or.inr
        case right =>
          exact Or.inl

    -- associativity of ∧ and ∨
    example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
      apply Iff.intro
      · intro ⟨⟨ hp, hq⟩, hr⟩
        exact And.intro hp (And.intro hq hr)
      · intro ⟨hp, ⟨hq, hr⟩⟩
        exact And.intro (And.intro hp hq) hr
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
      · intro ⟨hp, hq⟩
        cases hq with
        | inl hq => exact Or.inl (And.intro hp hq)
        | inr hr => exact Or.inr (And.intro hp hr)
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
      · intro ⟨hpq, hpr⟩
        cases hpq with
        | inl hp => exact Or.inl hp
        | inr hq =>
          cases hpr with
          | inl hp => exact Or.inl hp
          | inr hr => exact Or.inr (And.intro hq hr)

    -- other properties
    example : (p → (q → r)) ↔ (p ∧ q → r) := by
      apply Iff.intro
      · intro h ⟨hp, hq⟩
        exact h hp hq
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
      intro ⟨hp, hnp⟩
      exact hnp hp
    example : p ∧ ¬q → ¬(p → q) := by
      intro ⟨hp, hnq⟩ hpq
      exact hnq (hpq hp)
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
      by_cases hq : q
      · apply Or.inl
        intro hp
        exact hq
      · apply Or.inr
        intro hp
        apply (h hp).elim
        · intro hq'
          contradiction
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
    example : p ∨ ¬p := by
      by_cases hp : p
      · exact Or.inl hp
      · exact Or.inr hp
    example : (((p → q) → p) → p) := by
      intro h
      by_cases hp : p
      · exact hp
      · apply h
        intro hp'
        exfalso
        apply hp
        exact hp'
  end

  -- Prove ¬(p ↔ ¬p) without using classical logic.
end

section
  section
    -- 1. Prove these equivalences:
    variable (α : Type) (p q : α → Prop)

    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
      apply Iff.intro
      · intro h
        constructor
        · intro x
          exact (h x).left
        · intro x
          exact (h x).right
      · intro ⟨hp, hq⟩ x
        constructor
        · exact hp x
        · exact hq x
    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
      intro h hp x
      apply h x (hp x)
    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
      intro h x
      apply h.elim
      · intro hp
        exact Or.inl (hp x)
      · intro hq
        exact Or.inr (hq x)
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

    example : α → ((∀ x : α, r) ↔ r) := by
      intro w
      apply Iff.intro
      · intro h
        exact h w
      · intro hr x
        exact hr
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
      apply Iff.intro
      · intro h
        by_cases hr: r
        · exact Or.inr hr
        · apply Or.inl
          intro x
          apply (h x).elim
          · intro hx
            exact hx
          · intro hr'
            contradiction
      · intro h x
        apply h.elim
        · intro hp
          exact Or.inl (hp x)
        · intro hr'
          exact Or.inr hr'
    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
      apply Iff.intro
      · intro h hr x
        exact h x hr
      · intro h x hr
        exact h hr x
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

    open Classical

    variable (α : Type) (p q : α → Prop)
    variable (r : Prop)

    example : (∃ _ : α, r) → r := by
      intro h
      cases h with
      | intro x hr => exact hr
    example (a : α) : r → (∃ _ : α, r) := by
      intro h
      exists a
    example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
      apply Iff.intro
      · intro h
        cases h with
        | intro w hw =>
          apply And.intro
          · exists w
            exact hw.left
          · exact hw.right
      · intro h
        cases h with
        | intro hp hr =>
          cases hp with
          | intro w hw =>
            exists w
    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
      apply Iff.intro
      · intro h
        cases h with
        | intro x hpq =>
          cases hpq with
          | inl hp =>
            apply Or.inl
            exists x
          | inr hq =>
            apply Or.inr
            exists x
      · intro h
        cases h with
        | inl hp =>
          cases hp with
          | intro w hw =>
            exists w
            exact Or.inl hw
        | inr hq =>
          cases hq with
          | intro w hw =>
            exists w
            exact Or.inr hw

    example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
      apply Iff.intro
      · intro h hnp
        cases hnp with
        | intro w hw =>
          exact hw (h w)
      · intro h x
        by_cases hp : p x
        · exact hp
        · exfalso
          apply h
          exists x
    example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
      apply Iff.intro
      · intro h hnp
        cases h with
        | intro w hw =>
          exact hnp w hw
      · intro h
        by_cases hx : ∃ x, p x
        · exact hx
        · exfalso
          apply h
          intro x hp
          apply hx
          exists x
    example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
      apply Iff.intro
      · intro h x hnp
        apply h
        exists x
      · intro h hnp
        apply hnp.elim
        intro x hp
        exact h x hp
    example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
      apply Iff.intro
      · intro h
        by_cases h' : ∃ x, ¬p x
        · exact h'
        · exfalso
          apply h
          intro x
          by_cases h'' : p x
          · exact h''
          · exfalso
            apply h'
            exists x
      · intro h
        cases h with
        | intro w hnp =>
          intro hp
          exact hnp (hp w)

    example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
    example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
    example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
  end
end
