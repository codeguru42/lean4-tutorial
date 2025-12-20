/-
1. Prove these equivalences:
 -/
section
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    Iff.intro
      (fun h =>
        And.intro
          (fun hp => (h hp).left)
          (fun hq => (h hq).right))
      (fun h h' => And.intro (h.left h') (h.right h'))
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    fun h g x => (h x) (g x)
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    fun h x =>
      h.elim
        (fun hp => Or.inl (hp x))
        (fun hq => Or.inr (hq x))
end

/-
 2. You should also try to understand why the reverse
 implication is not derivable in the last example.

It is often possible to bring a component of a formula outside
a universal quantifier, when it does not depend on the
quantified variable. Try proving these (one direction of the
second of these requires classical logic):
 -/
section
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ _ : α, r) ↔ r) :=
    fun x =>
      Iff.intro
        (fun h => h x)
        (fun h _ => h)
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    Iff.intro
      (fun h =>
        Classical.byCases
          (fun hr : r => Or.inr hr)
          (fun hnr : ¬r =>
            Or.inl
              fun x =>
                (h x).elim
                  (fun hx => hx)
                  (fun hr' => absurd hr' hnr)))
      (fun h =>
        h.elim
          (fun hp x => Or.inl (hp x))
          (fun hr _ => Or.inr hr))
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    Iff.intro
      (fun h hr x => (h x) hr)
      (fun h x hr => (h hr) x)
end

/-
3. Consider the “barber paradox,” that is, the claim that in a
certain town there is a (male) barber that shaves all and
only the men who do not shave themselves. Prove that this is
a contradiction:
 -/
section
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    let t := h barber
    have h₁ := fun hp => (t.mp hp) hp
    have h₂ := t.mpr h₁
    h₁ h₂
end

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
section
  def even (n : Nat) : Prop := ∃x : Nat, n = 2*x

  def prime (n : Nat) : Prop :=
    ∀ x : Nat, x ∣ n → (x > 1) ∧ ((x = 1) ∨ (x = n))

  def infinitely_many_primes : Prop :=
    ∀ n : Nat, ∃ p : Nat, p > n ∧ prime p

  def Fermat_prime (n : Nat) : Prop := prime (2^2^n + 1)

  def infinitely_many_Fermat_primes : Prop := sorry

  def goldbach_conjecture : Prop := sorry

  def Goldbach's_weak_conjecture : Prop := sorry

  def Fermat's_last_theorem : Prop := sorry
end

/-
5.  Prove as many of the identities listed in the Existential
 Quantifier section as you can.
 -/

section
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : (∃ x : α, r) → r :=
    fun h => Exists.elim h (fun _ hr => hr)
  example (a : α) : r → (∃ x : α, r) :=
    fun h => Exists.intro a h
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    Iff.intro
      (fun h =>
        Exists.elim
          h
          fun w hw =>
            And.intro
              (Exists.intro w hw.left)
              hw.right)
      (fun h =>
        Exists.elim
          h.left
          (fun w hw =>
            Exists.intro
              w
              (And.intro hw h.right)))
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    Iff.intro
      (fun h =>
        Exists.elim
          h
          (fun w hw =>
            hw.elim
              (fun hp => Or.inl (Exists.intro w hp) )
              (fun hq => Or.inr (Exists.intro w hq))))
      (fun h =>
        h.elim
          (fun hp =>
            Exists.elim
              hp
              (fun w hw => Exists.intro w (Or.inl hw)))
          (fun hq =>
            Exists.elim
              hq
              (fun w hw => Exists.intro w (Or.inr hw))))
  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    Iff.intro
      (fun h hnp =>
        Exists.elim hnp (fun w hw => hw (h w)))
      (fun h x =>
        byContradiction (fun hnp => h (Exists.intro x hnp)))
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    Iff.intro
      (fun h => Exists.elim h (fun w hw hnp => hnp w hw))
      (fun h =>
        byContradiction
          (fun hnp =>
            h (fun x hp => hnp (Exists.intro x hp))))
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
end
