/-
As exercises, we encourage you to develop a notion of composition for
partial functions from α to β and β to γ, and show that it behaves as
expected.
-/
section
  variable (α β γ : Type)

  def partial_compose (f : Option β → Option γ) (g : Option α → Option β) : (Option α → Option γ) :=
    fun x : Option α =>
      match g x with
      | none => none
      | some x' =>
        match f x' with
        | none => none
        | some y' => some y'
end

/-
We also encourage you to show that Bool and Nat are inhabited,
that the product of two inhabited types is inhabited, and that the type
of functions to an inhabited type is inhabited.
-/

/-
As an exercise, prove the following:
-/

namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl
namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl
theorem append_nil (as : List α) :
    append as nil = as :=
  sorry

theorem append_assoc (as bs cs : List α) :
    append (append as bs) cs = append as (append bs cs) :=
  sorry
end List
end Hidden

/-
Try also defining the function length : {α : Type u} → List α → Nat that returns the length of a list, and prove that it behaves as expected (for example, length (append as bs) = length as + length bs).
-/

/-
1. Try defining other operations on the natural numbers, such as
multiplication, the predecessor function (with pred 0 = 0), truncated
subtraction (with n - m = 0 when m is greater than or equal to n), and
exponentiation. Then try proving some of their basic properties, building
on the theorems we have already proved.

Since many of these are already defined in Lean's core library, you
should work within a namespace named Hidden, or something like that, in
order to avoid name clashes.
 -/

/-
2. Define some operations on lists, like a length function or the reverse
function. Prove some properties, such as the following:

a. length (xs ++ ys) = length xs + length ys

b. length (reverse xs) = length xs

c. reverse (reverse xs) = xs
 -/

/-
3. Define an inductive data type consisting of terms built up from the
following constructors:

const n, a constant denoting the natural number n

var n, a variable, numbered n

plus s t, denoting the sum of s and t

times s t, denoting the product of s and t

Recursively define a function that evaluates any such term with respect
to an assignment of values to the variables.
-/

/-
4. Similarly, define the type of propositional formulas, as well as
functions on the type of such formulas: an evaluation function, functions
that measure the complexity of a formula, and a function that substitutes
another formula for a given variable.
 -/
