/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Statement

/-!
# The coefficient in `Statement.Approximates`

Mathlib at the revision this branch uses defines `MvPolynomial σ R` through the structure
`AddMonoidAlgebra`, whose field `coeff : (σ →₀ ℕ) →₀ R` holds the coefficients, and it has no
`MvPolynomial.coeff` any more. So the definition `Statement.Approximates` writes the coefficient of the
monomial `d` in `p` as `p.coeff d`, where the Mathlib revision of the upstream branch wrote
`coeff d p` (`MvPolynomial.coeff`). The text of the definition is otherwise the same.

Both spellings name the function characterised below: additive in the polynomial, with value `a` on the
monomial `monomial d a` at `d` and `0` at every other exponent. At the upstream revision
`MvPolynomial.coeff` has these properties (Mathlib's `MvPolynomial.coeff_add` and
`MvPolynomial.coeff_monomial` there). This file proves, at this branch's revision, that `p.coeff d` has
them and that every function with them is `fun d p ↦ p.coeff d`; so the definition means what it meant.

Run with `lake env lean scripts/StatementSpelling.lean`; it prints nothing when every proof checks.
-/

open MvPolynomial

namespace StatementSpelling

variable {σ R : Type*} [CommSemiring R] [DecidableEq σ]

omit [DecidableEq σ] in
/-- `p.coeff d` is additive in `p`. -/
theorem coeff_add' (d : σ →₀ ℕ) (p q : MvPolynomial σ R) :
    (p + q).coeff d = p.coeff d + q.coeff d := by
  simp

/-- `p.coeff d` on a monomial. -/
theorem coeff_monomial' (d e : σ →₀ ℕ) (a : R) :
    (monomial e a).coeff d = if e = d then a else 0 := by
  simp [coeff_monomial]

/-- A function with the two properties above is the coefficient. -/
theorem eq_coeff_of_laws (c : (σ →₀ ℕ) → MvPolynomial σ R → R)
    (hadd : ∀ d p q, c d (p + q) = c d p + c d q)
    (hmon : ∀ d e a, c d (monomial e a) = if e = d then a else 0) :
    c = fun d p ↦ p.coeff d := by
  funext d p
  induction p using MvPolynomial.induction_on' with
  | monomial e a => rw [hmon, coeff_monomial']
  | add p q hp hq => rw [hadd, hp, hq, coeff_add']

/-- So `Statement.Approximates`, written with any such function, is the definition of this branch. -/
theorem approximates_iff_of_laws {F : Type*} [Field F] {V : Type} [DecidableEq V]
    (c₁ : (V →₀ ℕ) → MvPolynomial V (LaurentSeries F) → LaurentSeries F)
    (c₂ : (V →₀ ℕ) → MvPolynomial V F → F)
    (hadd₁ : ∀ d p q, c₁ d (p + q) = c₁ d p + c₁ d q)
    (hmon₁ : ∀ d e a, c₁ d (monomial e a) = if e = d then a else 0)
    (hadd₂ : ∀ d p q, c₂ d (p + q) = c₂ d p + c₂ d q)
    (hmon₂ : ∀ d e a, c₂ d (monomial e a) = if e = d then a else 0)
    (f : MvPolynomial V F) (s : ℕ) :
    Statement.Approximates f s ↔
      ∃ q : MvPolynomial V (LaurentSeries F), Statement.Computes q s ∧
        ∀ (d : V →₀ ℕ) (i : ℤ), i ≤ 0 → (c₁ d q).coeff i = if i = 0 then c₂ d f else 0 := by
  rw [eq_coeff_of_laws c₁ hadd₁ hmon₁, eq_coeff_of_laws c₂ hadd₂ hmon₂]
  rfl

end StatementSpelling
