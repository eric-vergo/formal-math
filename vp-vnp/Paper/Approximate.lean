/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Fields

/-!
# The paper, appendix "Approximate computation"
-/

namespace Paper

open Finset MvPolynomial Nc Nc.Price Nc.CaseI Ov

universe u

/-- VP closure: like VP, with approximating circuits. -/
def VPBar (F : Type u) [Field F] : Set (Family F) :=
  {f | ∃ C : ℕ, ∀ n, Fintype.card (f.X n) ≤ n ^ C + C ∧ (f.poly n).totalDegree ≤ n ^ C + C ∧
    Approximates (f.poly n) (n ^ C + C)}

/-- **Paper: Definition def:approx.** "A circuit over k((ε)) approximates a polynomial f over the field k if its output
is f + εg with all coefficients of g in k[[ε]]. The closure of VP is defined like VP with approximating circuits."
Coefficientwise: no negative powers of ε, and the part of ε⁰ is f. -/
theorem def_approx {F : Type u} {X : Type*} [Field F] (f : MvPolynomial X F) (s : ℕ) :
    Approximates f s ↔ ∃ p : MvPolynomial X (LaurentSeries F), Computes p s ∧
      ∀ d : X →₀ ℕ, (∀ i : ℤ, i < 0 → (p.coeff d).coeff i = 0) ∧ (p.coeff d).coeff 0 = f.coeff d := by
  simp only [Approximates, coeff_nonpos_iff]

/-- **Paper: Theorem thm:approx.** "The theorem on all fields holds for circuits that approximate HC_m, respectively
PERM_m. In particular VNP is not contained in the closure of VP over every field." -/
theorem thm_approx :
    (∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, p = 0 ∨ p.Prime → ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Approximates (genHC F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) ∧
      (p ≠ 2 → Approximates (genPerm F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s)) ∧
    ∀ (F : Type u) [Field F], ¬ VNP F ⊆ VPBar F := by
  refine ⟨⟨1 / 1600 ^ 2, by norm_num, border_rate_allfields⟩, fun F _ h => ?_⟩
  obtain ⟨C, hC⟩ := h (hc_mem_VNP F)
  obtain ⟨p, _⟩ := CharP.exists F
  obtain ⟨m₀, hlow⟩ := border_rate_allfields p (CharP.char_is_prime_or_zero F p).symm
  exact no_poly_size_of_rate (P := fun m s => Approximates (genHC F m) s)
    (c := 1 / 1600 ^ 2) (by norm_num) (fun m hm s => (hlow F m hm s).1) C fun m => (hC m).2.2

end Paper
