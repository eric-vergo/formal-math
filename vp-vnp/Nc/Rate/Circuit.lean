/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Rate.Defs
import Nc.Final.CClasses
import Nc.Rate.Truncate

/-!
# Substitution into approximate circuits
-/

namespace Nc

open Finset MvPolynomial

variable {F X Y : Type*} [Field F]

/-- Expand one output coefficient of a substitution over any finite set containing the support. -/
private theorem coeff_aeval_sum {K : Type*} [CommSemiring K]
    (M : X → MvPolynomial Y K) (p : MvPolynomial X K) (d : Y →₀ ℕ)
    {s : Finset (X →₀ ℕ)} (hs : p.support ⊆ s) :
    (aeval M p).coeff d = ∑ b ∈ s, p.coeff b * (∏ x ∈ b.support, M x ^ b x).coeff d := by
  classical
  rw [aeval_def, eval₂_eq, coeff_sum]
  simp only [MvPolynomial.algebraMap_eq, coeff_C_mul]
  exact Finset.sum_subset hs fun b _ hb => by rw [notMem_support_iff.1 hb, zero_mul]

/-- An affine substitution keeps approximation; the number of gates grows by a factor
at most 5. -/
theorem LaurentApproximates.aeval {f : MvPolynomial X F} {s : ℕ} (h : LaurentApproximates f s) (M : X → MvPolynomial Y F)
    (hM : ∀ q, IsAffine (M q)) : LaurentApproximates (MvPolynomial.aeval M f) (5 * s) := by
  let ι := algebraMap F (LaurentPolynomial F)
  obtain ⟨p, hp, hpf⟩ := h
  refine ⟨MvPolynomial.aeval (fun q => MvPolynomial.map ι (M q)) p,
    hp.aeval _ fun q => ?_, fun d i hi => ?_⟩
  · rcases hM q with ⟨b, hb⟩ | ⟨j, a, b, hb⟩
    · exact Or.inl ⟨ι b, by rw [hb, map_C]⟩
    · exact Or.inr ⟨j, ι a, ι b, by rw [hb, map_add, map_mul, map_C, map_C, map_X]⟩
  · classical
    let s := p.support ∪ f.support
    have hp' : p.support ⊆ s := subset_union_left
    have hf' : f.support ⊆ s := subset_union_right
    have e3 : ∀ (a : LaurentPolynomial F) (r : F), (a * ι r).coeff i = a.coeff i * r := by
      intro a r
      rw [mul_comm, ← Algebra.smul_def, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, mul_comm]
    rw [coeff_aeval_sum _ p d hp', AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_aeval_sum M f d hf']
    simp only [← map_pow, ← map_prod, coeff_map, e3, hpf _ i hi]
    by_cases h0 : i = 0 <;> simp [h0]

/-- Affine projection preserves approximation and increases the gate bound by at most five. -/
theorem Approximates.aeval {f : MvPolynomial X F} {s : ℕ} (h : Approximates f s) (M : X → MvPolynomial Y F)
    (hM : ∀ q, IsAffine (M q)) : Approximates (MvPolynomial.aeval M f) (5 * s) :=
  laurentApproximates_iff.mp (h.exists_laurentPolynomial.aeval M hM)

end Nc
