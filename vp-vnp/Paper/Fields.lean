/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.BorderRate
import Paper.Ryser

/-!
# The paper, appendix "All fields and the Hamiltonian cycle polynomial"
-/

namespace Paper

open Finset MvPolynomial Nc

universe u

/-- An exact circuit gives a coefficientwise approximation of the same size by
viewing its constants as constant Laurent series. -/
theorem approximates_of_computes {F : Type u} [Field F] {V : Type} {f : MvPolynomial V F}
    {s : ℕ} (h : Computes f s) : Approximates f s := by
  refine ⟨_, h.map (HahnSeries.C : F →+* LaurentSeries F), fun d i _ => ?_⟩
  by_cases hi : i = 0 <;> simp [coeff_map, HahnSeries.C_apply, hi]

/-- **Paper: Theorem thm:allfields.** "There is an absolute constant c > 0 such that for every p, zero or prime,
there is m₀: over every field of characteristic p and for every m ≥ m₀ every circuit for HC_m, and for PERM_m if p ≠ 2,
has more than m^(c(log m)^(1/3)) gates." -/
theorem thm_allfields : ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, p = 0 ∨ p.Prime → ∃ m₀ : ℕ,
    ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Computes (genHC F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) ∧
      (p ≠ 2 → Computes (genPerm F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) := by
  refine ⟨1 / 1600 ^ 2, by norm_num, fun p hp => ?_⟩
  obtain ⟨M, hM⟩ := border_rate_allfields.{u} p hp
  exact ⟨M, fun F _ _ m hm s =>
    ⟨fun h => (hM F m hm s).1 (approximates_of_computes h),
     fun hne h => (hM F m hm s).2 hne (approximates_of_computes h)⟩⟩

/-- A bound m^(c(log m)^(1/3)) is beyond every polynomial. -/
theorem exists_beyond_poly {c : ℝ} (hc : 0 < c) (m₀ C : ℕ) :
    ∃ m ≥ m₀, ¬ (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < ((m ^ C + C : ℕ) : ℝ) := by
  obtain ⟨m, hm1, hm2⟩ := ((Filter.eventually_ge_atTop (m₀ + C + 2)).and
    ((tendsto_rate_exponent hc).eventually_ge_atTop ((C + 1 : ℕ) : ℝ))).exists
  refine ⟨m, by omega, fun hb => ?_⟩
  have h3 : (m : ℝ) ^ ((C + 1 : ℕ) : ℝ) < ((m ^ C + C : ℕ) : ℝ) :=
    lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m)) hm2) hb
  rw [Real.rpow_natCast] at h3
  have h4 : m ^ (C + 1) < m ^ C + C := by exact_mod_cast h3
  have h5 : 1 ≤ m ^ C := Nat.one_le_pow _ _ (by omega)
  have h6 : m ^ C * (C + 1) ≤ m ^ C * m := Nat.mul_le_mul_left _ (by omega)
  rw [pow_succ] at h4
  nlinarith

/-- An eventual lower bound on circuit size rules out a polynomial size bound
for the same family, for either exact or approximating circuits. -/
theorem no_poly_size_of_rate {P : ℕ → ℕ → Prop} {c : ℝ} (hc : 0 < c)
    {m₀ : ℕ} (h : ∀ m ≥ m₀, ∀ s, P m s →
      (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s)
    (C : ℕ) (hC : ∀ m, P m (m ^ C + C)) : False := by
  obtain ⟨m, hm, hb⟩ := exists_beyond_poly hc m₀ C
  exact hb (h m hm _ (hC m))

/-- "(HC_m) is in VNP." -/
theorem hc_mem_VNP (F : Type u) [Field F] :
    ({ X := fun n => Fin n × Fin n, poly := genHC F } : Family F) ∈ VNP F :=
  Hc.mem_VNP_of_quartic_witness _ (fun n => n * n) _ (fun _ => Nat.le_add_right _ _)
    (Hc.csize_hcWit F) (Hc.genHC_eq_sum_wit F)

/-- **Paper: Corollary cor:allclasses.** "Over every field, VP is a proper subset of VNP." -/
theorem cor_allclasses (F : Type u) [Field F] : VP F ⊂ VNP F := by
  refine ⟨vp_subset_vnp F, fun h => ?_⟩
  obtain ⟨C, hC⟩ := h (hc_mem_VNP F)
  obtain ⟨p, _⟩ := CharP.exists F
  obtain ⟨c, hc, hall⟩ := thm_allfields.{u}
  obtain ⟨m₀, hlow⟩ := hall p (CharP.char_is_prime_or_zero F p).symm
  exact no_poly_size_of_rate (P := fun m s => Computes (genHC F m) s) hc
    (fun m hm s => (hlow F m hm s).1) C fun m => (hC m).2.2

/-- **Paper: Theorem thm:main.** "There are c > 0 and m₀ such that for all m ≥ m₀ every circuit over ℝ that computes
PERM_m has more than m^(c(log m)^(1/3)) gates." -/
theorem thm_main : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ,
    Computes (∑ σ : Equiv.Perm (Fin m), ∏ i, MvPolynomial.X (σ i, i) : MvPolynomial (Fin m × Fin m) ℝ) s →
      (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s := by
  obtain ⟨c, hc, hall⟩ := thm_allfields.{0}
  obtain ⟨M, hM⟩ := hall 0 (Or.inl rfl)
  exact ⟨c, hc, M, fun m hm s hs => (hM ℝ m hm s).2 (by decide) (genPerm_eq ℝ m ▸ hs)⟩

/-- **Paper: Theorem thm:simple.** "For every C there is m₀ such that for all m ≥ m₀ no circuit over ℝ with at most m^C
gates computes PERM_m." -/
theorem thm_simple (C : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ, s ≤ m ^ C →
    ¬ Computes (∑ σ : Equiv.Perm (Fin m), ∏ i, MvPolynomial.X (σ i, i) : MvPolynomial (Fin m × Fin m) ℝ) s := by
  obtain ⟨c, hc, A, hA⟩ := thm_main
  exact excludes_poly_size hc hA C

/-- **Paper: Corollary cor:classes.** "Over ℝ, VP is a proper subset of VNP." The witness is the permanent: it is in VNP
by Ryser's formula and exceeds every polynomial size bound by Theorem thm:main. -/
theorem cor_classes : VP ℝ ⊂ VNP ℝ := by
  refine ⟨vp_subset_vnp ℝ, fun h => ?_⟩
  obtain ⟨C, hC⟩ := h (perm_mem_VNP ℝ)
  obtain ⟨c, hc, M, hM⟩ := thm_main
  exact no_poly_size_of_rate (P := fun m s => Computes (genPerm ℝ m) s) hc
    (fun m hm s hs => hM m hm s (by simpa only [← genPerm_eq] using hs)) C fun m => (hC m).2.2

end Paper
