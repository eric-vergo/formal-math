/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Rate
import Paper.HcGrid
import Paper.Transfer
import Paper.Ryser

/-!
# The paper, appendix "All fields and the Hamiltonian cycle polynomial"
-/

namespace Paper

open Finset MvPolynomial Nc

universe u

theorem map_genHC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) :
    MvPolynomial.map φ (genHC R m) = genHC S m := by
  simp only [genHC, map_sum, map_prod, map_X]

/-- The permanent with integer coefficients. -/
noncomputable def permInt (m : ℕ) : MvPolynomial (Fin m × Fin m) ℤ :=
  ∑ σ : Equiv.Perm (Fin m), ∏ i, X (σ i, i)

theorem map_permInt (F : Type u) [Field F] (m : ℕ) :
    MvPolynomial.map (Int.castRingHom F) (permInt m) = genPerm F m := by
  simp only [permInt, genPerm, Matrix.permanent, Matrix.of_apply, map_sum, map_prod, map_X]

/-- KK, "the algebraic closure of the prime field of characteristic p". -/
theorem exists_closed (p : ℕ) (hp : p = 0 ∨ p.Prime) : ∃ (K : Type) (_ : Field K), IsAlgClosed K ∧ CharP K p := by
  rcases hp with rfl | hp
  · exact ⟨AlgebraicClosure ℚ, inferInstance, inferInstance, inferInstance⟩
  · have : Fact p.Prime := ⟨hp⟩
    exact ⟨AlgebraicClosure (ZMod p), inferInstance, inferInstance, inferInstance⟩

/-- 2 is not 0 in characteristic other than 2. -/
theorem two_ne_zero_of_char (K : Type) [Field K] (p : ℕ) [CharP K p] (hp : p = 0 ∨ p.Prime) (h2 : p ≠ 2) :
    (2 : K) ≠ 0 := by
  intro h
  have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h3
  rcases hp with rfl | hp
  · simp at h3
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

/-- "The bound of the contracting case, although its constant depends on p, exceeds that of the flat case for large m." -/
theorem thm_allfields_exceeds {P : ℕ → ℕ → Prop}
    (h : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨c, hc, m₁, h⟩ := h
  obtain ⟨m₂, hm₂⟩ := thm_main_calculation (1 / (c * 1600 ^ 2))
  refine ⟨m₁ + m₂, fun m hm s hs => lt_of_le_of_lt ?_ (h m (by omega) s hs)⟩
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_left (hm₂ m (by omega)) hc.le).trans_eq (mul_div_assoc _ _ _).symm)
  field_simp

/-- The field dichotomy gives the same eventual rate for every family complete for
grid sums. Its threshold may depend on the family and the field. -/
theorem exact_rate_complete {K : Type} [Field K]
    {G : ∀ m, MvPolynomial (Fin m × Fin m) K} {κ : ℕ} (hG : GridComplete K G κ) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ s, Computes (G m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  rcases thm_alt K with hK | hK
  · obtain ⟨M, h⟩ := flat_rate_complete κ
    exact ⟨M, h K hK G hG⟩
  · obtain ⟨C, M, h⟩ := contracting_complete hK hG
    exact thm_allfields_exceeds (quasi_of_exponents (P := fun m s => Computes (G m) s)
      (fun _ _ _ hst hs => hs.mono hst) h)

/-- The bound 2^((log m)^(4/3)/1600²) in the form of the main theorems. -/
theorem beyond_of_rate {m s : ℕ} (hm : 2 ≤ m) (h : (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s) :
    (m : ℝ) ^ (1 / 1600 ^ 2 * Real.logb 2 m ^ (1 / 3 : ℝ)) < s := by
  rwa [thm_main_form hm, one_div_mul_eq_div]

/-- Combine the two family thresholds, imposing the permanent bound only away from
characteristic two. Both bounds then use an index at least two. -/
theorem common_family_threshold {p : ℕ} {H P : ℕ → Prop}
    (hc : ∃ M, ∀ m ≥ M, H m) (hp : p ≠ 2 → ∃ M, ∀ m ≥ M, P m) :
    ∃ M, ∀ m ≥ M, 2 ≤ m ∧ H m ∧ (p ≠ 2 → P m) := by
  obtain ⟨A, hA⟩ := hc
  by_cases he : p = 2
  · exact ⟨max A 2, fun m hm =>
      ⟨le_trans (le_max_right _ _) hm, hA m (le_trans (le_max_left _ _) hm),
        fun h => (h he).elim⟩⟩
  · obtain ⟨B, hB⟩ := hp he
    exact ⟨A + B + 2, fun m hm => ⟨by omega, hA m (by omega), fun _ => hB m (by omega)⟩⟩

/-- **Paper: Theorem thm:allfields.** "There is an absolute constant c > 0 such that for every p, zero or prime,
there is m₀: over every field of characteristic p and for every m ≥ m₀ every circuit for HC_m, and for PERM_m if p ≠ 2,
has more than m^(c(log m)^(1/3)) gates." -/
theorem thm_allfields : ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, p = 0 ∨ p.Prime → ∃ m₀ : ℕ,
    ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Computes (genHC F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) ∧
      (p ≠ 2 → Computes (genPerm F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) := by
  refine ⟨1 / 1600 ^ 2, by norm_num, fun p hp => ?_⟩
  obtain ⟨K, _, _, _⟩ := exists_closed p hp
  obtain ⟨M, hM⟩ := common_family_threshold (p := p) (exact_rate_complete (gridComplete_hc K))
    fun hne => exact_rate_complete (gridComplete_perm (two_ne_zero_of_char K p hp hne))
  refine ⟨M, fun F _ _ m hm s => ?_⟩
  obtain ⟨hm₂, hHC, hPerm⟩ := hM m hm
  constructor
  · intro hs
    rw [← map_genHC (Int.castRingHom F)] at hs
    have h := lem_transfer (KK := K) p (genHC ℤ m) hs
    rw [map_genHC] at h
    exact beyond_of_rate hm₂ (hHC s h)
  · intro hne hs
    rw [← map_permInt] at hs
    have h := lem_transfer (KK := K) p (permInt m) hs
    rw [map_permInt] at h
    exact beyond_of_rate hm₂ (hPerm hne s h)

private theorem tendsto_rate_exponent {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun m : ℕ => c * Real.logb 2 m ^ (1 / 3 : ℝ)) Filter.atTop Filter.atTop :=
  ((tendsto_rpow_atTop (by norm_num)).comp
    ((Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)).const_mul_atTop hc

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
    ({ X := fun n => Fin n × Fin n, poly := genHC F } : Family F) ∈ VNP F := by
  refine ⟨fun n => n * n, Hc.hcWit F, ⟨700, fun n => ?_⟩, Hc.genHC_eq_sum_wit F⟩
  have hb := Hc.quartic_bound n (C := 700) le_rfl
  obtain ⟨h1, h2⟩ := Hc.csize_hcWit F n
  refine ⟨le_trans ?_ hb, h2.trans hb, h1.mono hb⟩
  show Fintype.card ((Fin n × Fin n) ⊕ Fin (n * n)) ≤ _
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  nlinarith [Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

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
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 ((tendsto_rate_exponent hc).eventually_ge_atTop (C : ℝ))
  refine ⟨A + B + 1, fun m hm s hs hcomp => ?_⟩
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ m by exact_mod_cast (by omega : 1 ≤ m)) (hB m (by omega))
  rw [Real.rpow_natCast] at hpow
  exact (not_lt_of_ge (show (s : ℝ) ≤ (m : ℝ) ^ C by exact_mod_cast hs))
    (hpow.trans_lt (hA m (by omega) s hcomp))

/-- **Paper: Corollary cor:classes.** "Over ℝ, VP is a proper subset of VNP." The witness is the permanent: it is in VNP
by Ryser's formula and exceeds every polynomial size bound by Theorem thm:main. -/
theorem cor_classes : VP ℝ ⊂ VNP ℝ := by
  refine ⟨vp_subset_vnp ℝ, fun h => ?_⟩
  obtain ⟨C, hC⟩ := h (perm_mem_VNP ℝ)
  obtain ⟨c, hc, M, hM⟩ := thm_main
  exact no_poly_size_of_rate (P := fun m s => Computes (genPerm ℝ m) s) hc
    (fun m hm s hs => hM m hm s (by simpa only [← genPerm_eq] using hs)) C fun m => (hC m).2.2

end Paper
