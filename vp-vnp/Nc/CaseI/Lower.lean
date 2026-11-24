/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.CaseI.Fkl
import Nc.CaseI.Geo

/-!
# The complete network: ends, sums over the ends, and the numbers of the lower bound
-/

namespace Nc.CaseI

open Finset

variable {k : ℕ}

/-- The ends of all pairs. -/
abbrev End (k : ℕ) := Σ _ : Pr k, Fin 2

/-- The parties: the ends, and two hubs for every set. -/
abbrev RPt (k : ℕ) := End k ⊕ (Finset (Fin k) × Bool)

/-- The node of an end. -/
def endNode (e : Pr k) (i : Fin 2) : Fin k := if i = 0 then e.1.1 else e.1.2

/-- Sums over ends and over pairs. -/
theorem sum_pairs (G : Fin k → Fin k → ℝ) :
    ∑ e : Pr k, (G e.1.1 e.1.2 + G e.1.2 e.1.1) = ∑ a, ∑ b, if a = b then 0 else G a b := by
  rw [← Fintype.sum_prod_type' (f := fun a b => if a = b then (0 : ℝ) else G a b),
    Finset.sum_add_distrib,
    ← Finset.sum_subtype (univ.filter fun e : Fin k × Fin k => e.1 < e.2) (by simp)
      (fun e : Fin k × Fin k => G e.1 e.2),
    ← Finset.sum_subtype (univ.filter fun e : Fin k × Fin k => e.1 < e.2) (by simp)
      (fun e : Fin k × Fin k => G e.2 e.1), Finset.sum_filter, Finset.sum_filter]
  have h2 : ∑ e : Fin k × Fin k, (if e.1 < e.2 then G e.2 e.1 else 0) =
      ∑ e : Fin k × Fin k, if e.2 < e.1 then G e.1 e.2 else 0 :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun e => rfl
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases lt_trichotomy e.1 e.2 with h | h | h
  · rw [ite_eq_left h, ite_eq_right (not_lt.2 h.le), ite_eq_right h.ne, add_zero]
  · rw [ite_eq_right (not_lt.2 h.ge), ite_eq_right (not_lt.2 h.le), ite_eq_left h, add_zero]
  · rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h, ite_eq_right h.ne', zero_add]

/-- Sum a constant over the ordered pairs of distinct nodes. -/
theorem sum_off_diagonal (c : ℝ) :
    (∑ a : Fin k, ∑ b : Fin k, if a = b then 0 else c) = k * (k - 1) * c := by
  have row (a : Fin k) := sum_ite_card ({a} : Finset (Fin k)) 0 c
  simp only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, mul_zero, zero_add] at row
  rw [Finset.sum_comm]
  simp only [row, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

theorem sum_pairs_one : ∑ _e : Pr k, (1 : ℝ) = k * (k - 1) / 2 := by
  have h := sum_pairs (k := k) fun _ _ => (1 : ℝ) / 2
  rw [sum_off_diagonal] at h
  convert h using 1 <;> norm_num [div_eq_mul_inv]

/-- The numbers of the lower bound. -/
theorem lower_numbers {k ℓ c N δ S1 S2 S3 lg : ℝ} (hk1 : 1 ≤ k) (hℓ0 : 0 ≤ ℓ) (hc : 0 ≤ c)
    (hN : N = k * (k - 1) / 2) (hδ : δ = 1 / (150 * k)) (hlog : 0 ≤ lg) (hℓc : 100 * c ≤ ℓ)
    (hw : N * (1 - δ) ≤ c * S1) (hh : c * S2 ≤ N - k / 12 + 2 * N * δ)
    (hm : c * S3 ≤ 1 / (3 * √k) + δ) (h1 : ℓ * S1 ≤ k + ℓ * S2 + S3 * lg) :
    ℓ * (k * √k) / 6 ≤ lg := by
  have hk0 : 0 < k := by linarith
  have hN0 : 0 ≤ N := by
    have : (0 : ℝ) ≤ k - 1 := by linarith
    rw [hN]
    positivity
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have h3 : ℓ * (N * (1 - δ)) ≤ c * k + ℓ * (N - k / 12 + 2 * N * δ) + (1 / (3 * √k) + δ) * lg := by
    have h2 := mul_le_mul_of_nonneg_left h1 hc
    have a1 := mul_le_mul_of_nonneg_left hw hℓ0
    have a2 := mul_le_mul_of_nonneg_left hh hℓ0
    have a3 := mul_le_mul_of_nonneg_right hm hlog
    linarith
  have hNδ : 3 * N * δ ≤ k / 100 := by
    have : N ≤ k * k / 2 := by rw [hN]; nlinarith
    have h4 : 3 * N * δ ≤ 3 * (k * k / 2) * δ := by gcongr
    refine h4.trans (le_of_eq ?_)
    rw [hδ]
    field_simp
    norm_num
  have hck : c * k ≤ ℓ * (k / 100) := by nlinarith
  have h5 : ℓ * (k * (19 / 300)) ≤ (1 / (3 * √k) + δ) * lg := by
    have h6 : ℓ * (3 * N * δ) ≤ ℓ * (k / 100) := mul_le_mul_of_nonneg_left hNδ hℓ0
    linarith
  have hsq : √k * √k = k := Real.mul_self_sqrt hk0.le
  have hsq1 : 1 ≤ √k := by
    rw [Real.one_le_sqrt]
    exact hk1
  have hsq0 : 0 < √k := by linarith
  have h7 : 1 / (3 * √k) + δ ≤ (17 / 50) / √k := by
    have h8 : δ ≤ 1 / (150 * √k) := by
      rw [hδ]
      refine one_div_le_one_div_of_le (by positivity) ?_
      nlinarith
    have h9 : (1 : ℝ) / (3 * √k) + 1 / (150 * √k) = (17 / 50) / √k := by
      field_simp
      norm_num
    linarith
  have h10 : ℓ * (k * (19 / 300)) ≤ (17 / 50) / √k * lg :=
    h5.trans (mul_le_mul_of_nonneg_right h7 hlog)
  rw [div_mul_eq_mul_div, le_div_iff₀ hsq0] at h10
  have h11 : (0 : ℝ) ≤ ℓ * (k * √k) := by positivity
  linarith

/-- Sums over ends, with an error. -/
theorem sum_pairs_add (G : Fin k → Fin k → ℝ) (δ : ℝ) :
    ∑ e : Pr k, ((G e.1.1 e.1.2 + δ) + (G e.1.2 e.1.1 + δ)) =
      (∑ a, ∑ b, if a = b then 0 else G a b) + 2 * ((k : ℝ) * (k - 1) / 2) * δ := by
  have h1 : ∀ e : Pr k, ((G e.1.1 e.1.2 + δ) + (G e.1.2 e.1.1 + δ)) =
      (G e.1.1 e.1.2 + G e.1.2 e.1.1) + 1 * (2 * δ) := fun e => by ring
  rw [Finset.sum_congr rfl fun e _ => h1 e, Finset.sum_add_distrib, sum_pairs, ← Finset.sum_mul,
    sum_pairs_one]
  ring

end Nc.CaseI
