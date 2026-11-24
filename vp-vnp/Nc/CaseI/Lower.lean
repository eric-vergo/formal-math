/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.CaseI.Fkl
import Nc.CaseI.Geo

/-!
# The complete network: ends, parties and sums over the ends
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

end Nc.CaseI
