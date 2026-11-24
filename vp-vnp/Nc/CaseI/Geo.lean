/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Euclidean facts for the lower bound for the complete network

The distance from half a unit vector, sums over a set and its complement, signs of a set, and the
opposite corners of the cube {-1/2, 1/2}^k.
-/

namespace Nc.CaseI

open Finset

variable {k : ℕ}

/-- The distance from half a unit vector. -/
theorem dist_half_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u : V}
    (hu : ‖u‖ = 1) (x : V) : dist ((1 / 2 : ℝ) • u) x ≤ 1 / 2 - inner ℝ u x + ‖x‖ ^ 2 := by
  rw [dist_eq_norm]
  have h1 : ‖(1 / 2 : ℝ) • u - x‖ ^ 2 = 1 / 4 - inner ℝ u x + ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, hu, real_inner_smul_left, show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]
    ring
  have h2 : 0 ≤ ‖(1 / 2 : ℝ) • u - x‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖(1 / 2 : ℝ) • u - x‖ - 1 / 2)]

theorem sum_ite_card (A : Finset (Fin k)) (y z : ℝ) :
    ∑ a : Fin k, (if a ∈ A then y else z) = A.card * y + ((k : ℝ) - A.card) * z := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin k))) (fun a => a ∈ A)
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at h
  have : ((univ.filter fun a => a ∉ A).card : ℝ) = k - A.card := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact_mod_cast h
  exact this

/-- The sign of a. -/
noncomputable def sg (A : Finset (Fin k)) (a : Fin k) : ℝ := if a ∈ A then 1 else -1

/-! ### Opposite corners of the cube -/

/-- The sign 1 or -1 of a bit. -/
def bsign (b : Bool) : SignType := if b then 1 else -1

/-- The place of u in {-1,0,1}^k: the point u/2 of ℝ^k. -/
noncomputable def half (u : Fin k → SignType) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun x => ((u x : SignType) : ℝ) / 2

theorem half_apply (u : Fin k → SignType) (x : Fin k) : half u x = ((u x : SignType) : ℝ) / 2 := rfl

/-- Opposite vertices of the cube have the distance √k. -/
theorem dist_half_neg (π : Fin k → Bool) :
    dist (half fun x => bsign (π x)) (half fun x => -bsign (π x)) = √k := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have h : ∀ x, dist (half (fun x => bsign (π x)) x) (half (fun x => -bsign (π x)) x) ^ 2 = 1 := by
    intro x
    rw [half_apply, half_apply, Real.dist_eq]
    cases π x <;> simp [bsign] <;> norm_num
  simp [h]

end Nc.CaseI
