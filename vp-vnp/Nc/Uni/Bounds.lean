/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Exist
import Nc.Uni.LenU
import Nc.Uni.TopU
import Nc.Tape.ProgRun

/-!
# The universal automaton: bounds for the time
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset NS1

section General

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] {P : Mach A M K}

theorem tU_mono {b T T' L L' : ℕ} (hT : T ≤ T') (hL : L ≤ L') : tU b T L ≤ tU b T' L' := by
  unfold tU
  gcongr

end General

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The number of steps. -/
def stepsU (supp : Finset (List Bool)) (τ s : ℕ) : ℕ := 3 * s + (40 + 2 * Lm supp) * τ + 10

theorem tU_le (b T L : ℕ) : tU b T L ≤ (50 + b) * ((T + 1) * (L + 1) ^ 2) := by
  unfold tU
  ring_nf
  omega

theorem size_le_lg (n : ℕ) : Nat.size n ≤ lg n := by
  rw [Nat.size_le, lg]
  exact Nat.lt_pow_succ_log_self (by norm_num) n

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

end Nc.Uni
