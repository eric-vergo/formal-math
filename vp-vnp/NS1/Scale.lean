/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Postpone

/-!
# Scales

The cut at one scale (`CutAt`), the constant `cst` that bounds the fixed programs, and the sizes of
the budgets and plain instances of a round.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The cut at the scale `v ^ H`, for times up to `v ^ (H * α)`. -/
def CutAt (θ : List Bool → A) (H v α : ℕ) : Prop :=
  ∀ τ s, v ^ H ≤ τ → τ ≤ v ^ (H * α) → s * v ^ 48 ≤ τ → ∃ G, CutProg θ H v τ s G

theorem CutHyp.at {H C₀ v₀ v α : ℕ} (h : CutHyp θ H C₀ v₀) (hv : v₀ ≤ v) (hl : lg v ^ (C₀ * α) ≤ v) : CutAt θ H v α :=
  fun τ s => h v hv α τ s hl

/-- A constant: it bounds the sizes of the fixed programs. -/
def cst : ℕ := WF.code.size + UF.code.size + 2000

theorem cst_def : cst = WF.code.size + UF.code.size + 2000 := rfl

theorem size_LP (D : Tree) : (LP D).code.size ≤ D.size + 300 := by
  simp only [LP, Fm.code, Tree.size, size_num]
  omega

theorem pow_le_pow {u a b : ℕ} (hu : 1 ≤ u) (h : a ≤ b) : u ^ a ≤ u ^ b := Nat.pow_le_pow_right hu h

/-- Height and node count of an exponent budget for a trie of powers. -/
theorem KT.expand_budget_bounds (K : KT R) {B J : ℕ} {q : Bt × R} (hq : q ∈ (K.expand B).budg J) :
    q.1.ht ≤ K.ht + B + J + 1 ∧ q.1.nds ≤ (K.expand B).nds * (J + 1) := by
  have := KT.ht_budg hq
  have := KT.ht_expand B K
  exact ⟨by omega, KT.nds_budg hq⟩

/-- The encoded budget and the original input fit together in the input to the cutting program. -/
theorem size_zq_of_budget (K : KT R) {B J : ℕ} {p z : Tree} {q : Bt × R} (hq : q ∈ (K.expand B).budg J) :
    (zq p z q.1).size ≤ WF.code.size + p.size + z.size + 4 * ((K.expand B).nds * (J + 1)) + 3 := by
  have := Bt.size_enc q.1
  have := KT.nds_budg hq
  simp only [zq, Tree.size]
  omega

end NS1
