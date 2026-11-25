/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Acc.CompK

/-!
# The diagonal, over a finite ring

Over a finite ring a program can have the value 1 + its own value, if there is an accelerator at a scale that is
large against the ring and the number of constants.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- 1 + the value of the argument applied to itself. -/
def diagF (D : Tree) (g : Fm) : Fm := .ite .guess (.quote .nil) (app D (ZE .id g))

theorem diagF_ev {κ : List Bool → R} {D z : Tree} {g : Fm} {cg tD : ℕ} {P : List Bool → Prop} {lg : List (Run A)}
    {Q : List (Bt × R)} (hg : Ev θ g z lg) (rg : List.Forall₂ (RelG κ P cg) lg Q)
    (hD : ∀ q ∈ Q, Hl θ (Fm.ofTree D) (zq z z q.1) ∧ ∀ r ∈ evl θ (Fm.ofTree D) (zq z z q.1), r.cost ≤ tD ∧
      ∀ n ∈ r.bill, P n) :
    ∃ l, Ev θ (diagF D g) z l ∧ (∀ r ∈ l, r.cost ≤ cg + tD + 30 ∧ ∀ n ∈ r.bill, P n) ∧
      val κ l = 1 + (Q.map fun q => q.2 * val κ (evl θ (Fm.ofTree D) (zq z z q.1))).sum := by
  obtain ⟨lZ, eZ, rZ⟩ := ZE_ev (Dt.id z) hg rg
  have h := KV.either (S := {n | P n}) (KV.of_gives (κ := κ) (Gives.quote (θ := θ) .nil z))
    (KV.app_rel (P := D) (c := Prod.snd) (o := fun q => zq z z q.1)
      (w := fun q => val κ (evl θ (Fm.ofTree D) (zq z z q.1))) (d := tD) eZ rZ fun q hq =>
        ⟨_, (hD q hq).1.ev, (hD q hq).2, rfl⟩)
  exact h.mono (by omega)

end NS1
