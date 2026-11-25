/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.EvalU

/-!
# The universal machine evaluates formulas
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The sum over the runs without named constants. -/
def tot (m : Run A → A) (l : List (Run A)) : A := (l.map fun r => if r.bill = [] then r.th * m r else 0).sum

theorem tot_nil (m : Run A → A) : tot m [] = 0 := rfl

/-- Setting every named constant to zero counts exactly the runs with empty bills. -/
theorem tot_eq_weighted_sum (m : Run A → A) (l : List (Run A)) :
    tot m l = (l.map fun r => wt (fun _ => (0 : A)) r * m r).sum := by
  unfold tot
  congr 1
  refine List.map_congr_left fun r _ => ?_
  cases h : r.bill <;> simp [wt, h]

/-- One run after the other. -/
theorem tot_seq (m : Run A → A) (la : List (Run A)) (L : Run A → List (Run A)) (o : Run A → Run A → Tree) :
    tot m (la.flatMap fun r => (L r).map fun s => (r.seq s).tick (o r s)) =
      tot (fun r => tot (fun s => m ((r.seq s).tick (o r s))) (L r)) la := by
  simp only [tot_eq_weighted_sum, sum_flatMap_map, List.map_map, Function.comp_def, wt_tick,
    wt_seq, ← List.sum_map_mul_left, mul_assoc]

variable (supp) in
/-- Steps of the machine for one step of the evaluation. -/
def Cc : ℤ := 40 + 2 * (Lm supp : ℤ)

theorem Cc_ge : 40 ≤ Cc supp := by
  unfold Cc
  have : (0 : ℤ) ≤ (Lm supp : ℤ) := Int.natCast_nonneg _
  linarith

/-- The machine is about to evaluate the formula F at the tree x. -/
structure ES (σ : St supp) (F : Fm) (x : Tree) : Prop where
  ok : OKs σ
  mode : σ.mode = .E
  fm : ∃ c, Rep σ.heap (σ.regs 1) c ∧ Fm.ofTree c = F
  arg : Rep σ.heap (σ.regs 2) x

variable (θ supp) in
/-- The machine evaluates the formula correctly. -/
def EvOK (F : Fm) (x : Tree) (l : List (Run A)) : Prop :=
  ∀ σ : St supp, ES σ F x → ∀ (m : Run A → A) (Bd : Run A → ℤ) (B : ℤ),
    (∀ r ∈ l, r.bill = [] → KS θ supp σ.heap (σ.regs 3) σ.inp r.out (m r) (Bd r) ∧ Cc supp * r.cost + Bd r ≤ B) →
    Mach.SumTo (UM θ supp) σ (tot m l) B

/-- A step from an opcode. -/
theorem dstep {σ : St supp} (hσ : OKs σ) {c : Fin 11} (hm : σ.mode = .D c) (h1 : σ.regs 1 = 0) (r : Ra)
    (hr : nextR supp (.D c) .N = some (.inl r)) (hc : c ≠ 7) (hs : (ruleA r : RD A (Nm supp)).src = .D c)
    (hk : (ruleA r : RD A (Nm supp)).lk = .N) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) 0 0 0) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec := hσ.nil_load hm h1
  have h2 := sumTo_ruleA hσ hrec r (by rw [hm]; exact hr) (by rw [hm]; simp) (by rw [hm]; simp [hc]) (by rw [hm]; exact hs)
    hk h
  exact h2.mono (by omega)

theorem EvOK.quote (c0 x : Tree) : EvOK θ supp (.quote c0) x [.det 1 c0] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨hk, hB⟩ := h (.det 1 c0) (by simp) rfl
  have ht : tot m [.det 1 c0] = m (.det 1 c0) := by simp [tot, Run.det]
  rw [ht]
  have hC := Cc_ge (supp := supp)
  have hB' : Cc supp + Bd (.det 1 c0) ≤ B := by
    have : ((Run.det 1 c0 : Run A).cost : ℤ) = 1 := rfl
    rw [this] at hB
    linarith
  rcases Fm.codeShape_of_decode hF with ⟨rfl, rfl⟩ | ⟨o, rfl, hl⟩
  · have h0 : σ.regs 1 = 0 := hc
    have hrec := ok.nil_load hm h0
    have h2 := hk (nx θ σ (.inl .en) 0 0 0) 0 (ok.nx _ _ _ _) rfl h0 rfl (heap_nx σ _ _ _ _)
      (inpA σ _ (by simp) (by simp) _ _ _) rfl
    exact (sumTo_ruleA ok hrec .en (by rw [hm]; rfl) (by rw [hm]; simp) (by rw [hm]; simp) (by rw [hm]; rfl) rfl h2).mono
      (by linarith)
  · refine toOp ok hm hc 0 hl fun σ1 ok1 hm1' h11 h12 h13 h14 hh1 hi1 => ?_
    refine dstep ok1 hm1' h11 .d0 rfl (by decide) rfl rfl ?_
    refine (hk (nx θ σ1 (.inl .d0) 0 0 0) (σ1.regs 2) (ok1.nx _ _ _ _) rfl rfl h14
      (fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)) ((inpA σ1 _ (by simp) (by simp) _ _ _).trans hi1)
      (h12.mono (heap_nx σ1 _ _ _ _))).mono (by linarith)

theorem EvOK.id (x : Tree) : EvOK θ supp .id x [.det 1 x] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨hk, hB⟩ := h (.det 1 x) (by simp) rfl
  have ht : tot m [.det 1 x] = m (.det 1 x) := by simp [tot, Run.det]
  rw [ht]
  have hC := Cc_ge (supp := supp)
  have hB' : Cc supp + Bd (.det 1 x) ≤ B := by
    have : ((Run.det 1 x : Run A).cost : ℤ) = 1 := rfl
    rw [this] at hB
    linarith
  obtain ⟨o, a, rfl, hl⟩ := Fm.codeShape_of_decode hF
  refine toOp ok hm hc 1 hl fun σ1 ok1 hm1' h11 h12 h13 h14 hh1 hi1 => ?_
  refine dstep ok1 hm1' h11 .d1 rfl (by decide) rfl rfl ?_
  refine (hk (nx θ σ1 (.inl .d1) 0 0 0) (σ1.regs 3) (ok1.nx _ _ _ _) rfl rfl h14
    (fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)) ((inpA σ1 _ (by simp) (by simp) _ _ _).trans hi1) ?_).mono (by linarith)
  rw [h13]
  exact hx.mono fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)

theorem EvOK.fail (x : Tree) : EvOK θ supp .fail x [] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  rw [tot_nil]
  obtain ⟨o, a, rfl, hl | hl⟩ := Fm.codeShape_of_decode hF
  · refine toOp ok hm hc 8 hl fun σ1 ok1 hm1' h11 h12 h13 h14 hh1 hi1 => ?_
    have hrec := ok1.nil_load hm1' h11
    exact sumTo_stuck ok1 hrec (by rw [hm1']; rfl) (by rw [hm1']; simp) (by
      rw [hm1']
      rintro ⟨h, -⟩
      injection h with h
      exact absurd h (by decide)) (by rw [hm1']; simp) _
  · exact noOp ok hm hc hl

end Nc.Uni
