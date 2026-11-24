/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tape.Task

/-!
# Runs of automata

A letter of a run is `none` (idle) or a letter on a channel. The value of an automaton at an input is the sum,
over all runs of length `t` that put the same word on both sides of every tape and the input on the input
channels, of their weights.
-/

namespace Nc

variable {F : Type*} [CommRing F] {Γ S J Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype J] [DecidableEq J] [Fintype Q] [DecidableEq Q]

/-- A letter of a run. -/
abbrev Letter (S J Γ : Type*) := Option (Ch S J × Γ)

/-- What a run emits. -/
def emit (o : List (Letter S J Γ)) : Ch S J → List Γ := proj o.reduceOption

theorem emit_append (o₁ o₂ : List (Letter S J Γ)) (z : Ch S J) : emit (o₁ ++ o₂) z = emit o₁ z ++ emit o₂ z := by
  simp [emit, List.reduceOption_append, proj_append]

theorem length_emit_le (o : List (Letter S J Γ)) (z : Ch S J) : (emit o z).length ≤ o.length := by
  have h1 := sum_length_proj o.reduceOption
  have h2 := List.reduceOption_length_le o
  exact (Finset.single_le_sum (f := fun z => (proj o.reduceOption z).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ z)).trans (h1.le.trans h2)

/-- The run is matched: both sides of every tape agree, and the inputs are `u`. -/
def Matched (o : List (Letter S J Γ)) (u : J → List Γ) : Prop :=
  (∀ s, emit o (.tp s false) = emit o (.tp s true)) ∧ ∀ j, emit o (.inp j) = u j

instance (o : List (Letter S J Γ)) (u : J → List Γ) : Decidable (Matched o u) := by
  unfold Matched; infer_instance

/-- A product of matrices as a sum over paths. -/
theorem prod_path {K : ℕ} (M : Fin K → Matrix Q Q F) (a b : Q) :
    (List.ofFn M).prod a b = ∑ q : Fin (K + 1) → Q,
      if q 0 = a ∧ q (Fin.last K) = b then ∏ k, M k (q k.castSucc) (q k.succ) else 0 := by
  induction K generalizing a with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty]
    rw [Matrix.one_apply, ← (Equiv.funUnique (Fin 1) Q).symm.sum_comp]
    change (if a = b then 1 else 0) = ∑ q : Q, if q = a ∧ q = b then (1 : F) else 0
    by_cases h : a = b
    · simp [h]
    · have hq (q : Q) : ¬ (q = a ∧ q = b) := fun e => h (e.1.symm.trans e.2)
      simp [h, hq]
  | succ K ih =>
    have hR : (∑ q : Fin (K + 1 + 1) → Q, if q 0 = a ∧ q (Fin.last (K + 1)) = b then
        ∏ k, M k (q k.castSucc) (q k.succ) else 0) = ∑ q : Fin (K + 1) → Q,
        if q (Fin.last K) = b then M 0 a (q 0) * ∏ k : Fin K, M k.succ (q k.castSucc) (q k.succ) else 0 := by
      rw [← (Fin.consEquiv fun _ : Fin (K + 2) => Q).sum_comp, Fintype.sum_prod_type,
        Finset.sum_eq_single a]
      · refine Finset.sum_congr rfl fun q _ => ?_
        have e1 : (Fin.consEquiv fun _ : Fin (K + 2) => Q) (a, q) = (Fin.cons a q : Fin (K + 2) → Q) := rfl
        simp only [e1]
        have e2 : (Fin.cons a q : Fin (K + 2) → Q) (Fin.last (K + 1)) = q (Fin.last K) := by
          rw [← Fin.succ_last, Fin.cons_succ]
        have e3 : (Fin.cons a q : Fin (K + 2) → Q) 0 = a := rfl
        rw [e2, e3]
        simp only [true_and]
        split_ifs
        · rw [Fin.prod_univ_succ]
          rfl
        · rfl
      · intro a' _ ha'
        refine Finset.sum_eq_zero fun q _ => ite_eq_right ?_
        rintro ⟨h0, -⟩
        exact ha' h0
      · simp
    rw [hR, List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp only [ih, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single (q 0)]
    · by_cases h : q (Fin.last K) = b <;> simp [h]
    · intro c _ hc
      rw [ite_eq_right (fun hh => hc hh.1.symm), mul_zero]
    · simp

/-- The value of an automaton with transition matrices `mu`, initial state `i` and final state `e` at the input
`u`: the sum over the matched runs of length `t`. -/
def runVal (mu : Letter S J Γ → Matrix Q Q F) (i e : Q) (t : ℕ) (u : J → List Γ) : F :=
  ∑ o : Fin t → Letter S J Γ, if Matched (List.ofFn o) u then ((List.ofFn o).map mu).prod i e else 0

end Nc
