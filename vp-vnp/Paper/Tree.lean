/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Tree.Bounds

/-!
# Towers realizing the thin-tree decomposition
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset Nc Nc.G Nc.Tow Nc.Vp Unc
open Nc.Tower (U x NN ee JJ tower SL2 gen XX npair npair_sym)
open NS1 (lg)

section Towers

/-- More generous routes. -/
def _root_.Nc.Tow.Routes.mono {h b D J r m Uu m' Uu' : ℕ} {T : Tower h b D J r} (R : Routes T m Uu) (hm : m ≤ m')
    (hU : Uu ≤ Uu') : Routes T m' Uu' where
  rt := R.rt
  walk := R.walk
  len c c' := (R.len c c').trans hm
  use e := (R.use e).trans hU

/-- "Take the least n ≥ 1 with M ≤ |G_n|; so |G_n| = O(M)": towers of all sizes from Proposition prop:tower, whose
parts (c) and (d) give the size, the bottom and the words of the routes. -/
theorem tree_towers {A : Type} [CommRing A] {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (1 / 2 : ℝ) ^ 2 * h) (htwo : (2 : ℝ) ≤ 1 / 2 * ((2 ^ ee h : ℕ) : ℝ)) :
    ∃ c, ∀ y, 1 ≤ y → ∃ (J m Uu : ℕ) (T : Tower h (2 ^ ee h) (2 ^ ee h) J 1) (_ : Routes T m Uu) (FL : FlagLaws A T),
      FL.G₁ = VL.G₁ ∧ TCst FL ((univ : Finset VL.Di).toList.map VL.L) c (1 / 2) 1 (ee h) ∧
      y ≤ Fintype.card (T.X 0) ∧ Fintype.card (T.X 0) ≤ c * y ∧ 1 ≤ m ∧ m ≤ c * (J + 1) ^ 7 ∧
      Uu ≤ 2 * Fintype.card (T.X 0) * m := by
  classical
  have h2 : 2 ≤ h := by omega
  obtain ⟨C, hC⟩ := prop_tower h h3
  have hee2 : 2 ≤ ee h := by
    unfold Nc.Tower.ee
    have : 3 * 2 ≤ h * (h - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  have heeh : ee h ≤ h ^ 2 - 1 := by
    unfold Nc.Tower.ee
    have h4 : h * (h - 1) ≤ h * h := Nat.mul_le_mul_left _ (by omega)
    have h5 : h ^ 2 = h * h := by ring
    have h6 : 9 ≤ h * h := Nat.mul_le_mul h3 h3
    omega
  let S : ℕ := Nat.card (SL2 h)
  let g : ℕ → ℕ := fun n => Nat.card (Nc.Tower.G h n)
  have hg0 : ∀ n, g (n + 1) = g n * 2 ^ (h ^ 2 - 1) := fun n => (hC n).2.2.2.2.2.1
  have hg1 : ∀ n, 0 < g n := fun n => Nat.card_pos
  have hS : 0 < S := Nat.card_pos
  obtain ⟨c, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ : ∃ c : ℕ, h ≤ c ∧ 2 ^ ee h ≤ c ∧ 3 ≤ c ∧
      Fintype.card (NN h) ≤ c ∧ VL.G₁ ≤ c ∧ Fintype.card VL.Di ≤ c ∧ Fintype.card (Sym2 (U h)) ≤ c ∧
      ∑ d, Fintype.card (VL.L d).Sl ≤ c ∧ ∑ d, ∑ i, ∑ ν, (VL.L d).len i ν ≤ c ∧ ∑ d, (VL.L d).lam ≤ c ∧
      ⌈√(h : ℝ) * ((1 : ℕ) : ℝ) + √VL.C₁ * VL.a₁⌉₊ ≤ c ∧ S * 2 ^ ee h ≤ c ∧ g 0 ≤ c ∧ 2 ^ (h ^ 2 - 1) ≤ c ∧ C + 1 ≤ c := by
    let l : List ℕ := [h, 2 ^ ee h, 3, Fintype.card (NN h), VL.G₁, Fintype.card VL.Di, Fintype.card (Sym2 (U h)),
      ∑ d, Fintype.card (VL.L d).Sl, ∑ d, ∑ i, ∑ ν, (VL.L d).len i ν, ∑ d, (VL.L d).lam,
      ⌈√(h : ℝ) * ((1 : ℕ) : ℝ) + √VL.C₁ * VL.a₁⌉₊, S * 2 ^ ee h, g 0, 2 ^ (h ^ 2 - 1), C + 1]
    have hl : ∀ a ∈ l, a ≤ l.sum := fun a ha => List.single_le_sum (fun _ _ => Nat.zero_le _) a ha
    refine ⟨l.sum, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_,
      hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_⟩ <;> simp only [l, List.mem_cons, true_or, or_true]
  refine ⟨c, fun y hy => ?_⟩
  -- the least size
  have hg2 : ∀ n, 2 ^ n ≤ g n := by
    intro n
    induction n with
    | zero => exact hg1 0
    | succ n ih =>
      rw [hg0, pow_succ]
      exact Nat.mul_le_mul ih (Nat.le_self_pow (by omega) 2)
  have hex : ∃ n, y ≤ g n := ⟨y, (Nat.lt_two_pow_self).le.trans (hg2 y)⟩
  let n := Nat.find hex
  have hn1 : y ≤ g n := Nat.find_spec hex
  have hn2 : g n ≤ c * y := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]
      exact k13.trans (Nat.le_mul_of_pos_right _ hy)
    · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have h4 : ¬ y ≤ g k := Nat.find_min hex (by
        show k < n
        omega)
      rw [hk, hg0, mul_comm c y]
      exact Nat.mul_le_mul (by omega) k14
  have hnJ : n ≤ JJ h n := by
    unfold Nc.Tower.JJ
    rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
    exact Nat.mul_le_mul_right _ heeh
  obtain ⟨hG0, -, -, -, hXJ, -, hword⟩ := hC n
  obtain ⟨R⟩ := Nc.Tower.exists_routes (h := h) (n := n) h2 hword
  have hX0 : Fintype.card ((tower h n h2).X 0) = g n := hG0
  have hX0' : Fintype.card (XX h n 0) = g n := hG0
  have hXJ0 : 0 < Fintype.card ((tower h n h2).X (JJ h n)) :=
    Fintype.card_pos_iff.2 ⟨((QuotientGroup.mk 1 : XX h n (JJ h n)))⟩
  refine ⟨JJ h n, (C + 1) * (n + 1) ^ 7, 2 * Fintype.card ((tower h n h2).X 0) * ((C + 1) * (n + 1) ^ 7),
    tower h n h2, R.mono (Nat.mul_le_mul_right _ (by omega)) ?_, towFlag VL h2 n, rfl, ?_, ?_, ?_, ?_, ?_, le_rfl⟩
  · rw [hX0, hX0', ← mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  · have hlaw : ∀ d : VL.Di, VL.L d ∈ (univ : Finset VL.Di).toList.map VL.L := fun d =>
      List.mem_map.2 ⟨d, Finset.mem_toList.2 (mem_univ d), rfl⟩
    refine ⟨⟨one_pos, by positivity, by omega, by omega, by norm_num, by norm_num, hgain, htwo, ?_⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, hXJ0, ?_, ?_, ?_, ?_, hlaw, ?_⟩
    · intro (f : U h)
      have h4 := npair_sym (⟨0, by omega⟩ : Fin (h - 1)) f
      rcases Sym2.eq_iff.1 h4 with ⟨e1, -⟩ | ⟨e1, -⟩
      · exact ⟨npair ⟨0, by omega⟩ f, Or.inl e1.symm⟩
      · exact ⟨npair ⟨0, by omega⟩ f, Or.inr e1.symm⟩
    · exact k1
    · exact k2
    · omega
    · refine (Fintype.card_congr (Equiv.refl _)).le.trans (?_ : Fintype.card (NN h) ≤ c)
      exact k4
    · exact k5
    · refine (Fintype.card_congr (Equiv.refl _)).le.trans (?_ : Fintype.card VL.Di ≤ c)
      exact k6
    · refine (Fintype.card_congr (Equiv.refl _)).le.trans (?_ : Fintype.card (Sym2 (U h)) ≤ c)
      exact k7
    · intro d
      have h4 : Fintype.card (VL.L d).Sl ≤ ∑ d, Fintype.card (VL.L d).Sl :=
        Finset.single_le_sum (f := fun d => Fintype.card (VL.L d).Sl) (fun _ _ => Nat.zero_le _) (mem_univ d)
      exact h4.trans k8
    · exact hXJ.le.trans k12
    · show √(h : ℝ) * ((1 : ℕ) : ℝ) + √VL.C₁ * VL.a₁ ≤ (c : ℝ)
      exact (Nat.le_ceil _).trans (Nat.cast_le.2 k11)
    · have h4 : (1 : ℝ) / (1 - 1 / 2) = ((2 : ℕ) : ℝ) := by norm_num
      rw [h4]
      exact Nat.cast_le.2 (by omega)
    · omega
    · have h4 : (1 / 2 : ℝ) ^ ee h * (((2 ^ ee h : ℕ) : ℝ)) ^ 1 = 1 := by
        push_cast
        rw [pow_one, ← mul_pow]
        norm_num
      exact h4.le
    · intro L hL
      rw [List.mem_map] at hL
      obtain ⟨d, -, rfl⟩ := hL
      refine ⟨⟨fun i ν => ?_⟩, ?_⟩
      · have h4 : (VL.L d).len i ν ≤ ∑ ν, (VL.L d).len i ν :=
          Finset.single_le_sum (f := fun ν => (VL.L d).len i ν) (fun _ _ => Nat.zero_le _) (mem_univ ν)
        have h5 : ∑ ν, (VL.L d).len i ν ≤ ∑ i, ∑ ν, (VL.L d).len i ν :=
          Finset.single_le_sum (f := fun i => ∑ ν, (VL.L d).len i ν) (fun _ _ => Nat.zero_le _) (mem_univ i)
        have h6 : ∑ i, ∑ ν, (VL.L d).len i ν ≤ ∑ d, ∑ i, ∑ ν, (VL.L d).len i ν :=
          Finset.single_le_sum (f := fun d => ∑ i, ∑ ν, (VL.L d).len i ν) (fun _ _ => Nat.zero_le _) (mem_univ d)
        exact h4.trans (h5.trans (h6.trans k9))
      · have h4 : (VL.L d).lam ≤ ∑ d, (VL.L d).lam :=
          Finset.single_le_sum (f := fun d => (VL.L d).lam) (fun _ _ => Nat.zero_le _) (mem_univ d)
        exact h4.trans k10
  · rw [hX0]; exact hn1
  · rw [hX0]; exact hn2
  · exact Nat.mul_pos (by omega) (by positivity)
  · exact Nat.mul_le_mul k15 (Nat.pow_le_pow_left (by omega) 7)

end Towers

section Thm

variable {F : Type} [CommRing F] {h b D J m Uu AA N M ℓ : ℕ} {T : Tower h b D J 1}

/-- The exponent of the trees of a tower with the constant c. -/
def cTree (c : ℕ) : ℕ := (c + 4) * 200000 + cKap c * (2 * c + 1) + 7 + (4 + (2 * c * c + 1 + c) * c) * 8 +
  (1 + 8 * (c * (2 * c + 1) ^ 7))

/-- The tower load estimates give both the per-node saving and the total packet bound. -/
private theorem tree_load_bounds (FL : FlagLaws F T) {laws : List (G.Law F)} {c q C : ℕ} {ρ : ℝ}
    (hC : TCst FL laws c ρ 1 q) (hm1 : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m)
    (hM : 2 ≤ M) (hX1 : M ≤ Fintype.card (T.X 0)) (hAX : AA ≤ Fintype.card (T.X 0))
    (hCc : (c + 4) * 200000 + cKap c * (2 * c + 1) + 7 ≤ C)
    (hkap : 2 * c * kapB c m (Fintype.card (T.X 0)) N ≤ cKap c * (lg M ^ 7 * M * (N + M ^ 2))) :
    (((c + 1) * BhN FL Uu AA N ρ : ℕ) : ℝ) ≤
        (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2) ∧
      YhN FL Uu AA N ρ ≤ lg M ^ C * M * (N + M ^ 2) := by
  have hl := lg_two hM
  have hq : 0 < q := by have := hC.pq; omega
  have hBh : (BhN FL Uu AA N ρ : ℝ) ≤ ((cKap c * lg M ^ 7 : ℕ) : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) *
      (N + (M : ℝ) ^ 2) := by
    refine (gain_rpow hq (by omega) hX1 (BhN_le (lh := N) hC hm1 hUu hAX)).trans ?_
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    calc ((2 * c * kapB c m (Fintype.card (T.X 0)) N : ℕ) : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) ≤
        ((cKap c * (lg M ^ 7 * M * (N + M ^ 2)) : ℕ) : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hkap) (Real.rpow_nonneg hM0.le _)
      _ = _ := by
          rw [sub_eq_add_neg, Real.rpow_add hM0, Real.rpow_one]
          push_cast
          ring
  have hnode : (((c + 1) * BhN FL Uu AA N ρ : ℕ) : ℝ) ≤
      (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2) := by
    have h3 : (c + 1) * (cKap c * lg M ^ 7) ≤ lg M ^ C := by
      rw [← mul_assoc]
      refine const_mul_pow_le hl ?_
      calc (c + 1) * cKap c + 7 ≤ (2 * c + 1) * cKap c + 7 := by gcongr; omega
        _ ≤ C := by rw [mul_comm (2 * c + 1)]; omega
    calc (((c + 1) * BhN FL Uu AA N ρ : ℕ) : ℝ) ≤
        ((c + 1 : ℕ) : ℝ) * (((cKap c * lg M ^ 7 : ℕ) : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2)) := by
          rw [Nat.cast_mul]
          exact mul_le_mul_of_nonneg_left hBh (Nat.cast_nonneg _)
      _ = (((c + 1) * (cKap c * lg M ^ 7) : ℕ) : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2) := by
          push_cast; ring
      _ ≤ _ := by gcongr
  have htot : YhN FL Uu AA N ρ ≤ lg M ^ C * M * (N + M ^ 2) := by
    have h1 := YhN_le (lh := N) hC hm1 hUu hAX
    have h2 : cKap c * c * lg M ^ 7 ≤ lg M ^ C := const_mul_pow_le hl (by
      have : cKap c * c ≤ cKap c * (2 * c + 1) := Nat.mul_le_mul_left _ (by omega)
      omega)
    calc YhN FL Uu AA N ρ ≤ 2 * c * kapB c m (Fintype.card (T.X 0)) N * c := h1
      _ ≤ cKap c * (lg M ^ 7 * M * (N + M ^ 2)) * c := Nat.mul_le_mul_right _ hkap
      _ = cKap c * c * lg M ^ 7 * M * (N + M ^ 2) := by ring
      _ ≤ _ := by gcongr
  exact ⟨hnode, htot⟩

open Classical in
/-- The thin trees of one tower. -/
theorem exists_thinTrees (R : Routes T m Uu) (FL : FlagLaws F T) {laws : List (G.Law F)} {c q : ℕ} {ρ : ℝ}
    (hC : TCst FL laws c ρ 1 q) {C : ℕ} (hC0 : cTree c ≤ C) (hm1 : 1 ≤ m)
    (hm : m ≤ c * (J + 1) ^ 7) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hM : 2 ≤ M)
    (hX1 : M ≤ Fintype.card (T.X 0)) (hX2 : Fintype.card (T.X 0) ≤ c * M) (hAA : AA ≤ M) (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) :
    Nonempty (ThinTrees F laws AA N ℓ M b FL.G₁ C (1 / (q : ℝ))) := by
  classical
  obtain ⟨hCc, hC8, hC9⟩ : (c + 4) * 200000 + cKap c * (2 * c + 1) + 7 ≤ C ∧ (4 + (2 * c * c + 1 + c) * c) * 8 ≤ C ∧
      1 + 8 * (c * (2 * c + 1) ^ 7) + 7 ≤ C := by unfold cTree at hC0; omega
  have hH := hC.toTHypR
  have hc := hC.c_pos
  have hl := lg_two hM
  have hJX := two_pow_le (T := T) hC.D_two hC.bot_pos
  have hdep : J + 1 ≤ (2 * c + 1) * lg M := depth_le hJX (hX2.trans (Nat.mul_le_mul_left _ (by omega)))
  have hJ1 : J + 1 ≤ Fintype.card (T.X 0) := Nat.succ_le_of_lt ((Nat.lt_two_pow_self (n := J)).trans_le hJX)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := tree_nums (N := N) hc hM hN hX2 hJ1 hm
  have hAX : AA ≤ Fintype.card (T.X 0) := hAA.trans hX1
  obtain ⟨ch⟩ := Function.Embedding.nonempty_of_card_le (α := Fin AA) (β := T.X 0) (by rwa [Fintype.card_fin])
  obtain ⟨Pl⟩ := exists_place T ch
  have hkap := kapB_tree (N := N) hX2 hm hdep
  obtain ⟨U1, hU1⟩ : ∃ U1, U1 = capB c m (Fintype.card (T.X 0)) N N * (c + c) + 1 := ⟨_, rfl⟩
  rw [← hU1] at a7
  obtain ⟨W, hW⟩ : ∃ W, W = ((c + 3) * M) ^ 9 := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = ((c + 3) * (M * N)) ^ 30 := ⟨_, rfl⟩
  rw [← hW] at a1 a2 a3 a4 a5
  rw [← hV] at a5 a6 a7
  have hcV : c ≤ V := a1.trans a5
  have hMN : 2 ≤ M * N := le_trans hM (Nat.le_mul_of_pos_right _ hN)
  obtain ⟨hnode, htot⟩ := tree_load_bounds FL hC hm1 hUu hM hX1 hAX hCc hkap
  have hne : ∀ p, p ≠ Pl.pt none → Pl.pt.symm p ≠ none := fun p hp e => hp (by
    rw [← Equiv.apply_symm_apply Pl.pt p, e])
  have hV3 : 3 ≤ V := hV ▸ (le_trans (Nat.le_add_left 3 c)
    (Nat.le_mul_of_pos_right (c + 3) (show 0 < M * N by omega))).trans (Nat.le_self_pow (by norm_num) _)
  obtain ⟨steps, inp, H, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := tree_computed (R := R) (FL := FL)
    (Pl := Pl) (U1 := U1) (N := N) hH (V := V) hV3 (by omega) (by omega) (hC.h_le.trans hcV) (hC.r_le.trans hcV)
    (by omega) (by omega) (hC.di_le.trans hcV) (hC.b_le.trans hcV) (hC.fl_le.trans hcV)
    (fun d => (hC.sl_le d).trans hcV) a6 a7 (by have := hC.D_two; omega)
  refine ⟨{
    A' := extra T AA
    E := Fintype.card (Mv T R ch FL)
    U1 := U1
    sys := sys R FL Pl
    plan := Tow.plan R FL Pl N N U1
    stage := fun p => ndStage (Pl.pt.symm p)
    depth := J + 1
    root := Pl.pt none
    par := treePar R FL Pl hH.h_pos
    dead := deadU R FL Pl N
    isLaw := fun x => (eE R FL x).isRight
    depth_le := hdep.trans ((le_of_eq (by rw [pow_one])).trans (const_mul_pow_le hl (show 2 * c + 1 + 1 ≤ C by omega)))
    stage_le := fun p => ?_
    stage_given := fun a => by rw [← Pl.pt_base, Equiv.symm_apply_apply]; rfl
    stage_root := fun p => by rw [ndStage_eq_top, Equiv.symm_apply_eq]
    stage_par := fun n o p hp => by
      rw [treePar, Equiv.symm_apply_apply]
      exact ndStage_par _ _ (hne p hp)
    children_le := fun n o x hx => by
      have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o x
      rwa [ite_eq_right hx] at this
    root_children_le := fun n o => by
      have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o (Pl.pt none)
      rw [ite_eq_left rfl] at this
      exact this.trans (hC.bot.trans (by omega))
    dead_le := fun o => ?_
    kinds := fun x => ?_
    law_stage := fun r' hr' => ?_
    U1_pos := by rw [hU1]; exact Nat.succ_pos _
    cap := capN FL N Uu AA N
    ok := plan_ok_cap hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two
    up := treeUp R FL Pl
    good_iff := fun n o x => ?_
    poss_good := fun n o x hp => thm_tree_poss_good hℓ n o x hp
    edge := fun n hv o hg u hu => ?_
    between_le := fun n hv o hg p hp => tree_between hH (valid_of n hv) hg hp
    up_node := fun n hv o hg p => ?_
    up_total := fun n hv o hg => ?_
    copies_le := fun n hv o hg p => ?_
    value := fun n hv tab => tree_value hH hℓ (capN_capB hC hm1 hUu hAX) (fun d => hC.len _ (hC.mem d)) hc hU1 tab
    computed := ?_ }⟩
  · have e : ∀ ν : (kindM R ch FL (eE R FL x)).Cn, oo R FL Pl o ⟨eE R FL x, ν⟩ = (o ⟨x, ν⟩ : ℕ) := fun ν => by
      unfold oo
      have h1 : (eN R FL Pl).symm ⟨eE R FL x, ν⟩ = ⟨x, ν⟩ := by
        rw [Equiv.symm_apply_eq]
        rfl
      rw [h1]
    change GoodMv R ch FL N (nn n) (oo R FL Pl o) (eE R FL x) ↔ if (eE R FL x).isRight = true then
      b * ∑ ν : (kindM R ch FL (eE R FL x)).Cn, (o ⟨x, ν⟩).val ^ 2 ≤
          FL.G₁ * num R ch FL N (nn n) (oo R FL Pl o) (eE R FL x) ^ 2 ∧
        ∀ ν : (kindM R ch FL (eE R FL x)).Cn, num R ch FL N (nn n) (oo R FL Pl o) (eE R FL x) ≤ (o ⟨x, ν⟩ : ℕ)
      else ∀ ν : (kindM R ch FL (eE R FL x)).Cn, (o ⟨x, ν⟩).val = num R ch FL N (nn n) (oo R FL Pl o) (eE R FL x)
    simp only [← e]
    clear e
    generalize eE R FL x = mv
    rcases mv with y | l
    · exact Iff.rfl
    · simp only [Sum.isRight_inr, ite_true, GoodMv, GoodL, Nat.one_mul]
      rfl
  · rcases Pl.pt.symm p with _ | ⟨j, x⟩
    · exact le_rfl
    · exact Nat.le_of_lt (show j.1 < J + 1 from j.2)
  · obtain ⟨n1', -⟩ := cards_le (R := R) (ch := ch) (FL := FL) (Pl := Pl) (U0 := 0) (U1 := 0)
      (show 0 < D by have := hC.D_two; omega) hC.b_pos (show 1 ≤ W by omega) (hC.h_le.trans a1) (hC.r_le.trans a1) a2
      (show J ≤ W by omega) (show AA ≤ W by omega) a3 (hC.di_le.trans a1) (hC.b_le.trans a1)
      (fun d => (hC.sl_le d).trans a1) (Nat.zero_le _) (Nat.zero_le _)
    refine (card_image_le.trans (le_of_eq card_univ)).trans (n1'.trans ?_)
    rw [hW, ← pow_mul]
    calc 17 * ((c + 3) * M) ^ (9 * 6) ≤ ((c + 3) * M) ^ 3 * ((c + 3) * M) ^ (9 * 6) := by
          refine Nat.mul_le_mul_right _ ?_
          have := Nat.pow_le_pow_left (le_trans (Nat.le_add_left 3 c) (Nat.le_mul_of_pos_right (c + 3) (show 0 < M by omega))) 3
          omega
      _ = ((c + 3) * M) ^ 57 := by rw [← pow_add]
      _ ≤ M ^ C := const_pow_le hM (by omega)
  · change if (eE R FL x).isRight = true then kindM R ch FL (eE R FL x) ∈ laws else kindM R ch FL (eE R FL x) = relay F
    rcases eE R FL x with y | l
    · simp [kindM]
    · simp only [Sum.isRight_inr, ite_true]
      exact hC.mem _
  · change 0 < ndStage (Pl.pt.symm (Pl.pt (partM R ch FL (eE R FL r'.1) r'.2)))
    rw [Equiv.symm_apply_apply]
    have key : ∀ mv : Mv T R ch FL, mv.isRight = true → ∀ ro, 0 < ndStage (partM R ch FL mv ro) := by
      rintro (y | l) hl ro
      · simp at hl
      · exact Nat.succ_pos _
    exact key _ hr' _
  · obtain ⟨hu, hl'⟩ := mem_filter.1 hu
    obtain ⟨hu, hd⟩ := mem_sdiff.1 hu
    obtain ⟨s, -, hs⟩ := cur_tree hH (valid_of n hv) hg hu hd hl'
    exact ⟨_, fun e => Option.some_ne_none s (Pl.pt.injective e), hs⟩
  · exact (Nat.cast_le.2 (tree_up_node hH n o hC.b_le hC.bot p)).trans hnode
  · exact (tree_up_total hH n o).trans htot
  · -- copies
    refine (thm_tree_copies (R := R) (FL := FL) (Pl := Pl) hH hv hg hC.sl_le p).trans ?_
    refine Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ ?_) ?_) (Nat.mul_le_mul_right _ (by omega))
    · refine le_trans ?_ hC8
      have a1 := hC.nr_le
      have a2 := hC.g_le
      have a3 := hC.di_le
      gcongr
    · split_ifs
      · refine Nat.mul_le_mul_right _ ?_
        have h1 : 1 ≤ lg M ^ 7 := Nat.one_le_pow _ _ (by omega)
        calc 1 + 8 * m ≤ lg M ^ 7 + 8 * (c * ((2 * c + 1) ^ 7 * lg M ^ 7)) :=
              Nat.add_le_add h1 (Nat.mul_le_mul_left _ (m_le hm hdep))
          _ = (1 + 8 * (c * (2 * c + 1) ^ 7)) * lg M ^ 7 := by ring
          _ ≤ lg M ^ C := const_mul_pow_le hl hC9
      · exact le_rfl
  · -- the program
    have hpow : ∀ e, e ≤ 200000 → ((c + 3) * (M * N)) ^ e ≤ (M * N) ^ C := fun e he =>
      const_pow_le hMN ((Nat.mul_le_mul_left _ he).trans (by omega))
    have hG3 : 3 ≤ (c + 3) * (M * N) :=
      le_trans (Nat.le_add_left 3 c) (Nat.le_mul_of_pos_right (c + 3) (show 0 < M * N by omega))
    obtain ⟨G, hG⟩ : ∃ G, G = (c + 3) * (M * N) := ⟨_, rfl⟩
    rw [← hG] at hV hpow hG3
    have hYG : 20 * V ^ 9 ≤ G ^ 273 := by
      rw [hV, ← pow_mul]
      calc 20 * G ^ (30 * 9) ≤ G ^ 3 * G ^ (30 * 9) := Nat.mul_le_mul_right _ (by
            have := Nat.pow_le_pow_left hG3 3; omega)
        _ = G ^ 273 := by rw [← pow_add]
    have hyp : 20 * V ^ 9 ≤ (M * N) ^ C := hYG.trans (hpow 273 (by norm_num))
    refine ⟨_, steps, inp, H, ?_, ?_, ?_, b2.trans hyp, ?_, b3.trans hyp, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩
    · refine (Nat.pow_le_pow_left hYG 4).trans ?_
      rw [← pow_mul]
      exact hpow _ (by norm_num)
    · refine b0.trans ?_
      calc 3 * (20 * V ^ 9) ^ 16 ≤ G * (G ^ 273) ^ 16 := Nat.mul_le_mul hG3 (Nat.pow_le_pow_left hYG 16)
        _ = G ^ 4369 := by rw [← pow_mul, ← pow_succ']
        _ ≤ _ := hpow _ (by norm_num)
    · rw [card_party Pl]
      exact b1.trans hyp
    · refine a7.trans (le_trans ?_ hyp)
      have : V ≤ V ^ 9 := Nat.le_self_pow (by norm_num) V
      omega

/-- **Paper: Theorem thm:tree.** "There is a constant C with the following property. Let M ≥ 2, let
ℓ, N ≥ 1, and let a network over an A-algebra have at most M nodes, no unit from a node to itself,
and at most N units at each node. Its value is the sum, over a set of choices o (sequences of good
outcomes), of values of networks with the following properties. Put Λ = (lg M)^C, where lg M = ⌊log
M⌋+1, and γ = 1/log b. (a) The nodes form a rooted tree of depth at most Λ, by stages: the given
nodes are of stage 0, every node but the root has its parent in the next stage and at most b
children, and the root has at most C. (b) A set of at most M^C dead units may join any two nodes.
All others join a node and its parent; their number is at most ΛM^(1−γ)(N+M²) for one node, its
children included, and ΛM(N+M²) in all. (c) The table of a node is the given one (or 1) times the
tables of the moves at it, summed over the units that they have used up. At stage 0 these are tests
only; elsewhere they are tests and table entries of laws, and the numbers of layers of the law moves
at a node add up to at most the number of bits of all units that it ever holds. (d) The parents, the
units present, the units and numbers of the moves, and which outcomes are good are computed from o
and the given numbers of units by a straight-line program with at most (MN)^C steps on numbers below
(MN)^C. A step is an input, a constant, or an arbitrary function of two earlier results, given by
its table (a binary operation). The program does not depend on the numbers of units, the outcomes or
the tables." The tests are relays, and the laws are the fixed list, mapped to R. The last sentence
of (c), on the layers of the law moves at a node, is not formalized: Proposition prop:pieces does
not use it. Units from a node to itself are also allowed: they stay, and their node sums over them
(the printed formula is the case without them, cutUnits_id_cur). The operations of (d) are those of
a straight-line program that may depend on M, N and ℓ. -/
theorem thm_tree {A : Type} [CommRing A] {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ C : ℕ, ∀ (R : Type) [CommRing R] [Algebra A R] (M AA N ℓ : ℕ), 2 ≤ M → AA ≤ M → 1 ≤ N → 1 ≤ ℓ →
      Nonempty (ThinTrees R (((univ : Finset VL.Di).toList.map VL.L).map (lawMap (algebraMap A R))) AA N ℓ M
        (2 ^ ee h) (goodBound VL.C₁ VL.a₁) C (1 / Real.logb 2 ((2 ^ ee h : ℕ) : ℝ))) := by
  have he : 2 ≤ ee h := by
    unfold Nc.Tower.ee
    have : 3 * 2 ≤ h * (h - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  have htwo : (2 : ℝ) ≤ 1 / 2 * ((2 ^ ee h : ℕ) : ℝ) := by
    have : (4 : ℝ) ≤ ((2 ^ ee h : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by norm_num) he
    linarith
  obtain ⟨c, hc⟩ := tree_towers
    { VL with
      G₁ := goodBound VL.C₁ VL.a₁
      G₁_le := Nat.floor_le (by have := VL.C₁_nonneg; positivity)
      L2 := fun d i => (VL.L2 d i).trans (Nat.le_floor VL.G₁_le) } h3 (by linarith) htwo
  refine ⟨cTree c, fun R _ _ M AA N ℓ hM hAA hN hℓ => ?_⟩
  obtain ⟨J, m, Uu, T, Rt, FL, hG, hC, hX1, hX2, hm1, hm2, hUu⟩ := hc M (by omega)
  have e : Real.logb 2 ((2 ^ ee h : ℕ) : ℝ) = (ee h : ℝ) := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  simp only [] at hG
  rw [e, ← hG]
  exact exists_thinTrees Rt (flagMap (algebraMap A R) FL) (TCst_map _ hC) le_rfl hm1 hm2 hUu hM hX1 hX2 hAA hN hℓ

end Thm

end Paper
