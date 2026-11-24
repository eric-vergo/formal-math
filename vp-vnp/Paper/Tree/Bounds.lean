/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Tree.Construction

/-!
# Packet counts and resource bounds for the tree
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset Nc Nc.G Nc.Tow Nc.Vp Unc
open Nc.Tower (U x NN ee JJ tower SL2 gen XX npair npair_sym)
open NS1 (lg)

section Numbers

theorem lg_two {M : ℕ} (hM : 2 ≤ M) : 2 ≤ lg M := by
  unfold lg
  have := Nat.log_pos (b := 2) (n := M) (by norm_num) hM
  omega

/-- A constant times a power is a higher power. -/
theorem const_mul_pow_le {L : ℕ} (hL : 2 ≤ L) {k e C : ℕ} (h : k + e ≤ C) : k * L ^ e ≤ L ^ C := by
  calc k * L ^ e ≤ L ^ k * L ^ e :=
        Nat.mul_le_mul_right _ ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hL k))
    _ = L ^ (k + e) := (pow_add _ _ _).symm
    _ ≤ L ^ C := Nat.pow_le_pow_right (by omega) h

/-- The constant in front of the bounds for loads. -/
def cKap (c : ℕ) : ℕ := 2 * c * (c * (c * (2 * c + 1) ^ 7 * c * (1 + 2 * c ^ 2)))

theorem kapB_tree {c m X M J N : ℕ} (hX : X ≤ c * M) (hm : m ≤ c * (J + 1) ^ 7) (hJ : J + 1 ≤ (2 * c + 1) * lg M) :
    2 * c * kapB c m X N ≤ cKap c * (lg M ^ 7 * M * (N + M ^ 2)) := by
  have h1 : N + 2 * X ^ 2 ≤ (1 + 2 * c ^ 2) * (N + M ^ 2) := by
    have : X ^ 2 ≤ (c * M) ^ 2 := Nat.pow_le_pow_left hX 2
    nlinarith
  unfold kapB
  calc 2 * c * (c * (m * X * (N + 2 * X ^ 2))) ≤
      2 * c * (c * (c * ((2 * c + 1) ^ 7 * lg M ^ 7) * (c * M) * ((1 + 2 * c ^ 2) * (N + M ^ 2)))) := by
        have := m_le hm hJ
        gcongr
    _ = _ := by unfold cKap; ring

/-- The gain, as a power of M. -/
theorem gain_rpow {B A M X q : ℕ} (hq : 0 < q) (hM : 0 < M) (hX : M ≤ X) (h : B ^ q * X ^ 1 ≤ A ^ q) :
    (B : ℝ) ≤ (A : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : ((B : ℝ) * (M : ℝ) ^ (1 / (q : ℝ))) ^ q ≤ (A : ℝ) ^ q := by
    rw [mul_pow, ← Real.rpow_natCast ((M : ℝ) ^ (1 / (q : ℝ))) q, ← Real.rpow_mul hM0.le,
      one_div_mul_cancel (by exact_mod_cast hq.ne'), Real.rpow_one]
    have h2 : B ^ q * M ≤ A ^ q := (Nat.mul_le_mul_left _ (by rwa [pow_one])).trans h
    exact_mod_cast h2
  have h3 := le_of_pow_le_pow_left₀ hq.ne' (Nat.cast_nonneg A) h1
  rw [Real.rpow_neg hM0.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h3

/-- Powers of a constant times Z are powers of Z. -/
theorem const_pow_le {c Z a C : ℕ} (hZ : 2 ≤ Z) (h : (c + 4) * a ≤ C) : ((c + 3) * Z) ^ a ≤ Z ^ C := by
  calc ((c + 3) * Z) ^ a ≤ (Z ^ (c + 3) * Z) ^ a := by
        gcongr
        exact (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hZ _)
    _ = Z ^ ((c + 4) * a) := by rw [← pow_succ, ← pow_mul]
    _ ≤ Z ^ C := Nat.pow_le_pow_right (by omega) h

end Numbers

section Lemmas

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' N U1 ℓ c : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {ρ : ℝ}

/-- Units are few: the bounds in numbers. -/
theorem tree_nums {c M N X J m : ℕ} (hc : 1 ≤ c) (hM : 2 ≤ M) (hN : 1 ≤ N) (hX : X ≤ c * M) (hJ : J + 1 ≤ X)
    (hm : m ≤ c * (J + 1) ^ 7) :
    c ≤ ((c + 3) * M) ^ 9 ∧ m ≤ ((c + 3) * M) ^ 9 ∧ X ≤ ((c + 3) * M) ^ 9 ∧ M ≤ ((c + 3) * M) ^ 9 ∧
      ((c + 3) * M) ^ 9 ≤ ((c + 3) * (M * N)) ^ 30 ∧ N ≤ ((c + 3) * (M * N)) ^ 30 ∧
      capB c m X N N * (c + c) + 1 ≤ ((c + 3) * (M * N)) ^ 30 := by
  obtain ⟨G, hG⟩ : ∃ G, G = (c + 3) * (M * N) := ⟨_, rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ G0, G0 = (c + 3) * M := ⟨_, rfl⟩
  rw [← hG, ← hG0]
  have hG0G : G0 ≤ G := by rw [hG0, hG]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hN)
  have hXG : X ≤ G0 := by rw [hG0]; exact hX.trans (Nat.mul_le_mul_right _ (by omega))
  have hcG : c + 3 ≤ G0 := by rw [hG0]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hMG : M ≤ G0 := by rw [hG0]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hNG : N ≤ G := by
    rw [hG]
    exact (Nat.le_mul_of_pos_left _ (by omega : 0 < M)).trans (Nat.le_mul_of_pos_left _ (by omega))
  have q : ∀ a a', a ≤ a' → G0 ^ a ≤ G0 ^ a' := fun a a' ha => Nat.pow_le_pow_right (by omega) ha
  have p : ∀ a a', a ≤ a' → G ^ a ≤ G ^ a' := fun a a' ha => Nat.pow_le_pow_right (by omega) ha
  have hG9 : G0 ≤ G0 ^ 9 := Nat.le_self_pow (by norm_num) _
  have hG30 : G ≤ G ^ 30 := Nat.le_self_pow (by norm_num) _
  have hm8 : m ≤ G0 ^ 8 := by
    calc m ≤ c * (J + 1) ^ 7 := hm
      _ ≤ G0 * G0 ^ 7 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (hJ.trans hXG) 7)
      _ = G0 ^ 8 := by ring
  refine ⟨by omega, hm8.trans (q 8 9 (by norm_num)), by omega, by omega,
    (Nat.pow_le_pow_left hG0G 9).trans (p 9 30 (by norm_num)), by omega, ?_⟩
  have hm8' : m ≤ G ^ 8 := hm8.trans (Nat.pow_le_pow_left hG0G 8)
  have h1 : kapB c m X N ≤ G ^ 15 := by
    unfold kapB
    calc c * (m * X * (N + 2 * X ^ 2)) ≤ G * (G ^ 8 * G * (G + G * G ^ 2)) := by
          gcongr <;> omega
      _ = G ^ 11 + G ^ 13 := by ring
      _ ≤ G ^ 13 + G ^ 13 := Nat.add_le_add_right (p 11 13 (by norm_num)) _
      _ = 2 * G ^ 13 := by ring
      _ ≤ G * G ^ 13 := Nat.mul_le_mul_right _ (by omega)
      _ = G ^ 14 := by ring
      _ ≤ G ^ 15 := p 14 15 (by norm_num)
  have h2 : capB c m X N N ≤ G ^ 18 := by
    unfold capB
    have e1 : G ≤ G ^ 17 := Nat.le_self_pow (by norm_num) _
    calc N + 2 + 3 * c * kapB c m X N ≤ G + G + G * G * G ^ 15 := by gcongr <;> omega
      _ = G + G + G ^ 17 := by ring
      _ ≤ G ^ 17 + G ^ 17 + G ^ 17 := by omega
      _ = 3 * G ^ 17 := by ring
      _ ≤ G * G ^ 17 := Nat.mul_le_mul_right _ (by omega)
      _ = G ^ 18 := by ring
  calc capB c m X N N * (c + c) + 1 ≤ G ^ 18 * (G + G) + G ^ 19 := by
        gcongr <;> first | omega | exact Nat.one_le_pow _ _ (by omega)
    _ = 3 * G ^ 19 := by ring
    _ ≤ G * G ^ 19 := Nat.mul_le_mul_right _ (by omega)
    _ = G ^ 20 := by ring
    _ ≤ G ^ 30 := p 20 30 (by norm_num)

open Classical in
/-- The children of a node are few. -/
theorem card_treeChildren (hh : 0 < h) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (q : Fin (AA + A')) :
    (univ.filter fun p => p ≠ Pl.pt none ∧ treePar R FL Pl hh n o p = q).card ≤
      (if q = Pl.pt none then Fintype.card (T.X J) else b) := by
  obtain ⟨ν, rfl⟩ := Pl.pt.surjective q
  have h1 : (univ.filter fun p => p ≠ Pl.pt none ∧ treePar R FL Pl hh n o p = Pl.pt ν).card ≤
      (univ.filter fun μ : Nd T => μ ≠ none ∧ ndPar hh (lev (load R ch FL N (nn n) (oo R FL Pl o))) μ = ν).card := by
    refine card_le_card_of_injOn Pl.pt.symm ?_ Pl.pt.symm.injective.injOn
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_filter.1 (mem_coe.1 hp)
    refine mem_coe.2 (mem_filter.2 ⟨mem_univ _, fun e => h1 ?_, Pl.pt.injective h2⟩)
    rw [← Equiv.apply_symm_apply Pl.pt p, e]
  by_cases hν : ν = none
  · subst hν
    rw [ite_eq_left rfl]
    exact h1.trans (card_ndRoot _ _)
  · rw [ite_eq_right fun e => hν (Pl.pt.injective e)]
    exact h1.trans (card_ndChildren _ _ hν)

open Classical in
/-- The units at one node. -/
theorem tree_node_le (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : Valid N (nn n)) {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x)
    (hb : b ≤ c) (hX : Fintype.card (T.X J) ≤ c) (p : Fin (AA + A')) :
    ((cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
      ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)) \ deadU R FL Pl N o)).filter
      (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card ≤ (c + 1) * BhN FL Uu AA N ρ := by
  let S := (univ : Finset (Σ j : Fin (J + 1), T.X j)).filter fun s =>
    Pl.pt (some s) = p ∨ treePar R FL Pl hH.h_pos n o (Pl.pt (some s)) = p
  refine le_trans (card_le_card (t := S.biUnion (AsU R FL Pl N n o)) ?_) ?_
  · intro u hu
    obtain ⟨hu1, hu2⟩ := mem_filter.1 hu
    obtain ⟨hu1, hu4⟩ := mem_filter.1 hu1
    obtain ⟨hu1, hu3⟩ := mem_sdiff.1 hu1
    obtain ⟨s, hs1, hs2⟩ := cur_tree hH hv hg hu1 hu3 hu4
    refine mem_biUnion.2 ⟨s, mem_filter.2 ⟨mem_univ _, ?_⟩, hs1⟩
    have h2 : p ∈ s(Pl.pt (some s), treePar R FL Pl hH.h_pos n o (Pl.pt (some s))) := by
      rw [← hs2, Sym2.mem_iff]
      exact hu2
    rw [Sym2.mem_iff] at h2
    exact h2.imp Eq.symm Eq.symm
  refine card_biUnion_le.trans ((Finset.sum_le_sum fun s _ => (card_AsU hH.r_pos hH.b_pos hH.h_pos s).trans
    (fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.gain hH.two _ (Nat.le_of_lt_succ s.1.2) _)).trans ?_)
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  calc S.card ≤ ({p} ∪ univ.filter fun v => v ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o v = p : Finset _).card := by
        refine card_le_card_of_injOn (fun s => Pl.pt (some s)) ?_ (fun s _ s' _ e => Option.some.inj (Pl.pt.injective e))
        intro s hs
        rcases (mem_filter.1 (mem_coe.1 hs)).2 with h3 | h3
        · exact mem_coe.2 (mem_union_left _ (mem_singleton.2 h3))
        · exact mem_coe.2 (mem_union_right _ (mem_filter.2
            ⟨mem_univ _, fun e => Option.some_ne_none s (Pl.pt.injective e), h3⟩))
    _ ≤ 1 + (univ.filter fun v => v ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o v = p).card :=
        (card_union_le _ _).trans (by simp)
    _ ≤ c + 1 := by
        have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o p
        split_ifs at this <;> omega

open Classical in
/-- All units of the tree. -/
theorem tree_total_le (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : Valid N (nn n)) {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x) :
    (cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
      ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)) \ deadU R FL Pl N o)).card ≤
      YhN FL Uu AA N ρ := by
  refine le_trans (card_le_card (t := univ.biUnion (AsU R FL Pl N n o)) ?_) ?_
  · intro u hu
    obtain ⟨hu, hu4⟩ := mem_filter.1 hu
    obtain ⟨hu1, hu3⟩ := mem_sdiff.1 hu
    obtain ⟨s, hs1, -⟩ := cur_tree hH hv hg hu1 hu3 hu4
    exact mem_biUnion.2 ⟨s, mem_univ _, hs1⟩
  refine card_biUnion_le.trans ((Finset.sum_le_sum fun s _ => card_AsU hH.r_pos hH.b_pos hH.h_pos s).trans ?_)
  rw [Fintype.sum_sigma, Fin.sum_univ_eq_sum_range
    (fun j => ∑ x : T.X j, fb (lev (load R ch FL N (nn n) (oo R FL Pl o))) j x) (J + 1)]
  exact sum_fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two

open Classical in
/-- The units between a party and its parent are at most the load at it. -/
theorem tree_between (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)} (hv : Valid N (nn n))
    {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x) {p : Fin (AA + A')}
    (hp : p ≠ Pl.pt none) :
    ((cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
      ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)) \ deadU R FL Pl N o)).filter
      (fun u => s(hold0 (sys R FL Pl).np u, hold1 (sys R FL Pl).np u) =
        s(p, treePar R FL Pl hH.h_pos n o p))).card ≤ treeUp R FL Pl n o p := by
  obtain ⟨ν, rfl⟩ := Pl.pt.surjective p
  rcases ν with _ | q
  · exact absurd rfl hp
  refine (card_le_card (t := AsU R FL Pl N n o q) fun u hu => ?_).trans ?_
  · obtain ⟨hu, hu2⟩ := mem_filter.1 hu
    obtain ⟨hu, hu4⟩ := mem_filter.1 hu
    obtain ⟨hu1, hu3⟩ := mem_sdiff.1 hu
    obtain ⟨s', hs1, hs2⟩ := cur_tree hH hv hg hu1 hu3 hu4
    have he := hs2.symm.trans hu2
    rcases Sym2.eq_iff.1 he with ⟨e1, -⟩ | ⟨e1, e2⟩
    · rwa [← Option.some.inj (Pl.pt.injective e1)]
    · exfalso
      simp only [treePar, Equiv.symm_apply_apply] at e1 e2
      have a1 := ndStage_par hH.h_pos (lev (load R ch FL N (nn n) (oo R FL Pl o))) (Option.some_ne_none q)
      have a2 := ndStage_par hH.h_pos (lev (load R ch FL N (nn n) (oo R FL Pl o))) (Option.some_ne_none s')
      rw [← Pl.pt.injective e1] at a1
      rw [Pl.pt.injective e2] at a2
      omega
  · refine (card_AsU hH.r_pos hH.b_pos hH.h_pos q).trans (le_of_eq ?_)
    simp only [treeUp, Equiv.symm_apply_apply]
    rfl

open Classical in
/-- The loads at one node. -/
theorem tree_up_node (hH : THypR FL ρ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (hb : b ≤ c) (hX : Fintype.card (T.X J) ≤ c) (p : Fin (AA + A')) :
    treeUp R FL Pl n o p + ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o q = p),
      treeUp R FL Pl n o q ≤ (c + 1) * BhN FL Uu AA N ρ := by
  have h1 : ∀ q, treeUp R FL Pl n o q ≤ BhN FL Uu AA N ρ := fun q => by
    rcases nd_cases (Pl.pt.symm q) with e | ⟨j, hj, x, e⟩
    · simp [treeUp, e, onN]
    · simp only [treeUp, e, onN_nd]
      exact fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.gain hH.two j hj x
  rw [add_mul, one_mul, add_comm]
  refine Nat.add_le_add ((Finset.sum_le_sum fun q _ => h1 q).trans ?_) (h1 p)
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o p
  split_ifs at this <;> omega

/-- All loads. -/
theorem tree_up_total (hH : THypR FL ρ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1) :
    ∑ p, treeUp R FL Pl n o p ≤ YhN FL Uu AA N ρ := by
  rw [← Equiv.sum_comp Pl.pt]
  simp only [treeUp, Equiv.symm_apply_apply]
  rw [Fintype.sum_option]
  simp only [onN, Nat.zero_add]
  rw [Fintype.sum_sigma, Fin.sum_univ_eq_sum_range
    (fun j => ∑ x : T.X j, fb (lev (load R ch FL N (nn n) (oo R FL Pl o))) j x) (J + 1)]
  exact sum_fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two

/-- The loads at a chamber and below its children are those at the party and its children. -/
theorem onN_le_up (hh : 0 < h) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1) (P : Nd T) :
    onN (fun j x => 8 * fb (LfO R ch FL Pl N n o) j x + 3 * chF hh (LfO R ch FL Pl N n o) j x)
        (∑ e : T.Ed J, LfO R ch FL Pl N n o J e) P ≤
      8 * (treeUp R FL Pl n o (Pl.pt P) + ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧
        treePar R FL Pl hh n o q = Pl.pt P), treeUp R FL Pl n o q) := by
  classical
  have kids : ∀ (j : ℕ) (hj : j ≤ J) (s : Finset (T.X j)),
      (∀ x ∈ s, parN hh (LfO R ch FL Pl N n o) j x = P) →
      ∑ x ∈ s, fb (LfO R ch FL Pl N n o) j x ≤ ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧
        treePar R FL Pl hh n o q = Pl.pt P), treeUp R FL Pl n o q := by
    intro j hj s hs
    have e1 : ∀ x, treeUp R FL Pl n o (Pl.pt (nd T j hj x)) = fb (LfO R ch FL Pl N n o) j x := fun x => by
      simp only [treeUp, Equiv.symm_apply_apply, onN_nd]

    rw [← Finset.sum_congr rfl fun x _ => e1 x,
      ← Finset.sum_image (f := treeUp R FL Pl n o) (g := fun x => Pl.pt (nd T j hj x))
        (fun x _ x' _ e => nd_inj.1 (Pl.pt.injective e))]
    refine Finset.sum_le_sum_of_subset fun q hq => ?_
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hq
    refine mem_filter.2 ⟨mem_univ _, fun e => nd_ne_none (Pl.pt.injective e), ?_⟩
    simp only [treePar, Equiv.symm_apply_apply]
    exact congrArg Pl.pt (hs x hx)
  rcases nd_cases P with rfl | ⟨j, hj, x, rfl⟩
  · have h1 := kids J le_rfl univ fun x _ => by
      unfold parN
      rw [dite_eq_right (by omega)]
    have h2 := T.sum_bet (LfO R ch FL Pl N n o J)
    have h3 : ∑ x, fb (LfO R ch FL Pl N n o) J x = ∑ x, T.bet (LfO R ch FL Pl N n o J) x := rfl
    simp only [onN]
    omega
  · rw [onN_nd]
    have e1 : treeUp R FL Pl n o (Pl.pt (nd T j hj x)) = fb (LfO R ch FL Pl N n o) j x := by
      simp only [treeUp, Equiv.symm_apply_apply, onN_nd]

    rw [e1]
    rcases j with _ | j
    · simp only [chF]
      omega
    · have h1 : chF hh (LfO R ch FL Pl N n o) (j + 1) x ≤ _ :=
        le_trans (le_of_eq (by rw [chF, chs, Finset.sum_filter]))
          (kids j (by omega) (univ.filter fun y => hostj hh (LfO R ch FL Pl N n o) y = x) fun y hy => by
            unfold parN
            rw [dite_eq_left hj, (mem_filter.1 hy).2])
      omega

open Classical in
/-- **Paper: proof of Theorem thm:tree, Bounds.** The Lean form of "At no time does a node hold more than a constant times
the units that it has in the end ...": relays leave copies here, so what a node ever holds, zeros in slots included, is at
most a constant times the loads at it and its children, plus (1+8m)N at a given node (m bounds the words) and twice the
dead units at it. -/
theorem thm_tree_copies (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : ∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) {o : (sys R FL Pl).N → Fin U1}
    (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x) {Sm : ℕ} (hSm : ∀ d, Fintype.card (FL.L d).Sl ≤ Sm)
    (p : Fin (AA + A')) :
    ((Plan.seenAt n o (Fintype.card (Mv T R ch FL))).filter
        (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card +
        ∑ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p),
          (1 + Fintype.card (((sys R FL Pl).kind r'.1).SlAt r'.2)) * (Tow.plan R FL Pl N N U1).num n o r'.1 ≤
      (4 + (2 * Fintype.card T.Nr * FL.G₁ + 1 + Sm) * Fintype.card FL.Di) * 8 * (treeUp R FL Pl n o p +
          ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o q = p), treeUp R FL Pl n o q) +
        (if (p : ℕ) < AA then (1 + 8 * m) * N else 0) +
        2 * ((deadU R FL Pl N o).filter (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card := by
  have hgd : ∀ mv, GoodMv R ch FL N (nn n) (oo R FL Pl o) mv := fun mv => by
    have h1 : GoodMv R ch FL N (nn n) (oo R FL Pl o) (eE R FL ((eE R FL).symm mv)) := hg ((eE R FL).symm mv)
    rwa [Equiv.apply_symm_apply] at h1
  obtain ⟨P, rfl⟩ := Pl.pt.surjective p
  have h0 := held_node_le (R := R) (Pl := Pl) (lhat := N) (n := n) (o := o) hH.h_pos hH.r_pos hH.b_pos
    (fun x ν => hgd (.inl x) ν) (fun l => hgd (.inr l)) hH.near hSm (ℓf := N) P (fun a _ => hv a)
  have h2 : isB ch P * (N + 8 * m * N) ≤ if ((Pl.pt P : Fin (AA + A')) : ℕ) < AA then (1 + 8 * m) * N else 0 := by
    unfold isB
    split_ifs with e1 e2 e2
    · exact le_of_eq (by ring)
    · obtain ⟨a, rfl⟩ := e1
      exact absurd (by rw [Pl.pt_base]; exact a.2) e2
    · simp
    · simp
  have h3 : chanN R FL Pl (Pl.pt P) ≤
      2 * ((deadU R FL Pl N o).filter (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) (Pl.pt P))).card := by
    unfold deadU chanN
    rw [Finset.filter_image, card_image_of_injective _ (fun ν ν' e => (Uid.new.inj e).1), card_filter, Finset.mul_sum]
    refine Finset.sum_le_sum fun ν _ => ?_
    rw [Fintype.sum_bool]
    by_cases e : Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) (Pl.pt P)
        (Uid.new ν (o ν) : Un R FL Pl N U1)
    · rw [ite_eq_left e]
      split_ifs <;> omega
    · rw [ite_eq_right e, ite_eq_right fun h => e (Or.inr h.symm), ite_eq_right fun h => e (Or.inl h.symm)]
      exact Nat.zero_le _
  have h4 := onN_le_up (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o P
  rw [Finset.sum_filter]
  refine le_trans h0 ?_
  calc _ ≤ _ + _ + _ := Nat.add_le_add (Nat.add_le_add h2 h3) (Nat.mul_le_mul_left _ h4)
    _ = _ := by ring

open Classical in
/-- The network is the sum of the networks on trees. -/
theorem tree_value (hH : THypR FL ρ) (hℓ : 1 ≤ ℓ) {cap : ℕ} (hcap : capN FL N Uu AA N ≤ cap)
    (hlen : ∀ d, (FL.L d).Le c ∧ (FL.L d).lam ≤ c) (hc : 1 ≤ c) (hU1 : U1 = cap * (c + c) + 1)
    {n : Fin AA → Fin AA → Fin (N + 1)} (tab : ∀ a, NodeTable F (fun a c => (n a c).1) ℓ a) :
    netValue tab = ∑ o : (sys R FL Pl).N → Fin U1, if ∀ x, (Tow.plan R FL Pl N N U1).good n o x then
      ∑ w ∈ Common (none : UW ℓ) (cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
        ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)))), ∏ p,
        groupVal (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) none
          (Plan.seenAt n o (Fintype.card (Mv T R ch FL)))
          ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL))) id
          (fun a => partyTab (Tow.plan R FL Pl N N U1) n o (startTab (sys R FL Pl) U1 n tab a) a) p w
      else 0 := by
  have hok : (Tow.plan R FL Pl N N U1).Ok (capN FL N Uu AA N) :=
    plan_ok_cap hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two
  have hgood : ∀ n o x, (Tow.plan R FL Pl N N U1).Poss n o ℓ x → (Tow.plan R FL Pl N N U1).good n o x :=
    fun n o x => thm_tree_poss_good hℓ n o x
  have hkl : ∀ x, ((sys R FL Pl).kind x).Le c ∧ ((sys R FL Pl).kind x).lam ≤ c := by
    intro x
    change (kindM R ch FL (eE R FL x)).Le c ∧ (kindM R ch FL (eE R FL x)).lam ≤ c
    rcases eE R FL x with y | l
    · exact ⟨⟨fun _ _ => hc⟩, Nat.zero_le _⟩
    · exact hlen _
  have hU1' : ∀ x, capN FL N Uu AA N * (c + ((sys R FL Pl).kind x).lam) + 1 ≤ U1 := by
    intro x
    rw [hU1]
    exact Nat.add_le_add_right (Nat.mul_le_mul hcap (Nat.add_le_add_left (hkl x).2 c)) 1
  have hU0' : 0 < U1 := by omega
  rw [← posVal_start (S := sys R FL Pl) (U1 := U1) tab,
    Paper.thm_tree_moves hok hℓ hgood (m := fun _ => c) (fun x => (hkl x).1) hU0' hU1' n
      (startTab (sys R FL Pl) U1 n tab) (fun a y y' h => startTab_congr tab a h) (fun a y h => startTab_ne_none tab a y h)]
  refine Finset.sum_congr rfl fun o _ => ?_
  by_cases hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x
  swap
  · rw [ite_eq_right hg, ite_eq_right hg]
  rw [ite_eq_left hg, ite_eq_left hg, posVal_groups _ _ _ _ _ id]

open Classical in
/-- The program that computes the trees. -/
theorem tree_computed (hH : THypR FL ρ) {V : ℕ} (hV : 3 ≤ V) (hm : m ≤ V) (hJ : J + 1 ≤ V) (hh : h ≤ V) (hr : r ≤ V)
    (hAA : AA ≤ V) (hX : Fintype.card (T.X 0) ≤ V) (hdd : Fintype.card FL.Di ≤ V) (hbV : b ≤ V)
    (hfl : Fintype.card (Sym2 T.Fl) ≤ V) (hS : ∀ d, Fintype.card (FL.L d).Sl ≤ V) (hN : N ≤ V) (hU1 : U1 ≤ V)
    (hD : 0 < D) :
    ∃ (steps : ℕ) (inp : (Fin AA × Fin AA) ⊕ (sys R FL Pl).N →
        (Fin AA → Fin AA → Fin (N + 1)) × ((sys R FL Pl).N → Fin U1) → Fin ((20 * V ^ 9) ^ 4))
      (H : Set ((Fin AA → Fin AA → Fin (N + 1)) × ((sys R FL Pl).N → Fin U1) → ℕ)),
      steps ≤ 3 * (20 * V ^ 9) ^ 16 ∧ Fintype.card (Nd T) ≤ 20 * V ^ 9 ∧ Fintype.card (Mv T R ch FL) ≤ 20 * V ^ 9 ∧
      Fintype.card (Un R FL Pl N U1) ≤ 20 * V ^ 9 ∧
      (∀ a c x, (inp (.inl (a, c)) x : ℕ) = x.1 a c) ∧ (∀ ν x, (inp (.inr ν) x : ℕ) = x.2 ν) ∧ SlpN inp steps H ∧
      (∀ p q, (ind fun x => treePar R FL Pl hH.h_pos x.1 x.2 p = q) ∈ H) ∧
      (∀ u, (ind fun x => u ∈ (Tow.plan R FL Pl N N U1).cur x.1 x.2 (Fintype.card (Mv T R ch FL))) ∈ H) ∧
      (∀ z u, (ind fun x => u ∈ (Tow.plan R FL Pl N N U1).cons x.1 x.2 z) ∈ H) ∧
      (∀ y, (fun x => (Tow.plan R FL Pl N N U1).num x.1 x.2 y) ∈ H) ∧
      (∀ p, (fun x => treeUp R FL Pl x.1 x.2 p) ∈ H) ∧
      ∀ y, (ind fun x => (Tow.plan R FL Pl N N U1).good x.1 x.2 y) ∈ H := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cards_le (R := R) (ch := ch) (FL := FL) (Pl := Pl) (U0 := N) (U1 := U1) hD
    hH.b_pos (by omega : 1 ≤ V) hh hr hm (show J ≤ V by omega) hAA hX hdd hbV hS hN hU1
  have n7 := card_Tg_le (T := T) (m := m) (AA := AA) hD hH.b_pos (by omega : 1 ≤ V) hh hr hm (show J ≤ V by omega) hAA hX
    hfl
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 20 * V ^ 9 := ⟨_, rfl⟩
  rw [← hY]
  have pw : ∀ a, a ≤ 9 → V ^ a ≤ V ^ 9 := fun a ha => Nat.pow_le_pow_right (by omega) ha
  have p2 := pw 2 (by omega)
  have p5 := pw 5 (by omega)
  have p6 := pw 6 (by omega)
  have p7 := pw 7 (by omega)
  have p1 : V ≤ V ^ 9 := Nat.le_self_pow (by norm_num) V
  have hA : Alph (Y ^ 4) Y := ⟨by omega, le_rfl⟩
  have hNM : Fintype.card (NM R FL (ch := ch)) = Fintype.card (sys R FL Pl).N := Fintype.card_congr (eN R FL Pl).symm
  have hZM : Fintype.card (ZM R FL (ch := ch)) = Fintype.card (sys R FL Pl).Z := Fintype.card_congr (eZ R FL Pl).symm
  have hWb : Wb R ch FL N U1 = Fintype.card (Un R FL Pl N U1) := by
    rw [card_Un]
    unfold Wb
    rw [hNM]
  have hAA2 : AA * AA ≤ V ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hAA hAA
  have hBd : Bnd R ch FL N U1 Y := {
    aa := by omega
    w := by rw [hWb]; omega
    nm := by rw [hNM]; omega
    mv := by omega
    tg := by omega
    nd := by omega
    fl := by omega
    di := by omega
    h := by omega
    j := by omega
    t := by unfold tend; omega
    tt := by
      rw [hWb]
      have h1 : b * Fintype.card (Sym2 T.Fl) * Fintype.card (Un R FL Pl N U1) ≤ V * V * (18 * V ^ 7) := by gcongr
      have h2 : V * V * (18 * V ^ 7) = 18 * V ^ 9 := by ring
      omega }
  have hB2 : Bnd2 R FL Pl N U1 Y 0 := {
    zm := by rw [hZM]; omega
    un := by omega
    tm := Nat.zero_le _ }
  have hYY : Y < Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ < Y ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  let inp : (Fin AA × Fin AA) ⊕ (sys R FL Pl).N →
      (Fin AA → Fin AA → Fin (N + 1)) × ((sys R FL Pl).N → Fin U1) → Fin (Y ^ 4) := fun i x => match i with
    | .inl q => ⟨(x.1 q.1 q.2).1, by have := (x.1 q.1 q.2).2; omega⟩
    | .inr ν => ⟨(x.2 ν).1, by have := (x.2 ν).2; omega⟩
  obtain ⟨H', s1, f1, g1, e1⟩ := tree_slp (R := R) (FL := FL) (Pl := Pl) hA hBd hB2 hH.h_pos hH.b_pos
    (SlpN.inputs hA.zero_lt inp) (nI := fun x => x.1) (oI := fun x => x.2) (fun a b => ⟨.inl (a, b), rfl⟩)
    (fun ν => ⟨.inr ν, rfl⟩) N
  have s2 := (s1.snoc (fun _ => ⟨0, hA.zero_lt⟩) (Or.inr (Or.inl ⟨_, rfl⟩))).snoc
    (fun _ => ⟨1, hA.one_lt⟩) (Or.inr (Or.inl ⟨_, rfl⟩))
  refine ⟨_, inp, _, ?_, by omega, by omega, by omega, fun _ _ _ => rfl, fun _ _ => rfl, s2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e0 : Fintype.card ((Fin AA × Fin AA) ⊕ (sys R FL Pl).N) = AA * AA + Fintype.card (sys R FL Pl).N := by
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [e0]
    have : Y ≤ Y ^ 16 := Nat.le_self_pow (by norm_num) _
    omega
  · intro p q
    have key := par_computed (R := R) (FL := FL) (Pl := Pl) (U0' := N) (H := H') (n' := fun x => x.1) (o' := fun x => x.2)
      hH.h_pos g1 p q
    rcases key with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · exact fun u => Or.inr (Or.inr (f1.cur u))
  · exact fun z u => Or.inr (Or.inr (f1.cons (eZ R FL Pl z) u))
  · exact fun y => Or.inr (Or.inr (f1.num (eE R FL y)))
  · intro p
    unfold treeUp
    rcases nd_cases (Pl.pt.symm p) with e | ⟨j, hj, c, e⟩
    · simp only [e, onN]
      exact Or.inr (Or.inl rfl)
    · simp only [e, onN_nd]
      exact Or.inr (Or.inr (e1 j hj c))
  · exact fun y => Or.inr (Or.inr (f1.good (eE R FL y)))

/-- **Paper: Theorem thm:tree, Start.** "Hence every edge gets at most n₀ = 4L(N+M²) units." -/
theorem thm_tree_start_units {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ} (hr : 0 < r) (hb : 0 < b)
    (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) (e : T.Ed 0) :
    load R ch FL N n o (.edge 0 e) ≤ 4 * m * (N + Fintype.card (T.X 0) ^ 2) := by
  refine (thm_tree_start hr hb e).trans ((Nat.mul_le_mul hUu le_rfl).trans ?_)
  calc 2 * Fintype.card (T.X 0) * m * (N / Fintype.card (T.X 0) + 2 * AA) =
      2 * m * (N / Fintype.card (T.X 0) * Fintype.card (T.X 0)) + 4 * m * (Fintype.card (T.X 0) * AA) := by ring
    _ ≤ 2 * m * N + 4 * m * (Fintype.card (T.X 0) * Fintype.card (T.X 0)) := by
        gcongr
        exact Nat.div_mul_le_self _ _
    _ ≤ 4 * m * N + 4 * m * (Fintype.card (T.X 0) * Fintype.card (T.X 0)) := by gcongr; omega
    _ = _ := by ring

end Lemmas

end Paper
