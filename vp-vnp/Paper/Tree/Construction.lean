/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Tree.Network

/-!
# Building the tree and its straight-line program
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset Nc Nc.G Nc.Tow Nc.Vp Unc
open Nc.Tower (U x NN ee JJ tower SL2 gen XX npair npair_sym)
open NS1 (lg)

section Build

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' N U1 : ℕ} {T : Tower h b D J r} (R : Routes T m Uu)
  {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) (Pl : Place T ch A') {ρ : ℝ} {lhat : ℕ}

/-- The stage of a node of the tree. -/
def ndStage : Nd T → ℕ
  | none => J + 1
  | some s => s.1.1

/-- The parent of a node of the tree. -/
noncomputable def ndPar (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) : Nd T → Nd T
  | none => none
  | some s => parN hh Lf s.1.1 s.2

theorem ndStage_par (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) {ν : Nd T} (hν : ν ≠ none) :
    ndStage (ndPar hh Lf ν) = ndStage ν + 1 := by
  rcases ν with _ | ⟨j, c⟩
  · exact absurd rfl hν
  · show ndStage (parN hh Lf j.1 c) = j.1 + 1
    unfold parN
    split_ifs with hj
    · rfl
    · have := j.2
      show J + 1 = j.1 + 1
      omega

theorem card_ndChildren (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) [DecidableEq (Nd T)] {ν : Nd T} (hν : ν ≠ none) :
    (univ.filter fun μ : Nd T => μ ≠ none ∧ ndPar hh Lf μ = ν).card ≤ b := by
  rcases nd_cases ν with rfl | ⟨i, hi, c', rfl⟩
  · exact absurd rfl hν
  rcases i with _ | j
  · refine le_of_eq_of_le (card_eq_zero.2 (filter_false_of_mem fun μ _ hμ => ?_)) (Nat.zero_le _)
    have := ndStage_par hh Lf hμ.1
    rw [hμ.2] at this
    exact absurd this.symm (Nat.succ_ne_zero _)
  · refine le_trans ?_ (card_children (hh := hh) (Lf := Lf) (j := j) (by omega) c')
    refine le_trans (card_le_card ?_) (card_image_le (f := fun c : T.X j => nd T j (by omega) c))
    intro μ hμ
    obtain ⟨-, hμ1, hμ2⟩ := mem_filter.1 hμ
    have hs := ndStage_par hh Lf hμ1
    rw [hμ2] at hs
    rcases nd_cases μ with rfl | ⟨i, hi', c, rfl⟩
    · exact absurd rfl hμ1
    have e : i = j := by
      simp only [ndStage, nd] at hs
      omega
    subst e
    refine mem_image.2 ⟨c, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    have h2 : parN hh Lf i c = nd T (i + 1) hi c' := hμ2
    unfold parN at h2
    rw [dif_pos hi, nd_inj] at h2
    exact h2

theorem card_ndRoot (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) [DecidableEq (Nd T)] :
    (univ.filter fun μ : Nd T => μ ≠ none ∧ ndPar hh Lf μ = none).card ≤ Fintype.card (T.X J) := by
  rw [← card_univ (α := T.X J)]
  refine le_trans (card_le_card ?_) (card_image_le (f := fun c : T.X J => nd T J le_rfl c))
  intro μ hμ
  obtain ⟨-, hμ1, hμ2⟩ := mem_filter.1 hμ
  rcases nd_cases μ with rfl | ⟨i, hi', c, rfl⟩
  · exact absurd rfl hμ1
  have h2 : parN hh Lf i c = none := hμ2
  unfold parN at h2
  split_ifs at h2 with hi
  · exact absurd h2 nd_ne_none
  · have e : i = J := by omega
    subst e
    exact mem_image.2 ⟨c, mem_univ _, rfl⟩

theorem ndStage_eq_top {ν : Nd T} : ndStage ν = J + 1 ↔ ν = none := by
  rcases ν with _ | ⟨j, c⟩
  · simp [ndStage]
  · have := j.2
    simp [ndStage]
    omega

/-- The parent of a party. -/
noncomputable def treePar (hh : 0 < h) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (p : Fin (AA + A')) : Fin (AA + A') :=
  Pl.pt (ndPar hh (lev (load R ch FL N (nn n) (oo R FL Pl o))) (Pl.pt.symm p))

/-- The load at a party: the number of units between it and its parent. -/
noncomputable def treeUp (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1) (p : Fin (AA + A')) : ℕ :=
  onN (fb (lev (load R ch FL N (nn n) (oo R FL Pl o)))) 0 (Pl.pt.symm p)

variable {R FL Pl}

theorem valid_of (n : Fin AA → Fin AA → Fin (N + 1)) (h : ∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) : Valid N (nn n) := by
  intro a
  refine le_trans (Finset.sum_le_sum fun c _ => ?_) (h a)
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl

/-- Every unit of the end is dead or lies between a chamber and its parent. -/
theorem cur_tree (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : Valid N (nn n)) {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (plan R FL Pl N N U1).good n o x)
    {u : Un R FL Pl N U1} (hu : u ∈ (plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)))
    (hd : u ∉ deadU R FL Pl N o) (hloop : hold0 (sys R FL Pl).np u ≠ hold1 (sys R FL Pl).np u) :
    ∃ s : Σ j : Fin (J + 1), T.X j, u ∈ AsU R FL Pl N n o s ∧
      s(hold0 (sys R FL Pl).np u, hold1 (sys R FL Pl).np u) =
        s(Pl.pt (some s), treePar R FL Pl hH.h_pos n o (Pl.pt (some s))) := by
  classical
  have hr := hH.r_pos
  have hb := hH.b_pos
  have hh := hH.h_pos
  have hp : ∀ mv, GoodMv R ch FL N (nn n) (oo R FL Pl o) mv := fun mv => by
    have h1 : GoodMv R ch FL N (nn n) (oo R FL Pl o) (eE R FL ((eE R FL).symm mv)) := hg ((eE R FL).symm mv)
    rwa [Equiv.apply_symm_apply] at h1
  obtain ⟨hseen, hal⟩ := cur_end hr hb hh hu
  cases u with
  | init a c kk =>
    exfalso
    have hkn := mem_seen_init.1 hseen
    have hdone : tgB T R ch a c kk = .done := hal ⟨hv, hkn⟩
    have hne : a ≠ c := fun e => by
      subst e
      exact hloop rfl
    unfold tgB at hdone
    rw [if_neg hne] at hdone
    split_ifs at hdone with hs
    exact (edgeO_hold (R := R) (ch := ch) (AA := AA) (m := m) (c := ch a) (c' := ch c) (γ := gam T ch a kk) (s := 0)
      (R.pl_pos (fun e => hne (ch.injective e)) _)).1 hdone
  | new ν kk =>
    have hko := mem_seen_new.1 hseen
    have halv : alv R ch FL N (nn n) (oo R FL Pl o) (eN R FL Pl ν) = (o ν).1 := by
      rw [alv_good _ (hp _)]
      unfold oo
      rw [Equiv.symm_apply_apply]
    have hlt : kk.1 < (o ν).1 := by
      by_contra hge
      refine hd (mem_image.2 ⟨ν, mem_univ _, ?_⟩)
      rw [Fin.le_def] at hko
      have e : kk = o ν := Fin.ext (by omega)
      rw [e]
    have hA : AlU R FL Pl N n o (Uid.new ν kk : Un R FL Pl N U1) := by
      change kk.1 < alv R ch FL N (nn n) (oo R FL Pl o) (eN R FL Pl ν)
      rw [halv]
      exact hlt
    have hdone : tgM R ch FL (eN R FL Pl ν).1 (eN R FL Pl ν).2 = .done := hal hA
    have e0 : hold0 (sys R FL Pl).np (Uid.new ν kk : Un R FL Pl N U1) =
        Pl.pt (partM R ch FL (eN R FL Pl ν).1 ((kindM R ch FL (eN R FL Pl ν).1).cnEnd (eN R FL Pl ν).2 false)) :=
      np_eq R FL Pl ν false
    have e1 : hold1 (sys R FL Pl).np (Uid.new ν kk : Un R FL Pl N U1) =
        Pl.pt (partM R ch FL (eN R FL Pl ν).1 ((kindM R ch FL (eN R FL Pl ν).1).cnEnd (eN R FL Pl ν).2 true)) :=
      np_eq R FL Pl ν true
    rw [e0, e1]
    have hmem : ∀ s, IsCh R ch FL (eN R FL Pl ν) s → (Uid.new ν kk : Un R FL Pl N U1) ∈ AsU R FL Pl N n o s :=
      fun s hs => mem_AsU_new.2 ⟨hA, hs⟩
    have hal' : alv R ch FL N (nn n) (oo R FL Pl o) (eN R FL Pl ν) ≠ 0 := by omega
    revert hdone hal' hmem
    generalize eN R FL Pl ν = w
    intro hdone hmem hal'
    rcases w with ⟨⟨x, hx⟩ | l, β⟩
    · have hnum : num R ch FL N (nn n) (oo R FL Pl o) (.inl ⟨x, hx⟩) ≠ 0 := by
        have := alv_le_num (lhat := N) (n := nn n) (o := oo R FL Pl o) (FL := FL) hr hb ⟨x, hx⟩ β
        omega
      obtain ⟨j, hj, c, h1, h2⟩ := done_hold hr hb hh hx (β := β) hdone hnum
      refine ⟨⟨⟨j, Nat.lt_succ_of_le hj⟩, c⟩, hmem _ ⟨⟨x, hx⟩, β, rfl, hdone, h1⟩, ?_⟩
      have h3 : s(partM R ch FL (.inl ⟨x, hx⟩) ((kindM R ch FL (.inl ⟨x, hx⟩)).cnEnd β false),
          partM R ch FL (.inl ⟨x, hx⟩) ((kindM R ch FL (.inl ⟨x, hx⟩)).cnEnd β true)) =
          s(nd T j hj c, parN hh (lev (load R ch FL N (nn n) (oo R FL Pl o))) j c) := h2
      have h4 := congrArg (Sym2.map Pl.pt) h3
      simp only [Sym2.map_mk] at h4
      rw [h4, treePar, Equiv.symm_apply_apply]
      rfl
    · simp [tgM] at hdone

/-- The law moves at a node have no more layers than the node has units. -/
theorem layers_le_seen (hH : THypR FL ρ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (hg : ∀ x, (plan R FL Pl N N U1).good n o x) (p : Fin (AA + A')) :
    ∑ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true),
      (plan R FL Pl N N U1).num n o r'.1 ≤
    ((Plan.seenAt n o (Fintype.card (Mv T R ch FL))).filter
      (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card := by
  classical
  have key : ∀ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true),
      ∃ ν : (sys R FL Pl).N, ν.1 = r'.1 ∧ (∃ d, (sys R FL Pl).np ν d = p) ∧
        (plan R FL Pl N N U1).num n o r'.1 ≤ (o ν).1 := by
    rintro ⟨x, ro⟩ hr'
    obtain ⟨-, hrp, hlaw⟩ := mem_filter.1 hr'
    have hch : ∀ mv : Mv T R ch FL, mv.isRight = true → ∀ ro : (kindM R ch FL mv).Ro,
        GoodMv R ch FL N (nn n) (oo R FL Pl o) mv →
        ∃ ν : (kindM R ch FL mv).Cn, (∃ d, (kindM R ch FL mv).cnEnd ν d = ro) ∧
          num R ch FL N (nn n) (oo R FL Pl o) mv ≤ oo R FL Pl o ⟨mv, ν⟩ := by
      rintro (y | l) hl ro hgood
      · simp at hl
      obtain ⟨ν, hν⟩ := hH.near (FL.ro l.2.2.2 ro)
      refine ⟨(FL.cn l.2.2.2).symm ν, ?_, hgood.2 _⟩
      have h1 := FL.ends l.2.2.2 ((FL.cn l.2.2.2).symm ν)
      rw [Equiv.apply_symm_apply] at h1
      have h2 : FL.ro l.2.2.2 ro ∈ s(T.cN ν, T.dN ν) := by
        rcases hν with hν | hν <;> simp [hν]
      rw [← h1, Sym2.mem_iff] at h2
      rcases h2 with h2 | h2
      · exact ⟨false, ((FL.ro l.2.2.2).injective h2).symm⟩
      · exact ⟨true, ((FL.ro l.2.2.2).injective h2).symm⟩
    obtain ⟨ν, ⟨d, hd⟩, hle⟩ := hch (eE R FL x) hlaw ro (hg x)
    refine ⟨⟨x, ν⟩, rfl, ⟨d, ?_⟩, ?_⟩
    · rw [← hrp]
      exact congrArg (fun z => (sys R FL Pl).rp ⟨x, z⟩) hd
    · have e : (eN R FL Pl).symm ⟨eE R FL x, ν⟩ = ⟨x, ν⟩ := by
        rw [Equiv.symm_apply_eq]
        rfl
      unfold oo at hle
      rw [e] at hle
      exact hle
  choose ν hν1 hν2 hν3 using key
  let Fr : ∀ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true),
      Finset (Un R FL Pl N U1) := fun r' hr' =>
    (univ.filter fun k : Fin U1 => k.1 < (plan R FL Pl N N U1).num n o r'.1).image (Uid.new (ν r' hr'))
  rw [← Finset.sum_attach]
  calc _ = ∑ q ∈ (univ.filter fun r' : (sys R FL Pl).R =>
        (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true).attach, (Fr q.1 q.2).card := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [card_image_of_injective _ (fun k k' e => (Uid.new.inj e).2), card_fin_lt']
        exact (hν3 q.1 q.2).trans (o _).2.le
    _ = ((univ.filter fun r' : (sys R FL Pl).R =>
        (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true).attach.biUnion fun q => Fr q.1 q.2).card := by
        rw [card_biUnion]
        intro q _ q' _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro u hu hu'
        obtain ⟨k, -, rfl⟩ := mem_image.1 hu
        obtain ⟨k', -, e⟩ := mem_image.1 hu'
        apply hne
        have e1 : (ν q'.1 q'.2).1 = (ν q.1 q.2).1 := congrArg Sigma.fst (Uid.new.inj e).1
        rw [hν1, hν1] at e1
        obtain ⟨⟨x, ro⟩, hq⟩ := q
        obtain ⟨⟨x', ro'⟩, hq'⟩ := q'
        simp only at e1
        subst e1
        have a1 := (mem_filter.1 hq).2.1
        have a2 := (mem_filter.1 hq').2.1
        obtain rfl : ro = ro' := (sys R FL Pl).inj x' (a1.trans a2.symm)
        rfl
    _ ≤ _ := by
        refine card_le_card fun u hu => ?_
        obtain ⟨q, -, hu⟩ := mem_biUnion.1 hu
        obtain ⟨k, hk, rfl⟩ := mem_image.1 hu
        refine mem_filter.2 ⟨mem_seen_new.2 ?_, ?_⟩
        · rw [Fin.le_def]
          have := (mem_filter.1 hk).2
          have := hν3 q.1 q.2
          omega
        · obtain ⟨d, hd⟩ := hν2 q.1 q.2
          cases d
          · exact Or.inl hd.symm
          · exact Or.inr hd.symm

end Build

section Good

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' N U1 ℓ : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'}

/-- "Every possible outcome is good, by Theorem thm:laws(b), the triangle inequality over the tℓ layers, and λ ≥ 1." -/
theorem thm_tree_poss_good (hℓ : 0 < ℓ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (x : Fin (Fintype.card (Mv T R ch FL))) (hp : (Tow.plan R FL Pl N N U1).Poss n o ℓ x) :
    (Tow.plan R FL Pl N N U1).good n o x := by
  refine poss_good hℓ ?_
  obtain ⟨ι, hι⟩ := hp
  refine ⟨ι, fun ν => ?_⟩
  have h1 : (eN R FL Pl).symm ⟨eE R FL x, ν⟩ = ⟨x, ν⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  unfold oo
  rw [h1]
  exact hι ν

end Good

section Program

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}
variable {Inp ι : Type} {Dd Y p TM : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}
variable {nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)} {oI : Inp → (sys R FL Pl).N → Fin U1}

/-- The program of the tower plan, with the parents and the loads. -/
theorem tree_slp (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hB2 : Bnd2 R FL Pl U0 U1 Y TM) (hh : 0 < h) (hb : 0 < b)
    (hS : SlpN inp p H) (hn : ∀ a c, (fun x => ((nI x a c : Fin (U0 + 1)) : ℕ)) ∈ H)
    (ho : ∀ ν, (fun x => ((oI x ν : Fin U1) : ℕ)) ∈ H) (lhat : ℕ) :
    ∃ H', SlpN inp (p + Y ^ 16) H' ∧ Units nI oI lhat TM H' ∧
      HostOk hh (fun x => load R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x))) H' ∧
      ∀ (j : ℕ) (_ : j ≤ J) (c : T.X j), (fun x => fb (lev (load R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)))) j c) ∈ H' := by
  have hR : Rng (nX nI) (oX oI : Inp → NM R FL (ch := ch) → ℕ) U0 U1 := rng
  have hS0 : SY inp Y p 0 H := by
    unfold SY
    rw [Nat.zero_mul, Nat.add_zero]
    exact hS
  have hb0 : Base (nX nI) (oX oI : Inp → NM R FL (ch := ch) → ℕ) H := ⟨hn, fun ν => ho _⟩
  obtain ⟨H1, s1, u1, f1⟩ := after_stage hA hB hR hb hS0 hb0 (lhat := lhat)
  obtain ⟨H2, s2, u2, f2⟩ := units_stage hA hB hB2 s1 f1
  obtain ⟨H3, s3, u3, f3⟩ := host_stage hh (L := fun x => load R ch FL lhat (nX nI x) (oX oI x)) hA hB s2
    (fun j i => u2 (f1.isMin j i))
  obtain ⟨H4, s4, u4, f4⟩ := fb_stage (L := fun x => load R ch FL lhat (nX nI x) (oX oI x)) hA hB
    (fun x τ => ld_le (hR.n x) (hR.o x) _ τ) s3 (fun τ => u3 (u2 (f1.load τ)))
  refine ⟨H4, ?_, (f2.weaken u3).weaken u4, fun j hj c c' => u4 (f3 j hj c c'), f4⟩
  refine SlpN.le hA.zero_lt ?_ s4
  have h3 := hA.three
  have h4 : 0 + 11 + 8 * Y + 9 + 1 + 1 ≤ Y ^ 4 := by
    have e1 : Y ^ 4 = Y ^ 3 * Y := by ring
    have e2 : 3 ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left h3 3
    have e3 : 3 ^ 3 * Y ≤ Y ^ 3 * Y := Nat.mul_le_mul_right _ e2
    omega
  have h5 : (0 + 11 + 8 * Y + 9 + 1 + 1) * Y ^ 12 ≤ Y ^ 16 := by
    calc _ ≤ Y ^ 4 * Y ^ 12 := Nat.mul_le_mul_right _ h4
      _ = Y ^ 16 := by ring
  exact Nat.add_le_add_left h5 p

/-- Parents are computed: the indicator of "q is the parent of p". -/
theorem par_computed {U0' : ℕ} {n' : Inp → Fin AA → Fin AA → Fin (U0' + 1)} {o' : Inp → (sys R FL Pl).N → Fin U1}
    (hh : 0 < h) (hH : HostOk hh (fun x => load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x))) H) (a q : Fin (AA + A')) :
    (ind fun x => treePar R FL Pl hh (n' x) (o' x) a = q) ∈ H ∪ {(fun _ => 0), (fun _ => 1)} := by
  classical
  have hconst : ∀ P : Prop, (ind fun _ : Inp => P) ∈ H ∪ {(fun _ => 0), (fun _ => 1)} := by
    intro P
    by_cases hP : P
    · refine Or.inr (Or.inr (funext fun x => ?_))
      exact ind_true (P := fun _ : Inp => P) hP
    · refine Or.inr (Or.inl (funext fun x => ?_))
      exact ind_false (P := fun _ : Inp => P) hP
  rcases nd_cases (Pl.pt.symm a) with e | ⟨j, hj, c, e⟩
  · simp only [treePar, e, ndPar]
    exact hconst _
  simp only [treePar, e]
  by_cases hjJ : j < J
  · rcases nd_cases (Pl.pt.symm q) with eq | ⟨i, hi, c', eq⟩
    · have : ∀ x, ¬ (Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) := by
        intro x hx
        have := congrArg Pl.pt.symm hx
        rw [Equiv.symm_apply_apply, eq] at this
        simp only [ndPar, nd, parN, dif_pos (show j + 1 ≤ J by omega)] at this
        exact absurd this (Option.some_ne_none _)
      rw [show (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
        fun _ => False from funext fun x => eq_false (this x)]
      exact hconst _
    · by_cases hij : i = j + 1
      · subst hij
        refine Or.inl ?_
        have e2 : (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
            fun x => hostj hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) c = c' := by
          funext x
          rw [← Equiv.eq_symm_apply, eq]
          simp only [ndPar, nd, parN, dif_pos (show j + 1 ≤ J by omega)]
          simp
        rw [e2]
        exact hH j hjJ c c'
      · have : ∀ x, ¬ (Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) := by
          intro x hx
          have := congrArg Pl.pt.symm hx
          rw [Equiv.symm_apply_apply, eq] at this
          have h1 := congrArg ndStage this
          rw [ndStage_par hh _ nd_ne_none] at h1
          exact hij h1.symm
        rw [show (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
          fun _ => False from funext fun x => eq_false (this x)]
        exact hconst _
  · have e2 : (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
        fun _ => Pl.pt none = q := by
      funext x
      simp only [ndPar, nd, parN, dif_neg (show ¬ j + 1 ≤ J by omega)]
    rw [e2]
    exact hconst _

end Program

end Paper
