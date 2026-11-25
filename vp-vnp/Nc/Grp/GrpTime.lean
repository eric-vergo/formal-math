/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Script
import Nc.Grp.GroupProg
import Nc.G.PlayThm

/-!
# The time of GROUP at the script of a group
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

section lists

theorem sum_le_length_mul {ι : Type*} (l : List ι) (f : ι → ℕ) (c : ℕ) (h : ∀ i ∈ l, f i ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, add_comm]
    exact Nat.add_le_add (ih fun i hi => h i (by simp [hi])) (h i (by simp))

/-- Costs of writing, from the number of keys. -/
theorem putCost_le {ub Lc : ℕ} (kss : List (List (List Bool))) (h : ∀ ks ∈ kss, ∀ k ∈ ks, k.length ≤ Lc) :
    putCost ub kss ≤ (kss.map List.length).sum * (330 * (ub + Lc + 1)) + 200 * kss.length := by
  unfold putCost
  induction kss with
  | nil => simp
  | cons ks kss ih =>
    have h1 := ih fun ks' hks => h ks' (by simp [hks])
    have h2 : (ks.map fun k => ub * 90 + k.length * 60 + 330).sum ≤ ks.length * (330 * (ub + Lc + 1)) := by
      refine sum_le_length_mul _ _ _ fun k hk => ?_
      have := h ks (by simp) k hk
      nlinarith
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons, add_mul]
    omega

private theorem putCost_map {ι : Type*} {ub Lc : ℕ} (xs : List ι) (rows : ι → List (List Bool)) (count : ι → ℕ)
    (hlen : ∀ i, (rows i).length ≤ count i) (hk : ∀ i k, k ∈ rows i → k.length ≤ Lc) :
    putCost ub (xs.map rows) ≤ (xs.map count).sum * (330 * (ub + Lc + 1)) + 200 * xs.length := by
  refine (putCost_le (Lc := Lc) _ ?_).trans ?_
  · rintro ks hks k hk'
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hks
    exact hk i k hk'
  · rw [List.map_map, List.length_map]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (List.sum_le_sum fun i _ => hlen i)) _

theorem length_filter_lt (U m : ℕ) : ((List.finRange U).filter fun k => k.1 < m).length ≤ m := by
  have hnd : ((List.finRange U).filter fun k => k.1 < m).Nodup := (List.nodup_finRange U).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  calc _ ≤ (range m).card := by
        refine Finset.card_le_card_of_injOn Fin.val ?_ (fun a _ b _ e => Fin.ext e)
        intro k hk
        simpa using hk
    _ = m := Finset.card_range m

theorem length_filterMap_le {α β : Type*} (f : α → Option β) (l : List α) :
    (l.filterMap f).length = (l.filter fun a => (f a).isSome).length := by
  rw [List.length_filterMap_eq_countP, List.countP_eq_length_filter]

end lists

section group

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c : ℕ} {Gr : Type} [DecidableEq Gr]

variable (qn : Q → ℕ) (cb : Option Γ → Fin c → Bool) {M : Sys F (K + K + A') E} (P : G.Plan M U0 U1)
  (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
  (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr)
  (key : Cell M U0 U1 → List Bool) (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ)

/-- The number of units of a base party at the beginning. -/
def inN (p : Fin (K + K)) : ℕ := ∑ b, ((n p b).1 + (n b p).1)

theorem card_dom : (dom n o grp g : Finset (Cell M U0 U1)).card = evG n o grp g := by
  unfold evG
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ.filter fun p => grp p = g)]
  · refine Finset.sum_congr rfl fun p hp => ?_
    refine Finset.card_bij' (fun c _ => c.2) (fun id _ => (p, id)) ?_ ?_ ?_ ?_
    · intro c hc
      obtain ⟨h1, h2⟩ := mem_filter.1 hc
      obtain ⟨-, h3, h4⟩ := mem_dom.1 h1
      exact mem_filter.2 ⟨h3, h2 ▸ h4⟩
    · intro id hid
      obtain ⟨h1, h2⟩ := mem_filter.1 hid
      exact mem_filter.2 ⟨mem_dom.2 ⟨(mem_filter.1 hp).2, h1, h2⟩, rfl⟩
    · intro c hc
      exact Prod.ext (mem_filter.1 hc).2.symm rfl
    · intro id _
      rfl
  · intro c hc
    exact mem_filter.2 ⟨mem_univ _, (mem_dom.1 hc).1⟩

variable {qn cb P q x ρ n o grp g key dkey tg}

/-- The channels of the roles of the group. -/
theorem sum_cn_le : ∑ r ∈ univ.filter (fun r : M.R => grp (M.rp r) = g),
    ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1) ≤ evG n o grp g := by
  rw [← card_dom]
  let Sg : Finset (Σ r : M.R, Σ _ : (M.kind r.1).CnAt r.2, Fin U1) :=
    (univ.filter fun r : M.R => grp (M.rp r) = g).sigma fun r => univ.sigma fun ν => univ.filter fun k => k ≤ o ⟨r.1, ν.1⟩
  have h1 : ∑ r ∈ univ.filter (fun r : M.R => grp (M.rp r) = g),
      ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1) = Sg.card := by
    simp only [Sg]
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have h2 : (univ.filter fun k : Fin U1 => k ≤ o ⟨r.1, ν.1⟩) = Finset.Iic (o ⟨r.1, ν.1⟩) := by
      ext k; simp
    rw [h2, Fin.card_Iic]
  rw [h1]
  refine Finset.card_le_card_of_injOn (fun y => (M.rp y.1, G.Uid.new ⟨y.1.1, y.2.1.1⟩ y.2.2)) ?_ ?_
  · rintro ⟨r, ν, k⟩ hy
    simp only [Sg, Finset.coe_sigma, Finset.mem_coe, mem_filter, mem_univ, true_and, Set.mem_sigma_iff] at hy
    rw [Finset.mem_coe, mem_dom]
    refine ⟨hy.1, ?_, holds_cnAt ν k⟩
    rw [G.Plan.mem_seenAt_end]
    exact Nat.lt_succ_of_le hy.2
  · rintro ⟨⟨y, p⟩, ν, k⟩ _ ⟨⟨y', p'⟩, ν', k'⟩ _ e
    simp only [Prod.mk.injEq, G.Uid.new.injEq, Sigma.mk.injEq] at e
    obtain ⟨e1, ⟨rfl, e2⟩, rfl⟩ := e
    obtain rfl := role_eq_of_rp e1
    have : ν = ν' := Subtype.ext (eq_of_heq e2)
    subst this
    rfl

theorem holds0 (id : G.Uid (K + K) U0 M.N U1) : Holds (G.hold0 M.np) (G.hold1 M.np) (G.hold0 M.np id) id := Or.inl rfl

theorem holds1 (id : G.Uid (K + K) U0 M.N U1) : Holds (G.hold0 M.np) (G.hold1 M.np) (G.hold1 M.np id) id := Or.inr rfl

theorem length_endIns (b : G.Uid (K + K) U0 M.N U1 → UW ub) : (endIns P n o grp g key b).length ≤ evG n o grp g := by
  rw [← card_dom]
  unfold endIns
  rw [length_filterMap_le]
  set l := (((G.allIds (K + K) U0 M.N U1).filter fun id => id ∈ P.cur n o E).filter fun id =>
    (if grp (G.hold0 M.np id) = g then
      if grp (G.hold1 M.np id) = g then some (Ins.both (key (G.hold0 M.np id, id)) (key (G.hold1 M.np id, id)))
      else some (Ins.one (key (G.hold0 M.np id, id)) (uwBits (b id)))
    else if grp (G.hold1 M.np id) = g then some (Ins.one (key (G.hold1 M.np id, id)) (uwBits (b id)))
    else none).isSome) with hl
  have hnd : l.Nodup := ((Finset.nodup_toList _).filter _).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card_of_injOn
    (fun id => (if grp (G.hold0 M.np id) = g then G.hold0 M.np id else G.hold1 M.np id, id)) ?_ ?_
  · intro id hid
    rw [Finset.mem_coe, List.mem_toFinset, hl, List.mem_filter, List.mem_filter] at hid
    obtain ⟨⟨-, h1⟩, h2⟩ := hid
    have h3 := (G.Plan.mem_cur.1 (of_decide_eq_true h1)).1
    rw [Finset.mem_coe, mem_dom]
    change grp (if grp (G.hold0 M.np id) = g then G.hold0 M.np id else G.hold1 M.np id) = g ∧
      id ∈ G.Plan.seenAt n o E ∧ Holds (G.hold0 M.np) (G.hold1 M.np)
        (if grp (G.hold0 M.np id) = g then G.hold0 M.np id else G.hold1 M.np id) id
    by_cases h0 : grp (G.hold0 M.np id) = g
    · rw [ite_eq_left h0]
      exact ⟨h0, h3, holds0 id⟩
    · by_cases h1' : grp (G.hold1 M.np id) = g
      · rw [ite_eq_right h0]
        exact ⟨h1', h3, holds1 id⟩
      · simp [h0, h1'] at h2
  · intro id _ id' _ e
    exact (Prod.ext_iff.1 e).2

theorem cost_endIns {T Lc : ℕ} (hk : ∀ c, (key c).length ≤ Lc) (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    ((endIns P n o grp g key b).map (insCost T ub)).sum ≤ evG n o grp g * (2 * (ub + Lc + 1)) := by
  refine (sum_le_length_mul _ _ (2 * (ub + Lc + 1)) ?_).trans (Nat.mul_le_mul_right _ (length_endIns b))
  intro i hi
  unfold endIns at hi
  obtain ⟨id, -, hid⟩ := List.mem_filterMap.1 hi
  have hb := length_uwBits_le (b id)
  have h0 := hk (G.hold0 M.np id, id)
  have h1 := hk (G.hold1 M.np id, id)
  split_ifs at hid <;> simp only [Option.some.injEq] at hid <;> subst hid <;> simp only [insCost] <;> omega

theorem cost_role {cap T Lc X : ℕ} (hP : P.Ok cap) (hk : ∀ c, (key c).length ≤ Lc) (r : M.R)
    (hsl : Fintype.card ((M.kind r.1).SlAt r.2) ≤ X) (hcn : Fintype.card ((M.kind r.1).CnAt r.2) ≤ X) :
    insCost T ub (roleIns P n o key tg r) ≤
      ((1 + Fintype.card ((M.kind r.1).SlAt r.2)) * P.num n o r.1 +
        ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1)) * (330 * (ub + Lc + 1)) + 400 * X + 1 := by
  unfold roleIns
  simp only [insCost]
  have h1 := putCost_map (ub := ub) (Lc := Lc) (univ : Finset ((M.kind r.1).SlAt r.2)).toList
    (fun e => ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse) (fun _ => P.num n o r.1)
    (fun e => by rw [List.length_reverse, List.length_map, G.Plan.length_ids]; exact hP.card n o ⟨r.1, e.1⟩)
    (fun _ _ hm => by obtain ⟨_, _, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hm); exact hk _)
  have h2 := putCost_map (ub := ub) (Lc := Lc) (univ : Finset ((M.kind r.1).CnAt r.2)).toList
    (fun ν => ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k))
    (fun ν => (o ⟨r.1, ν.1⟩).val + 1)
    (fun ν => by simpa only [List.length_map, Nat.lt_succ_iff, Fin.le_def] using length_filter_lt U1 ((o ⟨r.1, ν.1⟩).val + 1))
    (fun _ _ hm => by obtain ⟨_, _, rfl⟩ := List.mem_map.1 hm; exact hk _)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, Finset.length_toList, Finset.card_univ] at h1
  rw [Finset.sum_map_toList, Finset.length_toList, Finset.card_univ] at h2
  set sl := Fintype.card ((M.kind r.1).SlAt r.2)
  set W := 330 * (ub + Lc + 1) with hW
  set t := P.num n o r.1
  set cs := ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1)
  have h6 : t * (ub + 1) ≤ t * W := Nat.mul_le_mul_left _ (by omega)
  have h9 : ((1 + sl) * t + cs) * W = t * W + sl * t * W + cs * W := by ring
  rw [h9]
  omega

theorem cost_roles {cap T Lc X : ℕ} (hP : P.Ok cap) (hk : ∀ c, (key c).length ≤ Lc)
    (hsl : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X) (hcn : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X)
    (hR : Fintype.card M.R ≤ X) :
    (((roleList grp g M).map (roleIns P n o key tg)).map (insCost T ub)).sum ≤
      (pdG P n o grp g + evG n o grp g) * (330 * (ub + Lc + 1)) + X * (400 * X + 1) := by
  have hnd : (roleList grp g M).Nodup := pairwise_roleList.imp fun h => h.1
  have hfin : (roleList grp g M).toFinset = univ.filter fun r : M.R => grp (M.rp r) = g := by
    ext r
    simp [mem_roleList]
  rw [List.map_map, ← List.sum_toFinset _ hnd, hfin]
  calc _ ≤ ∑ r ∈ univ.filter (fun r : M.R => grp (M.rp r) = g), ((((1 + Fintype.card ((M.kind r.1).SlAt r.2)) * P.num n o r.1 +
        ∑ ν : (M.kind r.1).CnAt r.2, ((o ⟨r.1, ν.1⟩).1 + 1)) * (330 * (ub + Lc + 1))) + (400 * X + 1)) :=
        Finset.sum_le_sum fun r _ => (cost_role hP hk r (hsl r) (hcn r)).trans (le_of_eq (Nat.add_assoc _ _ _))
    _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
        refine Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.add_le_add le_rfl sum_cn_le)) (Nat.mul_le_mul_right _ ?_)
        exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ]; exact hR)

/-- Writing bounded keys for the first entries in each row. -/
private theorem putCost_rows {N U ub Lc : ℕ} (count : Fin N → ℕ) (key : Fin N → Fin U → List Bool)
    (hk : ∀ b k, (key b k).length ≤ Lc) :
    putCost ub (List.ofFn fun b => ((List.finRange U).filter fun k => k.val < count b).map (key b)) ≤
      (∑ b, count b) * (330 * (ub + Lc + 1)) + 200 * N := by
  rw [List.ofFn_eq_map]
  simpa [← List.ofFn_eq_map, List.sum_ofFn] using
    putCost_map (ub := ub) (Lc := Lc) (List.finRange N)
      (fun b => ((List.finRange U).filter fun k => k.val < count b).map (key b)) count
      (fun b => by simpa using length_filter_lt U (count b))
      (fun b _ hm => by obtain ⟨i, _, rfl⟩ := List.mem_map.1 hm; exact hk b i)

theorem cost_body {Lc X : ℕ} (hk : ∀ c, (key c).length ≤ Lc) (hd : ∀ c, (dkey c).length ≤ Lc)
    (hS : Fintype.card (Option S) ≤ X) (hA : K + K ≤ X) (p : Fin (K + K)) :
    bodyCost ub (bodyOf ρ n key dkey p) ≤ inN n p * (330 * (ub + Lc + 1)) + X * X + 401 * X + 1 := by
  unfold bodyCost bodyOf
  simp only
  have h1 := putCost_rows (ub := ub) (Lc := Lc) (fun b => (n p b).val)
    (fun b k => key (Fin.castAdd A' p, .init p b k)) fun _ _ => hk _
  have h2 := putCost_rows (ub := ub) (Lc := Lc) (fun b => (n b p).val)
    (fun b k => if b = p then dkey (p, k) else key (Fin.castAdd A' p, .init b p k))
    (fun b k => by split <;> first | exact hd _ | exact hk _)
  have h5 : flen ((univ : Finset (Option S)).toList.map fun s => (List.ofFn fun b => rowFlag (ρ s p) b).reverse) ≤ X * X := by
    unfold flen
    rw [List.map_map]
    refine (sum_le_length_mul _ _ (K + K) fun s _ => ?_).trans ?_
    · simp
    · rw [Finset.length_toList, Finset.card_univ]
      exact Nat.mul_le_mul hS hA
  rw [List.length_ofFn, inN, Finset.sum_add_distrib, add_mul]
  omega

theorem diag_le (p : Fin (K + K)) : ((List.finRange U0).filter fun k => k.1 < (n p p).1).length ≤ inN n p := by
  refine (length_filter_lt _ _).trans ?_
  unfold inN
  exact (Nat.le_add_right _ _).trans (Finset.single_le_sum (f := fun b => (n p b).1 + (n b p).1) (fun _ _ => Nat.zero_le _)
    (mem_univ p))

theorem cost_base {T Lc X : ℕ} (hx : ∀ κ, (x κ).length ≤ T) (hk : ∀ c, (key c).length ≤ Lc) (hd : ∀ c, (dkey c).length ≤ Lc)
    (hS : Fintype.card (Option S) ≤ X) (hA : K + K ≤ X) (p : Fin (K + K)) :
    ((baseIns qn cb q x ρ n key dkey p).map (insCost T ub)).sum ≤
      T + inN n p * (660 * (ub + Lc + 1)) + X * X + 401 * X + 1 ∧
    (baseIns qn cb q x ρ n key dkey p).length ≤ 1 + inN n p := by
  have hb := cost_body (ub := ub) (Lc := Lc) (X := X) (ρ := ρ) (n := n) (key := key) (dkey := dkey) hk hd hS hA p
  have hdg := diag_le (n := n) p
  have h1 : ((((List.finRange U0).filter fun k => k.1 < (n p p).1).map fun k =>
      Ins.both (key (Fin.castAdd A' p, .init p p k)) (dkey (p, k))).map (insCost T ub)).sum ≤
      inN n p * (330 * (ub + Lc + 1)) := by
    rw [List.map_map]
    refine (sum_le_length_mul _ _ (330 * (ub + Lc + 1)) fun k _ => ?_).trans (Nat.mul_le_mul_right _ hdg)
    simp only [Function.comp, insCost]
    have a1 := hk (Fin.castAdd A' p, .init p p k)
    have a2 := hd (p, k)
    omega
  have h2 : insCost T ub (Fin.addCases (motive := fun _ => Ins)
      (fun κ => .block (qn (q κ.castSucc)) (qn (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
      (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p) ≤
      T + (inN n p * (330 * (ub + Lc + 1)) + X * X + 401 * X + 1) := by
    refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
    · rw [Fin.addCases_left]
      exact Nat.add_le_add_left (cost_body hk hd hS hA _) T
    · rw [Fin.addCases_right]
      refine Nat.add_le_add ?_ (cost_body hk hd hS hA _)
      rw [List.length_reverse, List.length_map]
      exact hx κ
  unfold baseIns
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, List.sum_cons]
    have h3 : inN n p * (660 * (ub + Lc + 1)) = inN n p * (330 * (ub + Lc + 1)) + inN n p * (330 * (ub + Lc + 1)) := by ring
    rw [h3]
    omega
  · rw [List.length_cons, List.length_map]
    omega

theorem length_roleList_le : (roleList grp g M).length ≤ Fintype.card M.R := by
  have hnd : (roleList grp g M).Nodup := pairwise_roleList.imp fun h => h.1
  rw [← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_univ _

/-- **The time of GROUP at the script of a group.** -/
theorem script_time_le {cap T Lc X ιb lh ev pd : ℕ} {bT bub : List Bool} (hT : bval bT = T) (hub : bval bub = ub)
    (hlT : bT.length ≤ Lc) (hlub : bub.length ≤ Lc) (hP : P.Ok cap) (hx : ∀ κ, (x κ).length ≤ T)
    (hk : ∀ c, (key c).length ≤ Lc) (hd : ∀ c, (dkey c).length ≤ Lc) (hS : Fintype.card (Option S) ≤ X)
    (hA : K + K ≤ X) (hR : Fintype.card M.R ≤ X) (hsl : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X)
    (hcn : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X) (hι : (baseList (A' := A') grp g).length ≤ ιb) (hιX : ιb ≤ X)
    (hlh : ∀ p : Fin (K + K), grp (Fin.castAdd A' p) = g → ∑ b, ((n p b).1 + (n b p).1) ≤ lh)
    (hev : evG n o grp g ≤ ev) (hpd : pdG P n o grp g ≤ pd) (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    (bT.length + 1) * (bval bT + 1) + (bub.length + 1) * (bval bub + 1) +
        ((script qn cb P q x ρ n o grp g key dkey tg b).map (insCost (bval bT) (bval bub))).sum +
        (script qn cb P q x ρ n o grp g key dkey tg b).length ≤
      2 * (Lc + 1) * (T + ub + 2) + ιb * T + (ev + pd + ιb * lh) * (1000 * (ub + Lc + 1)) + 1000 * X ^ 3 := by
  rw [hT, hub]
  have hX : 1 ≤ X := le_trans Fintype.card_pos hS
  -- base parties
  have c1 : (((baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey)).map (insCost T ub)).sum ≤
      ιb * (T + lh * (660 * (ub + Lc + 1)) + X * X + 401 * X + 1) := by
    rw [sum_flatMap_map]
    refine (sum_le_length_mul _ _ (T + lh * (660 * (ub + Lc + 1)) + X * X + 401 * X + 1) fun p hp => ?_).trans
      (Nat.mul_le_mul_right _ hι)
    have h1 := (cost_base (qn := qn) (cb := cb) (q := q) (ρ := ρ) (n := n) (ub := ub) (X := X) hx hk hd hS hA p).1
    have h2 : inN n p ≤ lh := hlh p (mem_baseList.1 hp)
    refine h1.trans ?_
    gcongr
  have l1 : ((baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey)).length ≤ ιb * (1 + lh) := by
    rw [List.length_flatMap]
    refine (sum_le_length_mul _ _ (1 + lh) fun p hp => ?_).trans (Nat.mul_le_mul_right _ hι)
    have h1 := (cost_base (qn := qn) (cb := cb) (q := q) (ρ := ρ) (n := n) (ub := ub) (X := X) (T := T) hx hk hd hS hA p).2
    have h2 : inN n p ≤ lh := hlh p (mem_baseList.1 hp)
    omega
  have c2 := cost_roles (ub := ub) (T := T) (X := X) (o := o) (n := n) (tg := tg) (grp := grp) (g := g) hP hk hsl hcn hR
  have l2 : ((roleList grp g M).map (roleIns P n o key tg)).length ≤ X := by
    rw [List.length_map]
    exact length_roleList_le.trans hR
  have c3 := cost_endIns (P := P) (n := n) (o := o) (grp := grp) (g := g) (T := T) hk b
  have l3 := length_endIns (P := P) (n := n) (o := o) (grp := grp) (g := g) (key := key) b
  unfold script
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append, List.length_append, List.length_append]
  generalize (((baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey)).map (insCost T ub)).sum = C1 at *
  generalize ((baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey)).length = L1 at *
  generalize (((roleList grp g M).map (roleIns P n o key tg)).map (insCost T ub)).sum = C2 at *
  generalize ((roleList grp g M).map (roleIns P n o key tg)).length = L2 at *
  generalize ((endIns P n o grp g key b).map (insCost T ub)).sum = C3 at *
  generalize (endIns P n o grp g key b).length = L3 at *
  generalize evG n o grp g = e at *
  generalize pdG P n o grp g = p at *
  have h0 : (bT.length + 1) * (T + 1) + (bub.length + 1) * (ub + 1) ≤ 2 * (Lc + 1) * (T + ub + 2) := by
    have a1 : (bT.length + 1) * (T + 1) ≤ (Lc + 1) * (T + ub + 2) := Nat.mul_le_mul (by omega) (by omega)
    have a2 : (bub.length + 1) * (ub + 1) ≤ (Lc + 1) * (T + ub + 2) := Nat.mul_le_mul (by omega) (by omega)
    calc _ ≤ (Lc + 1) * (T + ub + 2) + (Lc + 1) * (T + ub + 2) := Nat.add_le_add a1 a2
      _ = _ := by ring
  set W := ub + Lc + 1 with hW
  have hW1 : 1 ≤ W := by omega
  have b1 : ιb * (T + lh * (660 * W) + X * X + 401 * X + 1) ≤ ιb * T + 660 * (ιb * lh * W) + 403 * X ^ 3 := by
    have a1 : ιb * (X * X + 401 * X + 1) ≤ 403 * X ^ 3 := by
      calc ιb * (X * X + 401 * X + 1) ≤ X * (X * X + 401 * (X * X) + X * X) := by
            refine Nat.mul_le_mul hιX ?_
            have : X ≤ X * X := Nat.le_mul_of_pos_left _ hX
            have : 1 ≤ X * X := Nat.one_le_iff_ne_zero.2 (by positivity)
            omega
        _ = 403 * X ^ 3 := by ring
    calc ιb * (T + lh * (660 * W) + X * X + 401 * X + 1) = ιb * T + 660 * (ιb * lh * W) + ιb * (X * X + 401 * X + 1) := by
          ring
      _ ≤ _ := by omega
  have b2 : ιb * (1 + lh) ≤ X ^ 3 + ιb * lh * W := by
    have a1 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
    have a3 : ιb * lh ≤ ιb * lh * W := Nat.le_mul_of_pos_right _ hW1
    calc ιb * (1 + lh) = ιb + ιb * lh := by ring
      _ ≤ _ := by omega
  have b3 : (p + e) * (330 * W) + X * (400 * X + 1) ≤ 330 * (pd * W) + 330 * (ev * W) + 401 * X ^ 3 := by
    have a1 : X * (400 * X + 1) ≤ 401 * X ^ 3 := by
      have : X ≤ X * X := Nat.le_mul_of_pos_left _ hX
      have h2 : X * X ≤ X ^ 3 := by
        calc X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ hX
          _ = X ^ 3 := by ring
      calc X * (400 * X + 1) = 400 * (X * X) + X := by ring
        _ ≤ _ := by omega
    have a3 : p * W ≤ pd * W := Nat.mul_le_mul_right _ hpd
    have a4 : e * W ≤ ev * W := Nat.mul_le_mul_right _ hev
    calc (p + e) * (330 * W) + X * (400 * X + 1) = 330 * (p * W) + 330 * (e * W) + X * (400 * X + 1) := by ring
      _ ≤ _ := by omega
  have b4 : e * (2 * W) ≤ 2 * (ev * W) := by
    have a4 : e * W ≤ ev * W := Nat.mul_le_mul_right _ hev
    calc e * (2 * W) = 2 * (e * W) := by ring
      _ ≤ _ := by omega
  have b5 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
  have b6 : e ≤ ev * W := hev.trans (Nat.le_mul_of_pos_right _ hW1)
  have hfin : (ev + pd + ιb * lh) * (1000 * W) =
      1000 * (ev * W) + 1000 * (pd * W) + 1000 * (ιb * lh * W) := by ring
  rw [hfin]
  omega

end group

end Nc.Grp
