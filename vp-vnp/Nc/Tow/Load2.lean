/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Flow

/-!
# The tower plan: loads of a stage
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

theorem alv_le_num (x : {x : RM T m AA // okR T R ch x}) (ν : (kindM R ch FL (.inl x)).Cn) :
    alv R ch FL lhat n o ⟨.inl x, ν⟩ ≤ num R ch FL lhat n o (.inl x) := by
  rw [alv, alvN_inl]
  split <;> simp

theorem load_def (τ : Tg T m AA) : load R ch FL lhat n o τ = bt R ch lhat n τ +
    ∑ ν : NM R FL (ch := ch), if tgM R ch FL ν.1 ν.2 = τ then alv R ch FL lhat n o ν else 0 := rfl

/-- A load that comes from few channels. -/
theorem load_le_sum {τ : Tg T m AA} (s : Finset (NM R FL (ch := ch))) (hbt : bt R ch lhat n τ = 0)
    (hs : ∀ ν : NM R FL (ch := ch), tgM R ch FL ν.1 ν.2 = τ → alv R ch FL lhat n o ν ≠ 0 → ν ∈ s) :
    load R ch FL lhat n o τ ≤ ∑ ν ∈ s, alv R ch FL lhat n o ν := by
  rw [load_def, hbt, Nat.zero_add, ← Finset.sum_filter]
  rw [← Finset.sum_filter_ne_zero]
  refine Finset.sum_le_sum_of_subset ?_
  intro ν hν
  obtain ⟨h1, h2⟩ := mem_filter.1 hν
  exact hs ν (mem_filter.1 h1).2 h2

theorem edgeO_cases (e : Option (T.Ed 0)) : (edgeO T e : Tg T m AA) = .done ∨ ∃ e', e = some e' ∧
    (edgeO T e : Tg T m AA) = .edge 0 e' := by
  cases e
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl, rfl⟩

/-- Targets of initial units. -/
theorem tgB_cases (a c : Fin AA) (k : ℕ) : (tgB T R ch a c k = .done) ∨
    (∃ hm, tgB T R ch a c k = .nxt (.start a c (gam T ch a k) ⟨0, hm⟩)) ∨
    ∃ e, (R.path (ch a) (ch c) (gam T ch a k))[0]? = some e ∧ tgB T R ch a c k = .edge 0 e ∧ a ≠ c ∧
      ¬ 1 < R.pl (ch a) (ch c) (gam T ch a k) := by
  have hle := (R.pl_le (ch a) (ch c) (gam T ch a k)).trans (R.length_path (ch a) (ch c) (gam T ch a k))
  unfold tgB
  by_cases hac : a = c
  · rw [ite_eq_left hac]; exact Or.inl rfl
  · rw [ite_eq_right hac]
    by_cases hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (gam T ch a k)
    · rw [dite_eq_left hs]; exact Or.inr (Or.inl ⟨hs.1, rfl⟩)
    · rw [dite_eq_right hs]
      rcases edgeO_cases (m := m) (AA := AA) ((R.path (ch a) (ch c) (gam T ch a k))[0]?) with h1 | ⟨e, h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨e, h1, h2, hac, fun hh => hs ⟨by omega, hh⟩⟩)

theorem bt_zero {τ : Tg T m AA} (hτ : ∀ a c k, tgB T R ch a c k ≠ τ) : bt R ch lhat n τ = 0 := by
  simp_all [bt]

theorem bt_edge_succ (j : Fin J) (e : T.Ed (j + 1)) : bt R ch lhat n (.edge j.succ e) = 0 := by
  refine bt_zero fun a c k hk => ?_
  rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hk
  · simp at hk
  · simp at hk
  · exact absurd (Tg.edge.inj hk).1.symm (Fin.succ_ne_zero j)

theorem bt_seg (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    bt R ch lhat n (.seg j i ω q : Tg T m AA) = 0 := by
  refine bt_zero fun a c k hk => ?_
  rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hk <;> simp at hk

theorem bt_mid (j : Fin J) (e : T.Ed j) (s : Fin 4) : bt R ch lhat n (.nxt (.mid j e s) : Tg T m AA) = 0 := by
  refine bt_zero fun a c k hk => ?_
  rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hk <;> simp at hk

section Targets

/-- Which channels of relays have a target of a given kind. -/
theorem tgR_edge_succ {x : RM T m AA} {ν : Bool} {j : Fin J} {e' : T.Ed (j + 1)}
    (hx : tgR T R ch x ν = .edge j.succ e') : ∃ e, x = .mid j e 2 ∧ ν = false ∧ T.πE e = e' := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j', i, e⟩ | ⟨j', e, s⟩ | e
  · rcases tgR_start_cases (R := R) (ch := ch) a c γ s ν with
      ⟨_, _, he⟩ | ⟨k, _, he⟩ <;> rw [he] at hx
    · simp at hx
    · rcases edgeO_cases (m := m) (AA := AA) (T := T) _ with h' | ⟨_, -, h'⟩ <;> rw [h'] at hx
      · simp at hx
      · exact absurd (Tg.edge.inj hx).1.symm (Fin.succ_ne_zero j)
  · simp [tgR] at hx
  · rcases tgR_mid_cases (R := R) (ch := ch) j' e s ν with he | ⟨_, _, he⟩ | ⟨rfl, rfl, he⟩ |
      ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨_, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he] at hx <;>
        simp only [Fin.isValue, reduceCtorEq, Tg.edge.injEq, Fin.succ_inj] at hx
    obtain ⟨rfl, h2⟩ := hx
    exact ⟨e, rfl, rfl, eq_of_heq h2⟩
  · simp [tgR] at hx

theorem tgR_seg {x : RM T m AA} {ν : Bool} {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i} {q : Sym2 T.Fl}
    (hx : tgR T R ch x ν = .seg j i ω q) : ∃ e : T.Ed j, ν = false ∧ T.ty e = i ∧
      ((x = .mid j e 1 ∧ (T.πV (T.vx i (T.e0 e)) : T.V (j + 1) i) = ω ∧ s(T.co i (hst T i (T.e0 e)), T.co i (T.e0 e)) = q) ∨
      (x = .mid j e 3 ∧ (T.πV (T.vx i (T.e1 e)) : T.V (j + 1) i) = ω ∧ s(T.co i (hst T i (T.e1 e)), T.co i (T.e1 e)) = q)) := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j', i', e⟩ | ⟨j', e, s⟩ | e
  · rcases tgR_start_cases (R := R) (ch := ch) a c γ s ν with
      ⟨_, _, he⟩ | ⟨k, _, he⟩ <;> rw [he] at hx
    · simp at hx
    · rcases edgeO_cases (m := m) (AA := AA) (T := T) _ with h' | ⟨_, -, h'⟩ <;>
        rw [h'] at hx <;> simp at hx
  · simp [tgR] at hx
  · rcases tgR_mid_cases (R := R) (ch := ch) j' e s ν with he | ⟨rfl, rfl, he⟩ | ⟨_, _, he⟩ |
      ⟨rfl, rfl, he⟩ | ⟨_, _, _, he⟩ | ⟨_, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he] at hx <;>
        simp only [Fin.isValue, reduceCtorEq, Tg.seg.injEq] at hx
    · obtain ⟨rfl, rfl, h3, h4⟩ := hx
      exact ⟨e, rfl, rfl, Or.inl ⟨rfl, eq_of_heq h3, h4⟩⟩
    · obtain ⟨rfl, rfl, h3, h4⟩ := hx
      exact ⟨e, rfl, rfl, Or.inr ⟨rfl, eq_of_heq h3, h4⟩⟩
  · simp [tgR] at hx

theorem tgR_mid {x : RM T m AA} {ν : Bool} {j : Fin J} {e : T.Ed j} {s : Fin 4}
    (hx : tgR T R ch x ν = .nxt (.mid j e s)) : ν = true ∧
      ((s = 1 ∧ x = .mid j e 0) ∨
      (s = 2 ∧ ((x = .mid j e 0 ∧ hst T (T.ty e) (T.e0 e) = T.π (T.e0 e)) ∨ x = .mid j e 1)) ∨
      (s = 3 ∧ x = .mid j e 2)) := by
  rcases x with ⟨a, c, γ, s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e'
  · rcases tgR_start_cases (R := R) (ch := ch) a c γ s' ν with
      ⟨_, _, he⟩ | ⟨k, _, he⟩ <;> rw [he] at hx
    · simp at hx
    · rcases edgeO_cases (m := m) (AA := AA) (T := T) _ with h' | ⟨_, -, h'⟩ <;>
        rw [h'] at hx <;> simp at hx
  · simp [tgR] at hx
  · rcases tgR_mid_cases (R := R) (ch := ch) j' e' s' ν with he | ⟨_, _, he⟩ | ⟨_, _, he⟩ |
      ⟨_, _, he⟩ | ⟨rfl, rfl, -, he⟩ | ⟨hs, rfl, he⟩ | ⟨rfl, rfl, -, he⟩ <;> rw [he] at hx <;>
        simp only [Fin.isValue, reduceCtorEq, Tg.nxt.injEq, RM.mid.injEq] at hx
    · obtain ⟨rfl, h2, rfl⟩ := hx
      obtain rfl := eq_of_heq h2
      simp
    · obtain ⟨rfl, h2, rfl⟩ := hx
      obtain rfl := eq_of_heq h2
      rcases hs with ⟨rfl, hh⟩ | rfl
      · exact ⟨rfl, Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, hh⟩⟩)⟩
      · exact ⟨rfl, Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)⟩
    · obtain ⟨rfl, h2, rfl⟩ := hx
      obtain rfl := eq_of_heq h2
      simp
  · simp [tgR] at hx

end Targets

theorem sum_union_le {κ : Type*} [DecidableEq κ] (s t : Finset κ) (f : κ → ℕ) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  rw [← Finset.sum_union_inter]
  exact Nat.le_add_right _ _

theorem sum_biUnion_le' {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (s : Finset ι) (t : ι → Finset κ) (f : κ → ℕ) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (sum_union_le _ _ _).trans (Nat.add_le_add_left ih _)

/-- The end segments on a pair, by edges. -/
theorem nEnd_eq {j : ℕ} {i : Fin h} (n : T.Ed j → ℕ) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) : T.nEnd i n ω q =
    (∑ e : T.Ed j, if T.ty e = i ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q then n e else 0) +
    ∑ e : T.Ed j, if T.ty e = i ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q then n e else 0 := by
  unfold Tower.nEnd
  have e2 : ∀ c : T.X j, (if T.πV (T.vx i c) = ω ∧ s(T.co i (T.host i (T.vx i c)), T.co i c) = q then T.be i n c else 0) =
      ∑ e : T.Ed j, ((if T.e0 e = c then (if T.ty e = i ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
        s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q then n e else 0) else 0) +
        if T.e1 e = c then (if T.ty e = i ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
        s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q then n e else 0) else 0) := by
    intro c
    unfold Tower.be
    rw [Finset.ite_sum_zero]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h0 : T.e0 e = c
    · subst c
      have h1 := (T.e_ne e).symm
      simp [h1, ← ite_and, and_comm]
    · by_cases h1 : T.e1 e = c
      · subst c
        simp [h0, ← ite_and, and_comm]
      · simp [h0, h1]
  rw [Finset.sum_congr rfl fun c _ => e2 c, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, ite_eq_left (mem_univ _), ite_eq_left (mem_univ _)]

section Mid

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

theorem num_inl (x : {x : RM T m AA // okR T R ch x}) : num R ch FL lhat n o (.inl x) ≤
    load R ch FL lhat n o (inpR T x.1) := by
  rw [num_eq, numF]
  split <;> simp

theorem num_mid0 (j : Fin J) (e : T.Ed j) (hx : okR T R ch (.mid j e 0)) :
    num R ch FL lhat n o (.inl ⟨.mid j e 0, hx⟩) ≤ load R ch FL lhat n o (.edge j.castSucc e) ∧
    (¬ IsMin (load R ch FL lhat n o) j.castSucc (T.ty e) → num R ch FL lhat n o (.inl ⟨.mid j e 0, hx⟩) = 0) := by
  classical
  refine ⟨num_inl hr hb _, fun hn => ?_⟩
  rw [num_eq, numF, ite_eq_right]
  intro ha
  exact hn (ha rfl)

omit hr hb in
/-- When a relay target has no initial units and a single possible incoming channel,
its load is bounded by the number of units given to that channel's relay. -/
theorem load_nxt_le_num {y p : RM T m AA} (hp : okR T R ch p)
    (hbt : bt R ch lhat n (.nxt y) = 0)
    (hpred : ∀ x, okR T R ch x → ∀ ν, tgR T R ch x ν = .nxt y → ν = true ∧ x = p) :
    load R ch FL lhat n o (.nxt y) ≤ num R ch FL lhat n o (.inl ⟨p, hp⟩) := by
  refine (load_le_sum {⟨.inl ⟨p, hp⟩, true⟩} hbt ?_).trans ?_
  · rintro ⟨⟨x, hx⟩ | l, ν⟩ ht -
    · obtain ⟨rfl, rfl⟩ := hpred x hx ν ht
      exact mem_singleton_self _
    · simp [tgM] at ht
  · rw [Finset.sum_singleton]
    exact alv_le_num _ _

/-- Stage three of a middle relay receives its units from stage two. -/
theorem num_mid3_le_mid2 (j : Fin J) (e : T.Ed j) (hx3 : okR T R ch (.mid j e 3))
    (hx2 : okR T R ch (.mid j e 2)) :
    num R ch FL lhat n o (.inl ⟨.mid j e 3, hx3⟩) ≤ num R ch FL lhat n o (.inl ⟨.mid j e 2, hx2⟩) := by
  refine (num_inl hr hb _).trans ?_
  apply load_nxt_le_num hx2 (bt_mid j e 3)
  intro x _ ν ht
  simpa using tgR_mid (x := x) (ν := ν) ht

/-- The relays of an edge are given at most what is on the edge. -/
theorem num_mid_le (j : Fin J) (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s)) :
    ∃ hx0 : okR T R ch (.mid j e 0), num R ch FL lhat n o (.inl ⟨.mid j e s, hx⟩) ≤
      num R ch FL lhat n o (.inl ⟨.mid j e 0, hx0⟩) := by
  have hx0 : okR T R ch (.mid j e 0) := ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
  refine ⟨hx0, ?_⟩
  have one : ∀ hx1 : okR T R ch (.mid j e 1), num R ch FL lhat n o (.inl ⟨.mid j e 1, hx1⟩) ≤
      num R ch FL lhat n o (.inl ⟨.mid j e 0, hx0⟩) := by
    intro hx1
    refine (num_inl hr hb _).trans ?_
    apply load_nxt_le_num hx0 (bt_mid j e 1)
    intro x _ ν ht
    simpa using tgR_mid (x := x) (ν := ν) ht
  have two : ∀ hx2 : okR T R ch (.mid j e 2), num R ch FL lhat n o (.inl ⟨.mid j e 2, hx2⟩) ≤
      num R ch FL lhat n o (.inl ⟨.mid j e 0, hx0⟩) := by
    intro hx2
    refine (num_inl hr hb _).trans ?_
    by_cases hh : hst T (T.ty e) (T.e0 e) = T.π (T.e0 e)
    · apply load_nxt_le_num hx0 (bt_mid j e 2)
      intro x hx' ν ht
      obtain ⟨hν, hx' | rfl⟩ : ν = true ∧ (x = .mid j e 0 ∨ x = .mid j e 1) := by
        simpa [hh] using tgR_mid (x := x) (ν := ν) ht
      · exact ⟨hν, hx'⟩
      · exact (hx'.1 rfl hh).elim
    · have hx1 : okR T R ch (.mid j e 1) := ⟨fun _ => hh, fun h3 => absurd h3 (by decide)⟩
      refine (load_nxt_le_num hx1 (bt_mid j e 2) ?_).trans (one hx1)
      intro x _ ν ht
      simpa [hh] using tgR_mid (x := x) (ν := ν) ht
  fin_cases s
  · exact le_rfl
  · exact one hx
  · exact two hx
  · have hx2 : okR T R ch (.mid j e 2) := ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
    exact (num_mid3_le_mid2 hr hb j e hx hx2).trans (two hx2)

theorem alv_mid_le (j : Fin J) (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s)) (ν : Bool) :
    alv R ch FL lhat n o (⟨.inl ⟨.mid j e s, hx⟩, ν⟩ : NM R FL (ch := ch)) ≤ load R ch FL lhat n o (.edge j.castSucc e) ∧
    (¬ IsMin (load R ch FL lhat n o) j.castSucc (T.ty e) →
      alv R ch FL lhat n o (⟨.inl ⟨.mid j e s, hx⟩, ν⟩ : NM R FL (ch := ch)) = 0) := by
  obtain ⟨hx0, h1⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
  have h2 := num_mid0 (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e hx0
  have h3 := alv_le_num (lhat := lhat) (n := n) (o := o)
    (⟨.mid j e s, hx⟩ : {x : RM T m AA // okR T R ch x}) ν
  refine ⟨h3.trans (h1.trans h2.1), fun hn => ?_⟩
  have := h2.2 hn
  omega

/-- The channels of end segments. -/
theorem seg_chan {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i} {q : Sym2 T.Fl} {ν : NM R FL (ch := ch)}
    (hν : tgM R ch FL ν.1 ν.2 = .seg j i ω q) : ∃ (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s)),
      T.ty e = i ∧ ν = ⟨.inl ⟨.mid j e s, hx⟩, false⟩ ∧
      ((s = 1 ∧ T.πV (T.vx i (T.e0 e)) = ω ∧ s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q) ∨
      (s = 3 ∧ T.πV (T.vx i (T.e1 e)) = ω ∧ s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q)) := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · obtain ⟨e, h1, h2, h3⟩ := tgR_seg (x := x) (ν := ν) hν
    have h1 : ν = false := h1
    subst h1
    rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · subst h3
      exact ⟨e, 1, hx, h2, rfl, Or.inl ⟨rfl, h4⟩⟩
    · subst h3
      exact ⟨e, 3, hx, h2, rfl, Or.inr ⟨rfl, h4⟩⟩
  · simp [tgM] at hν

/-- End segments, inactive types. -/
theorem seg_zero {j : Fin J} {i : Fin h} (hn : ¬ IsMin (load R ch FL lhat n o) j.castSucc i) (ω : T.V (j + 1) i)
    (q : Sym2 T.Fl) : load R ch FL lhat n o (.seg j i ω q) = 0 := by
  rw [load_def, bt_seg, Nat.zero_add]
  refine Finset.sum_eq_zero fun ν _ => ?_
  split_ifs with hν
  · obtain ⟨e, s, hx, h1, h2, -⟩ := seg_chan hr hb hν
    rw [h2]
    exact (alv_mid_le hr hb j e s hx false).2 (by rw [h1]; exact hn)
  · rfl

open Classical in
/-- The channel of an end segment. -/
noncomputable def segS (j : Fin J) (s : Fin 4) (e : T.Ed j) : Finset (NM R FL (ch := ch)) :=
  if hx : okR T R ch (.mid j e s) then {⟨.inl ⟨.mid j e s, hx⟩, false⟩} else ∅

theorem sum_segS (j : Fin J) (s : Fin 4) (e : T.Ed j) : ∑ ν ∈ segS (R := R) (ch := ch) (FL := FL) j s e, alv R ch FL lhat n o ν ≤
    load R ch FL lhat n o (.edge j.castSucc e) := by
  unfold segS
  split_ifs with hx
  · rw [Finset.sum_singleton]
    exact (alv_mid_le hr hb j e s hx false).1
  · rw [Finset.sum_empty]
    exact Nat.zero_le _

/-- End segments. -/
theorem seg_le (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    load R ch FL lhat n o (.seg j i ω q) ≤ T.nEnd i (fun e => load R ch FL lhat n o (.edge j.castSucc e)) ω q := by
  classical
  rw [nEnd_eq]
  refine (load_le_sum
    (((univ.filter fun e : T.Ed j => T.ty e = i ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q).biUnion (segS (R := R) (ch := ch) (FL := FL) j 1)) ∪
    ((univ.filter fun e : T.Ed j => T.ty e = i ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q).biUnion (segS (R := R) (ch := ch) (FL := FL) j 3)))
    (bt_seg j i ω q) ?_).trans ?_
  · intro ν hν _
    obtain ⟨e, s, hx, h1, h2, h3⟩ := seg_chan hr hb hν
    rcases h3 with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · subst h5
      refine mem_union_left _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, h1, h6⟩, ?_⟩)
      unfold segS
      rw [dite_eq_left hx, h2]
      exact mem_singleton_self _
    · subst h5
      refine mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, h1, h6⟩, ?_⟩)
      unfold segS
      rw [dite_eq_left hx, h2]
      exact mem_singleton_self _
  · refine (sum_union_le _ _ _).trans (add_le_add ?_ ?_)
    · refine (sum_biUnion_le' _ _ _).trans ?_
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun e _ => ?_
      split_ifs
      · exact sum_segS hr hb j 1 e
      · exact le_rfl
    · refine (sum_biUnion_le' _ _ _).trans ?_
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun e _ => ?_
      split_ifs
      · exact sum_segS hr hb j 3 e
      · exact le_rfl

end Mid

end Nc.Tow
