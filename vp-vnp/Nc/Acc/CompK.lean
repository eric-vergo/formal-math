/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Util

/-!
# Values of formulas with named constants

`KV θ κ S F x w c`: all runs of the formula `F` at `x` stop; the accepting ones have cost at most `c` and use names of
constants in `S`; with the constants `κ` the sum of their weights is `w`.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The value of a formula. -/
def KV (θ : List Bool → A) (κ : List Bool → R) (S : Set (List Bool)) (F : Fm) (x : Tree) (w : R) (c : ℕ) : Prop :=
  ∃ l, Ev θ F x l ∧ (∀ r ∈ l, r.cost ≤ c ∧ ∀ p ∈ r.bill, p ∈ S) ∧ val κ l = w

theorem wt_mul (κ : List Bool → R) {r s u : Run A} (h1 : u.th = r.th * s.th) (h2 : u.bill = r.bill ++ s.bill) :
    wt κ u = wt κ r * wt κ s := by
  rw [wt, wt, wt, h1, h2, map_mul, List.map_append, List.prod_append]
  ring

namespace KV

variable {κ : List Bool → R} {S : Set (List Bool)} {F G H : Fm} {x : Tree} {w w' : R} {c d : ℕ}

theorem mono (h : KV θ κ S F x w c) (hc : c ≤ d) : KV θ κ S F x w d := by
  obtain ⟨l, h1, h2, h3⟩ := h
  exact ⟨l, h1, fun r hr => ⟨(h2 r hr).1.trans hc, (h2 r hr).2⟩, h3⟩

theorem congr (h : KV θ κ S F x w c) (hw : w = w') : KV θ κ S F x w' c := hw ▸ h

theorem hl (h : KV θ κ S F x w c) : Hl θ F x := by
  obtain ⟨l, h1, -⟩ := h
  exact h1.hl

theorem evl (h : KV θ κ S F x w c) : (∀ r ∈ NS1.evl θ F x, r.cost ≤ c ∧ ∀ p ∈ r.bill, p ∈ S) ∧
    val κ (NS1.evl θ F x) = w := by
  obtain ⟨l, h1, h2, h3⟩ := h
  rw [h1.evl]
  exact ⟨h2, h3⟩

theorem of_does {Q : List (A × Tree)} (h : Does θ F x Q c) :
    KV θ κ S F x (algebraMap A R (Q.map Prod.fst).sum) c := by
  obtain ⟨l, h1, h2, h3⟩ := h
  refine ⟨l, h1, fun r hr => ⟨(h2 r hr).2.1, ?_⟩, ?_⟩
  · rw [(h2 r hr).1]
    simp
  · rw [val_plain fun r hr => (h2 r hr).1, pval]
    have := h3 fun _ => 1
    simp only [mul_one, wsum] at this
    rw [this]

theorem of_gives {o : Tree} (h : Gives θ F x o c) : KV θ κ S F x 1 c := (of_does h).congr (by simp)

theorem fail (x : Tree) : KV θ κ S .fail x 0 0 := ⟨[], .fail x, by simp, by simp [val]⟩

theorem mul {o : Tree} (h : Gives θ F x o c) (ho : o.path ∈ S) : KV θ κ S (.mul F) x (κ o.path) (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  have hout : ∀ r ∈ l, r.out = o := Gives.output_of_mem e2
  refine ⟨_, Ev.mul e1, ?_, ?_⟩
  · intro u hu
    rw [List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    refine ⟨by simpa using a2, fun p hp => ?_⟩
    rw [a1, List.nil_append, List.mem_singleton] at hp
    rw [hp, hout r hr]
    exact ho
  · have h1 : (l.map fun r : Run A => (⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩ : Run A)).map (wt κ) =
        l.map fun r => algebraMap A R r.th * κ o.path := by
      rw [List.map_map]
      refine List.map_congr_left fun r hr => ?_
      simp [wt, (e2 r hr).1, hout r hr]
    rw [val, h1, List.sum_map_mul_right]
    have h2 := e3 fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h3 : (l.map fun r => algebraMap A R r.th).sum = 1 := by
      have h4 := congrArg (algebraMap A R) h2
      rw [map_list_sum, List.map_map, map_one] at h4
      exact h4
    rw [h3, one_mul]

theorem cons (hF : KV θ κ S F x w c) (hG : KV θ κ S G x w' d) : KV θ κ S (.cons F G) x (w * w') (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  refine ⟨_, Ev.cons e1 f1, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    refine ⟨?_, fun p hp => ?_⟩
    · have h1 := (e2 r hr).1
      have h2 := (f2 s hs).1
      simp only [Run.tick, Run.seq]
      omega
    · simp only [Run.tick, Run.seq, List.mem_append] at hp
      exact hp.elim ((e2 r hr).2 p) ((f2 s hs).2 p)
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r : Run A, ((l'.map fun s => (r.seq s).tick (.cons r.out s.out)).map (wt κ)).sum = wt κ r * w' := by
      intro r
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun s _ => wt_mul κ rfl rfl
    simp only [h1]
    rw [List.sum_map_mul_right, ← e3]
    rfl

private theorem ite_of_gives {o : Tree} (hF : Gives θ F x o c)
    (hbranch : KV θ κ S (if o = .nil then H else G) x w d) :
    KV θ κ S (.ite F G H) x w (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hbranch
  have hout : ∀ r ∈ l, r.out = o := Gives.output_of_mem e2
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr hn => ?_) (fun r hr hn => ?_), ?_, ?_⟩
  · simpa [show o ≠ .nil from fun h => hn ((hout r hr).trans h)] using f1
  · simpa [show o = .nil from (hout r hr).symm.trans hn] using f1
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2⟩ := f2 s hs
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp only [Run.tick, Run.seq, a1, List.nil_append] at hp
      exact b2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map (wt κ)).sum = algebraMap A R r.th * w := by
      intro r hr
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      rw [Function.comp_apply, wt_mul κ (r := r) (s := s) rfl rfl, wt, (e2 r hr).1]
      simp
    rw [List.map_congr_left h1, List.sum_map_mul_right]
    have h2 := e3 fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h4 := congrArg (algebraMap A R) h2
    rw [map_list_sum, List.map_map, map_one] at h4
    have h3 : (l.map fun r => algebraMap A R r.th).sum = 1 := h4
    rw [h3, one_mul]

theorem ite_true {o : Tree} (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : KV θ κ S G x w d) :
    KV θ κ S (.ite F G H) x w (c + d + 1) :=
  ite_of_gives hF (by simpa [ho] using hG)

theorem ite_false (hF : Gives θ F x .nil c) (hH : KV θ κ S H x w d) : KV θ κ S (.ite F G H) x w (c + d + 1) :=
  ite_of_gives hF (by simpa using hH)

theorem either (hG : KV θ κ S G x w c) (hH : KV θ κ S H x w' d) :
    KV θ κ S (.ite .guess G H) x (w + w') (max c d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hG
  obtain ⟨l', f1, f2, f3⟩ := hH
  refine ⟨_, Ev.ite (L := fun r => if r.out = .nil then l' else l) (Ev.guess x) (fun r _ h => by rw [ite_eq_right h]; exact e1)
    (fun r _ h => by rw [ite_eq_left h]; exact f1), ?_, ?_⟩
  · intro u hu
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_map, Run.det, Tree.one,
      _root_.ite_true, reduceCtorEq, _root_.ite_false] at hu
    rcases hu with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · obtain ⟨a1, a2⟩ := f2 s hs
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Run.seq, Run.tick]
        omega
      · simp only [Run.seq, Run.tick, List.nil_append] at hp
        exact a2 p hp
    · obtain ⟨a1, a2⟩ := e2 s hs
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Run.seq, Run.tick]
        omega
      · simp only [Run.seq, Run.tick, List.nil_append] at hp
        exact a2 p hp
  · rw [← e3, ← f3, val, val, val, add_comm]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.sum_append, List.map_map,
      Run.det, Tree.one, _root_.ite_true, reduceCtorEq, _root_.ite_false]
    congr 1
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick]
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick]

/-- Group a weighted list by output before applying an algebra-valued function. -/
private theorem sum_by_output {ι : Type*} (L : List ι) (weight : ι → A) (out : ι → Tree)
    (ω : Tree → R) (D : Finset Tree) (hD : ∀ x ∈ L, out x ∈ D) :
    (L.map fun x => algebraMap A R (weight x) * ω (out x)).sum =
      ∑ o ∈ D, algebraMap A R (L.map fun x => weight x * if out x = o then 1 else 0).sum * ω o := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, map_add, add_mul, Finset.sum_add_distrib,
      ih fun y hy => hD y (List.mem_cons_of_mem _ hy)]
    congr 1
    rw [Finset.sum_eq_single (out x)]
    · simp
    · intro o _ ho
      simp [Ne.symm ho]
    · exact fun h => (h (hD x List.mem_cons_self)).elim

/-- A plain computation, then a value. -/
theorem app {p : Tree} {Q : List (A × Tree)} {ω : Tree → R} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, KV θ κ S (Fm.ofTree p) q.2 (ω q.2) d) :
    KV θ κ S (NS1.app p F) x (Q.map fun q => algebraMap A R q.1 * ω q.2).sum (c + d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  have hG' : ∀ s ∈ l, KV θ κ S (Fm.ofTree p) s.out (ω s.out) d := by
    intro s hs
    obtain ⟨-, -, q, hq, h⟩ := e2 s hs
    rw [← h]
    exact hG q hq
  refine ⟨_, Ev.app e1 fun s hs => (hG' s hs).hl, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, h3, -⟩ := mem_app hu
    obtain ⟨a1, a2, -⟩ := e2 s hs
    obtain ⟨b1, b2⟩ := (hG' s hs).evl.1 t ht
    refine ⟨by omega, fun p hp => ?_⟩
    rw [h2, a1, List.nil_append] at hp
    exact b2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ s ∈ l, (((NS1.evl θ (Fm.ofTree p) s.out).map fun t => ((Run.det 1 p).seq s).seq t |>.tick t.out).map
        (wt κ)).sum = algebraMap A R s.th * ω s.out := by
      intro s hs
      rw [← (hG' s hs).evl.2, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick, Run.det, (e2 s hs).1, mul_assoc]
    rw [List.map_congr_left h1]
    let D := (l.map Run.out).toFinset ∪ (Q.map Prod.snd).toFinset
    rw [sum_by_output l Run.th Run.out ω D (fun _ hr => Finset.mem_union_left _
      (List.mem_toFinset.2 (List.mem_map_of_mem hr))),
      sum_by_output Q Prod.fst Prod.snd ω D (fun _ hq => Finset.mem_union_right _
      (List.mem_toFinset.2 (List.mem_map_of_mem hq)))]
    exact Finset.sum_congr rfl fun o _ => by rw [e3 fun t => if t = o then 1 else 0]; rfl

theorem lett {Q : List (A × Tree)} {ω : Tree → R} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, KV θ κ S G q.2 (ω q.2) d) :
    KV θ κ S (NS1.lett F G) x (Q.map fun q => algebraMap A R q.1 * ω q.2).sum (c + d + 2) :=
  app (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

theorem app_gives {p o : Tree} (hF : Gives θ F x o c) (hG : KV θ κ S (Fm.ofTree p) o w d) :
    KV θ κ S (NS1.app p F) x w (c + d + 2) :=
  (app (Q := [(1, o)]) (ω := fun _ => w) hF (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hG)).congr (by simp)

/-- Apply a program that is the value of a formula. -/
theorem run {p y : Tree} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d)
    (h : KV θ κ S (Fm.ofTree p) y w e) : KV θ κ S (.run F G) x w (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have ho : ∀ r ∈ l, r.out = p := Gives.output_of_mem e2
  have ho' : ∀ r ∈ l', r.out = y := Gives.output_of_mem f2
  have one : ∀ {L : List (Run A)} {o : Tree}, (∀ φ : Tree → A, (L.map fun r => r.th * φ r.out).sum = wsum [(1, o)] φ) →
      (L.map fun r => algebraMap A R r.th).sum = 1 := by
    intro L o hL
    have h2 := hL fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h4 := congrArg (algebraMap A R) h2
    rw [map_list_sum, List.map_map, map_one] at h4
    exact h4
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [ho r hr, ho' s hs]; exact h.hl, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    rw [ho r hr, ho' s hs] at ht
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, -⟩ := f2 s hs
    obtain ⟨c1, c2⟩ := h.evl.1 t ht
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp only [Run.seq, Run.tick, a1, b1, List.nil_append] at hp
      exact c2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out).map (wt κ)).sum = algebraMap A R r.th * w := by
      intro r hr
      rw [sum_flatMap_map]
      have h2 : ∀ s ∈ l', (((NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
          ((r.seq s).seq t).tick t.out).map (wt κ)).sum = algebraMap A R s.th * (algebraMap A R r.th * w) := by
        intro s hs
        rw [ho r hr, ho' s hs, List.map_map, ← h.evl.2, val, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun t _ => ?_
        simp only [Function.comp_apply, wt, Run.seq, Run.tick, (e2 r hr).1, (f2 s hs).1, List.nil_append, map_mul]
        ring
      rw [List.map_congr_left h2, List.sum_map_mul_right, one f3, one_mul]
    rw [List.map_congr_left h1, List.sum_map_mul_right, one e3, one_mul]

/-- The universal program on a plain instance uses no named constants and returns its plain sum. -/
theorem uf {z : Tree} {T : ℕ} (pl : Plain θ T z) :
    KV θ κ S UF z (algebraMap A R (pv θ z)) (T + 5) := by
  refine ⟨_, UF_ev pl.1.ev, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hb, hc⟩ := pl.2 s hs
    exact ⟨by simp only [Run.delay]; omega, by simp [Run.delay, hb]⟩
  · rw [pv, val_plain]
    · simp [pval, Function.comp_def, Run.delay]
    · intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      exact (pl.2 s hs).1

end KV

/-- Runs that give values with weights, then a formula at the values. -/
theorem KV.app_rel {R : Type} [CommRing R] [Algebra A R] {κ : List Bool → R} {S : Set (List Bool)} {β : Type*}
    {P : Tree} {e : Fm} {x : Tree} {le : List (Run A)} {Q : List β} {c : β → R} {o : β → Tree} {w : β → R}
    {ce d : ℕ} (he : Ev θ e x le)
    (rel : List.Forall₂ (fun r q => wt κ r = c q ∧ r.out = o q ∧ (∀ p ∈ r.bill, p ∈ S) ∧ r.cost ≤ ce) le Q)
    (hF : ∀ q ∈ Q, KV θ κ S (Fm.ofTree P) (o q) (w q) d) :
    KV θ κ S (NS1.app P e) x (Q.map fun q => c q * w q).sum (ce + d + 2) := by
  have eU := Ev.app (p := P) he fun s hs => by
    obtain ⟨q, hq, -, h, -⟩ := forall₂_exists rel hs
    rw [h]
    exact (hF q hq).hl
  refine ⟨_, eU, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, -, -⟩ := mem_app hu
    obtain ⟨q, hq, -, h4, h5, h6⟩ := forall₂_exists rel hs
    rw [h4] at ht
    obtain ⟨c1, c2⟩ := (hF q hq).evl.1 t ht
    refine ⟨by omega, fun p hp => ?_⟩
    rw [h2, List.mem_append] at hp
    exact hp.elim (h5 p) (c2 p)
  · rw [val_eq_sumF, sumF_app, sum_rel (c := c) (o := o) (rel.imp fun r q hr => ⟨hr.1, hr.2.1⟩)]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    rw [← val_eq_sumF, (hF q hq).evl.2]

end NS1
