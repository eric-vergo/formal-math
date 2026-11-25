/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Guess

/-!
# The parts of a round

Weights of runs, a program applied to the outputs of another (`app`), the loop `LP` that applies a
program to every piece of a list, and the plain instance `zq` formed from a guessed budget (`ZE`).
The round of the approximate scale-up, `stepA`, is assembled from them.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R] {κ : List Bool → R}

section Values

theorem wt_seq (r s : Run A) : wt κ (r.seq s) = wt κ r * wt κ s := by
  simp only [wt, Run.seq, map_mul, List.map_append, List.prod_append]
  ring

theorem wt_tick (r : Run A) (o : Tree) : wt κ (r.tick o) = wt κ r := rfl

theorem wt_delay (k : ℕ) (r : Run A) : wt κ (r.delay k) = wt κ r := rfl

theorem wt_det (k : ℕ) (o : Tree) : wt κ (Run.det k o : Run A) = 1 := by simp [wt, Run.det]

/-- Sums over runs, with a function of the value. -/
def sumF (κ : List Bool → R) (l : List (Run A)) (f : Tree → R) : R := (l.map fun r => wt κ r * f r.out).sum

theorem val_eq_sumF (l : List (Run A)) : val κ l = sumF κ l fun _ => 1 := by simp [val, sumF]

theorem sumF_delay (k : ℕ) (l : List (Run A)) (f : Tree → R) : sumF κ (l.map (Run.delay k)) f = sumF κ l f := by
  simp only [sumF, List.map_map]
  rfl

theorem sum_rel {β : Type*} {l : List (Run A)} {Q : List β} {c : β → R} {o : β → Tree} {f : Tree → R}
    (h : List.Forall₂ (fun r q => wt κ r = c q ∧ r.out = o q) l Q) :
    sumF κ l f = (Q.map fun q => c q * f (o q)).sum := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [sumF, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, h.1, h.2]

end Values

section App

/-- Apply a fixed program. -/
def app (p : Tree) (e : Fm) : Fm := .run (.quote p) e

theorem size_app (p : Tree) (e : Fm) : (app p e).code.size = p.size + e.code.size + 17 := by
  rw [app, size_run, size_quote]; ring

theorem Ev.app {p x : Tree} {e : Fm} {le : List (Run A)} (he : Ev θ e x le)
    (h : ∀ s ∈ le, Hl θ (Fm.ofTree p) s.out) : Ev θ (app p e) x
      (le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t => ((Run.det 1 p).seq s).seq t |>.tick t.out) := by
  have := Ev.run' (Dt.quote (θ := θ) p x) he (fun r hr s hs => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact h s hs)
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  exact this

/-- The value of a dynamic program call is the weighted sum over its programs and arguments. -/
theorem sumF_run {lp lx : List (Run A)} {f : Tree → R} :
    sumF κ (lp.flatMap fun r => lx.flatMap fun s => (evl θ (Fm.ofTree r.out) s.out).map
      fun t => ((r.seq s).seq t).tick t.out) f =
      sumF κ lp fun p => sumF κ lx fun x => sumF κ (evl θ (Fm.ofTree p) x) f := by
  simp only [sumF, sum_flatMap_map, List.map_map, Function.comp_def, wt_tick, wt_seq,
    ← List.sum_map_mul_left, mul_assoc]
  rfl

theorem sumF_app {p : Tree} {le : List (Run A)} {f : Tree → R} :
    sumF κ (le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t =>
      ((Run.det 1 p).seq s).seq t |>.tick t.out) f = sumF κ le fun o => sumF κ (NS1.evl θ (Fm.ofTree p) o) f := by
  simpa [sumF, Run.det, List.flatMap_cons, List.flatMap_nil, wt] using
    (sumF_run (κ := κ) (θ := θ) (lp := [Run.det 1 p]) (lx := le) (f := f))

theorem mem_app {p : Tree} {le : List (Run A)} {u : Run A}
    (h : u ∈ le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t =>
      ((Run.det 1 p).seq s).seq t |>.tick t.out) :
    ∃ s ∈ le, ∃ t ∈ NS1.evl θ (Fm.ofTree p) s.out, u.cost = s.cost + t.cost + 2 ∧ u.bill = s.bill ++ t.bill ∧
      u.out = t.out ∧ u.th = s.th * t.th := by
  rw [List.mem_flatMap] at h
  obtain ⟨s, hs, h⟩ := h
  rw [List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  refine ⟨s, hs, t, ht, ?_, ?_, rfl, ?_⟩
  · simp only [Run.seq, Run.tick, Run.det]
    omega
  · simp [Run.seq, Run.tick, Run.det]
  · simp [Run.seq, Run.tick, Run.det]

end App

section Loop

/-- Apply the program `D` to all trees of a list. The argument is (this program, the list). -/
def LP (D : Tree) : Fm := .ite (.tl .id)
  (.cons (.run (.quote D) (.hd (.tl .id))) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) (.quote .nil)

theorem LP_ev {D : Tree} {T : ℕ} {P : List Bool → Prop} (ys : Tree) (h : ∀ y ∈ ys.toList, Hl θ (Fm.ofTree D) y ∧
    ∀ r ∈ evl θ (Fm.ofTree D) y, r.cost ≤ T ∧ ∀ p ∈ r.bill, P p) :
    ∃ l, Ev θ (LP D) (.cons (LP D).code ys) l ∧
      (∀ r ∈ l, r.cost ≤ (T + 30) * ys.toList.length + 10 ∧ ∀ p ∈ r.bill, P p) ∧
      val κ l = (ys.toList.map fun y => val κ (evl θ (Fm.ofTree D) y)).prod := by
  induction ys with
  | nil =>
    refine ⟨_, Dt.ite_false (.tl (.id _)) (.quote _ _), ?_, ?_⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      simp [Run.det]
    · simp [val, wt_det, toList]
  | cons a ys _ ih =>
    obtain ⟨lr, er, hr, vr⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    obtain ⟨ha, ha'⟩ := h a List.mem_cons_self
    have e1 := Ev.run_det (Dt.quote (θ := θ) D (.cons (LP D).code (.cons a ys))) (.hd (.tl (.id _))) ha.ev
    have er' : Ev θ (Fm.ofTree (LP D).code) (.cons (LP D).code ys) lr := by rwa [Fm.ofTree_code]
    have e2 := Ev.run_det (Dt.hd (Dt.id (θ := θ) (.cons (LP D).code (.cons a ys)))) (.cons (.hd (.id _))
      (.tl (.tl (.id _)))) er'
    refine ⟨_, Ev.ite_true (.tl (.id _)) (by simp) (Ev.cons e1 e2), ?_, ?_⟩
    · intro r hr0
      simp only [List.mem_map, List.mem_flatMap] at hr0
      obtain ⟨_, ⟨_, ⟨r1, hr1, rfl⟩, ⟨_, ⟨r2, hr2, rfl⟩, rfl⟩⟩, rfl⟩ := hr0
      obtain ⟨c1, p1⟩ := ha' r1 hr1
      obtain ⟨c2, p2⟩ := hr r2 hr2
      refine ⟨?_, ?_⟩
      · simp only [Run.delay, Run.seq, Run.tick, toList, List.length_cons]
        nlinarith
      · intro p hp
        simp only [Run.delay, Run.seq, Run.tick, List.mem_append] at hp
        rcases hp with hp | hp
        · exact p1 p hp
        · exact p2 p hp
    · rw [val_eq_sumF, sumF_delay, toList, List.map_cons, List.prod_cons, ← vr]
      simp only [sumF, mul_one]
      rw [sum_flatMap_map, List.map_map]
      simp only [List.map_map, Function.comp_def, wt_tick, wt_seq, wt_delay]
      simp only [List.sum_map_mul_left]
      rw [List.sum_map_mul_right]
      rfl

end Loop

section Inst

/-- The plain instance for a program `p`, an argument `z` and budgets `t`. -/
def zq (p z : Tree) (t : Bt) : Tree := .cons WF.code (.cons p (.cons z t.enc))

/-- Form the plain instance: `fp` gives the program, `g` guesses the budgets. -/
def ZE (fp g : Fm) : Fm := .cons (.quote WF.code) (.cons fp (.cons .id g))

theorem ZE_ev {fp g : Fm} {p z : Tree} {k cg : ℕ} {P : List Bool → Prop} {lg : List (Run A)} {Q : List (Bt × R)}
    (hp : Dt θ fp z p k) (hg : Ev θ g z lg) (rg : List.Forall₂ (RelG κ P cg) lg Q) :
    ∃ l, Ev θ (ZE fp g) z l ∧ List.Forall₂ (fun r q => wt κ r = q.2 ∧ r.out = zq p z q.1 ∧ (∀ n ∈ r.bill, P n) ∧
      r.cost ≤ cg + k + 5) l Q := by
  refine ⟨_, Ev.cons (Dt.quote _ _) (Ev.cons hp (Ev.cons (Dt.id _) hg)), ?_⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff]
  refine rg.imp fun r q hr => ⟨?_, ?_, ?_, ?_⟩
  · rw [wt_tick, wt_seq, wt_tick, wt_seq, wt_tick, wt_seq, wt_det, wt_det, wt_det]
    simp [wt, hr.th, hr.bill]
  · simp [Run.tick, Run.det, hr.out, zq]
  · simpa [Run.seq, Run.tick, Run.det] using hr.names
  · have := hr.cost
    simp only [Run.seq, Run.tick, Run.det]
    omega

end Inst

end NS1
