/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Fan
import Paper.Toolkit
import Nc.Cat.Core

/-!
# The paper, section "Prices are nonpositively curved"

The subsection "Means" is in Paper/Means.lean, Theorem thm:cn and its proof are in Paper/Fan.lean, the definition of CAT(0)
spaces and Lemma lem:toolkit in Paper/Toolkit.lean; this file has Proposition prop:space.
-/

namespace Paper

open Finset Filter Topology Nc.Price

variable {K : Type} [Field K]

section Space

open Cat Cat.Term

variable {V : Type} {w : V → V → ℝ}

/-- One step of the proof of Proposition prop:space: "let V_{l+1} be V_l with a new point for each pair of its points; define
prices by placing each new point at either end with probability ½ (Proposition prop:random)." The points are named by terms;
V_n consists of the terms of depth at most n. -/
theorem prop_space_step {d : Term V → Term V → ℝ} (hd : IsPrice K d) (n : ℕ) :
    ∃ d' : Term V → Term V → ℝ, IsPrice K d' ∧
      (∀ s t, s.depth ≤ n → t.depth ≤ n → d' s t = d s t) ∧
      ∀ s t, max s.depth t.depth = n →
        d' s (Term.mid s t) ≤ d s t / 2 ∧ d' t (Term.mid s t) ≤ d s t / 2 := by
  obtain ⟨w', h1, h2, h3⟩ := prop_random_finite hd (Q := Term V × Term V) (Λ := Fin 2) (fun _ => 1 / 2)
    (fun _ => by norm_num) (by simp) (fun l κ => if l = 0 then κ.1 else κ.2)
  refine ⟨fun s t => w' (Term.place n s) (Term.place n t), h1.comp _, ?_, ?_⟩
  · intro s t hs ht
    simp only [Term.place, ite_eq_left hs, ite_eq_left ht]
    exact h2 s t
  · intro s t hst
    have hs : s.depth ≤ n := hst ▸ le_max_left _ _
    have ht : t.depth ≤ n := hst ▸ le_max_right _ _
    have hm : ¬ (Term.mid s t).depth ≤ n := by
      simp only [depth, hst]
      omega
    simp only [Term.place, ite_eq_left hs, ite_eq_left ht, ite_eq_right hm]
    have g1 := h3 (Sum.inl s) (Sum.inr (s, t))
    have g2 := h3 (Sum.inl t) (Sum.inr (s, t))
    simp only [Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr, id, ite_true, Fin.isValue, one_ne_zero, ite_false] at g1 g2
    rw [hd.self] at g1 g2
    rw [hd.symm t s] at g2
    constructor <;> linarith

/-- "Each step extends the one before, so together they form a price; in it each new point is a midpoint of its pair". -/
theorem prop_space_midpoints (hw : IsPrice K w) : ∃ d : Term V → Term V → ℝ, IsPrice K d ∧
    (∀ a b, d (of a) (of b) = w a b) ∧
    ∀ s t, d s (Term.mid s t) ≤ d s t / 2 ∧ d t (Term.mid s t) ≤ d s t / 2 := by
  choose! f hf1 hf2 hf3 using fun (n : ℕ) (d : Term V → Term V → ℝ) (hd : IsPrice K d) => prop_space_step hd n
  let D : ℕ → Term V → Term V → ℝ := fun n => Nat.rec (fun s t => w s.base t.base) (fun n d => f n d) n
  have hDs : ∀ n, D (n + 1) = f n (D n) := fun _ => rfl
  have hP : ∀ n, IsPrice K (D n) := by
    intro n
    induction n with
    | zero => exact hw.comp _
    | succ n ih => rw [hDs]; exact hf1 n _ ih
  have hst : ∀ n k s t, s.depth ≤ n → t.depth ≤ n → D (n + k) s t = D n s t := by
    intro n k s t hs ht
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← add_assoc, hDs, hf2 _ _ (hP _) s t (by omega) (by omega), ih]
  refine ⟨fun s t => D (max s.depth t.depth) s t, ?_, ?_, ?_⟩
  · refine isPrice_of_tendsto (l := atTop) (d := D) (fun s t => ?_) (Eventually.of_forall hP)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (max s.depth t.depth)] with n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (hst _ k s t (le_max_left _ _) (le_max_right _ _)).symm
  · intro a b
    rfl
  · intro s t
    have h := hf3 (max s.depth t.depth) (D (max s.depth t.depth)) (hP _) s t rfl
    have e1 : max s.depth (Term.mid s t).depth = max s.depth t.depth + 1 := by
      simp only [depth]
      omega
    have e2 : max t.depth (Term.mid s t).depth = max s.depth t.depth + 1 := by
      simp only [depth]
      omega
    simp only [e1, e2, hDs]
    exact h

/-- "Midpoints of Cauchy sequences are Cauchy by (CN) itself": if a n → x and b n → v, and m n satisfies (CN) for a n and b n,
then (m n) is a Cauchy sequence. -/
theorem prop_space_cauchy {X : Type*} [MetricSpace X] {a b m : ℕ → X} {x v : X} (ha : Tendsto a atTop (𝓝 x))
    (hb : Tendsto b atTop (𝓝 v))
    (hm : ∀ n z, dist z (m n) ^ 2 ≤ (dist z (a n) ^ 2 + dist z (b n) ^ 2) / 2 - dist (a n) (b n) ^ 2 / 4) :
    CauchySeq m := by
  have midpt (n : ℕ) : IsPt (a n) (b n) (1 / 2) (m n) := fun z => by linarith [hm n z]
  -- Bound the midpoint discrepancy by the two endpoint errors and the two chord lengths.
  let bound (p : ℕ × ℕ) :=
    ((dist (a p.1) (b p.1) / 2 + dist (a p.1) (a p.2)) ^ 2 +
      (dist (a p.1) (b p.1) / 2 + dist (b p.1) (b p.2)) ^ 2) / 2 - dist (a p.2) (b p.2) ^ 2 / 4
  have upper (i j : ℕ) : dist (m i) (m j) ^ 2 ≤ bound (i, j) := by
    refine (hm j (m i)).trans ?_
    apply sub_le_sub_right
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply add_le_add <;> apply pow_le_pow_left₀ dist_nonneg
    · have h := (midpt i).dist_left (by norm_num) (by norm_num)
      linarith [dist_triangle (a j) (a i) (m i), dist_comm (a j) (a i), dist_comm (a j) (m i)]
    · have h := (midpt i).dist_right (by norm_num) (by norm_num)
      linarith [dist_triangle (m i) (b i) (b j)]
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by rw [← prod_atTop_atTop_eq]; exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by rw [← prod_atTop_atTop_eq]; exact tendsto_snd
  have limit : Tendsto bound atTop (𝓝 0) := by
    have ha₁ := ha.comp hfst
    have ha₂ := ha.comp hsnd
    have hb₁ := hb.comp hfst
    have hb₂ := hb.comp hsnd
    have h := (((((ha₁.dist hb₁).div_const 2).add (ha₁.dist ha₂)).pow 2).add
      ((((ha₁.dist hb₁).div_const 2).add (hb₁.dist hb₂)).pow 2)).div_const 2
    convert h.sub (((ha₂.dist hb₂).pow 2).div_const 4) using 1
    all_goals simp [bound]
    ring
  apply cauchySeq_iff_tendsto_dist_atTop_0.2
  refine squeeze_zero (fun _ => dist_nonneg) (fun p => Real.le_sqrt_of_sq_le (upper p.1 p.2)) ?_
  simpa using limit.sqrt

/-- "The completion satisfies (CN)": a complete metric space is CAT(0) if any two points x, v of a dense subset S have a
point m for which (CN) holds at all z in S. -/
theorem prop_space_completion {X : Type*} [MetricSpace X] [CompleteSpace X] {S : Set X} (hS : Dense S)
    (h : ∀ x ∈ S, ∀ v ∈ S, ∃ m, ∀ z ∈ S,
      dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4) : CN X := by
  have h' : ∀ x ∈ S, ∀ v ∈ S, ∃ m, ∀ z,
      dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4 := by
    intro x hx v hv
    obtain ⟨m, hm⟩ := h x hx v hv
    refine ⟨m, fun z => ?_⟩
    have hc : IsClosed {z | dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have h3 : S ⊆ {z | dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4} := hm
    exact hc.closure_subset_iff.2 h3 (hS z)
  refine ⟨fun x v => ?_⟩
  obtain ⟨a, haS, ha⟩ := mem_closure_iff_seq_limit.1 (hS x)
  obtain ⟨b, hbS, hb⟩ := mem_closure_iff_seq_limit.1 (hS v)
  choose m hm using fun n => h' (a n) (haS n) (b n) (hbS n)
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete (prop_space_cauchy ha hb hm)
  refine ⟨p, fun z => ?_⟩
  have hl : Tendsto (fun n => dist z (m n) ^ 2) atTop (𝓝 (dist z p ^ 2)) :=
    (tendsto_const_nhds.dist hp).pow 2
  have hr : Tendsto (fun n => (dist z (a n) ^ 2 + dist z (b n) ^ 2) / 2 - dist (a n) (b n) ^ 2 / 4)
      atTop (𝓝 ((dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4)) :=
    ((((tendsto_const_nhds.dist ha).pow 2).add ((tendsto_const_nhds.dist hb).pow 2)).div_const 2).sub
      (((ha.dist hb).pow 2).div_const 4)
  exact le_of_tendsto_of_tendsto' hl hr fun n => hm n z

/-- "Its metric is a price as a limit": if the distance of a pseudometric space is a price, so is the metric of its
completion. -/
theorem prop_space_limit {T : Type} [PseudoMetricSpace T] (hd : IsPrice K fun s t : T => dist s t) :
    IsPrice K fun a b : UniformSpace.Completion T => dist a b := by
  have hseq : ∀ a : UniformSpace.Completion T, ∃ u : ℕ → T,
      Tendsto (fun n => ((u n : T) : UniformSpace.Completion T)) atTop (𝓝 a) := by
    intro a
    obtain ⟨u, hu, ha⟩ := mem_closure_iff_seq_limit.1 (UniformSpace.Completion.denseRange_coe (α := T) a)
    choose u' hu' using hu
    exact ⟨u', by simpa only [hu'] using ha⟩
  choose u hu using hseq
  refine isPrice_of_tendsto (l := atTop) (d := fun n a b => dist (u a n) (u b n)) ?_
    (Eventually.of_forall fun n => hd.comp fun a => u a n)
  intro a b
  have h := (hu a).dist (hu b)
  simpa only [UniformSpace.Completion.dist_eq] using h

/-- **Paper: Proposition prop:space.** "Every price on a set V is the pull-back of the metric of a price space." A price
space is a complete CAT(0) space whose metric is a price. -/
theorem prop_space {V : Type} {w : V → V → ℝ} (hw : IsPrice K w) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : Cat.CN X) (f : V → X),
      IsPrice K (fun a b : X => dist a b) ∧ ∀ a b, dist (f a) (f b) = w a b := by
  obtain ⟨d, hd, hof, hmid⟩ := prop_space_midpoints hw
  let _ : PseudoMetricSpace (Term V) :=
    { dist := d
      dist_self := hd.self
      dist_comm := hd.symm
      dist_triangle := hd.triangle }
  have hdd : ∀ s t : Term V, dist s t = d s t := fun _ _ => rfl
  -- "identify points at distance 0. The completion satisfies (CN), its metric is a price as a limit"
  refine ⟨UniformSpace.Completion (Term V), inferInstance,
    prop_space_completion UniformSpace.Completion.denseRange_coe ?_,
    fun v => ((of v : Term V) : UniformSpace.Completion (Term V)), prop_space_limit hd, ?_⟩
  · -- "each new point is a midpoint of its pair, so (CN) holds", by Theorem thm:cn
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    refine ⟨((Term.mid s t : Term V) : UniformSpace.Completion (Term V)), ?_⟩
    rintro _ ⟨z, rfl⟩
    simp only [UniformSpace.Completion.dist_eq, hdd]
    have h := thm_cn hd s t (Term.mid s t) z (D := d s t / 2) (hmid s t).1 (hmid s t).2 (by ring)
    refine h.trans (le_of_eq ?_)
    ring
  · intro a b
    simp only [UniformSpace.Completion.dist_eq, hdd]
    exact hof a b

end Space

end Paper
