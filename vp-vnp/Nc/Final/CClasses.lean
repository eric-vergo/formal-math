/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.LowDegree

/-!
# The classes VP and VNP

Valiant's classes over a commutative semiring: families of polynomials with polynomially many variables,
polynomial degree and circuits of polynomial size; and sums of such polynomials over all values 0, 1 of some of
the variables.
-/

namespace Nc

open Finset

section Definitions

/-- A family of polynomials, with finitely many variables for every n. -/
structure Family (F : Type*) [CommSemiring F] where
  /-- the variables -/
  X : ℕ → Type
  /-- finitely many -/
  [fin : ∀ n, Fintype (X n)]
  /-- the polynomials -/
  poly : ∀ n, MvPolynomial (X n) F

attribute [instance] Family.fin

variable (F : Type*) [CommSemiring F]

/-- VP: the families with polynomially many variables, polynomial degree and circuits of polynomial size. -/
def VP : Set (Family F) :=
  {p | ∃ C : ℕ, ∀ n, Fintype.card (p.X n) ≤ n ^ C + C ∧ (p.poly n).totalDegree ≤ n ^ C + C ∧
    Computes (p.poly n) (n ^ C + C)}

variable {F} in
/-- Substitute the bits e for the variables of the second kind. -/
noncomputable def bits {X : Type*} {m : ℕ} (q : MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    MvPolynomial X F :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X fun i => if e i then 1 else 0) q

/-- VNP: the families p n (x) = ∑ q n (x, e), the sum over all e in {0, 1} ^ m n, for a family q in VP (so m is
polynomially bounded). -/
def VNP : Set (Family F) :=
  {p | ∃ (m : ℕ → ℕ) (q : ∀ n, MvPolynomial (p.X n ⊕ Fin (m n)) F),
    ({ X := fun n => p.X n ⊕ Fin (m n), poly := q } : Family F) ∈ VP F ∧
      ∀ n, p.poly n = ∑ e : Fin (m n) → Bool, bits (q n) e}

end Definitions

section Size

variable {F : Type*} [CommSemiring F] {X Y : Type*}

/-- Relabel a gate and its predecessors inside a larger gate list. -/
theorem IsStep.reindex {l L : ℕ → MvPolynomial X F} {k : ℕ}
    (h : IsStep l k) (f : ℕ → ℕ) (hf : StrictMono f) (he : ∀ i ≤ k, L (f i) = l i) : IsStep L (f k) := by
  unfold IsStep
  rw [he k le_rfl]
  rcases h with e | e | ⟨i, hi, j, hj, e⟩ | ⟨i, hi, j, hj, e⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl ⟨f i, hf hi, f j, hf hj, by rw [he i hi.le, he j hj.le, e]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨f i, hf hi, f j, hf hj, by rw [he i hi.le, he j hj.le, e]⟩))

theorem Computes.mono {p : MvPolynomial X F} {s t : ℕ} (h : Computes p s) (hst : s ≤ t) : Computes p t := by
  obtain ⟨l, hl, a, ha, rfl⟩ := h
  refine ⟨fun k => if k < s then l k else MvPolynomial.C 0, fun k hk => ?_, a, by omega, if_pos ha⟩
  by_cases h : k < s
  · exact (hl k h).reindex id strictMono_id fun i hi => if_pos (hi.trans_lt h)
  · exact Or.inr (Or.inl ⟨0, by simp only [h, if_false]⟩)

/-- Apply a ring map that sends input gates to inputs and constant gates to constants. -/
private theorem Computes.map_gates {K : Type*} [CommSemiring K] {p : MvPolynomial X F} {s : ℕ}
    (h : Computes p s) (φ : MvPolynomial X F →+* MvPolynomial Y K)
    (hX : ∀ i, ∃ j, φ (MvPolynomial.X i) = MvPolynomial.X j)
    (hC : ∀ c, ∃ b, φ (MvPolynomial.C c) = MvPolynomial.C b) : Computes (φ p) s := by
  obtain ⟨l, hl, a, ha, rfl⟩ := h
  refine ⟨φ ∘ l, fun k hk => ?_, a, ha, rfl⟩
  rcases hl k hk with ⟨i, e⟩ | ⟨c, e⟩ | ⟨i, hi, j, hj, e⟩ | ⟨i, hi, j, hj, e⟩
  · exact Or.inl (by simpa only [Function.comp_apply, e] using hX i)
  · exact Or.inr (Or.inl (by simpa only [Function.comp_apply, e] using hC c))
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by simp [Function.comp_apply, e]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by simp [Function.comp_apply, e]⟩))

/-- Circuits over a larger ring. -/
theorem Computes.map {K : Type*} [CommSemiring K] (φ : F →+* K) {p : MvPolynomial X F} {s : ℕ}
    (h : Computes p s) : Computes (MvPolynomial.map φ p) s :=
  h.map_gates (MvPolynomial.map φ) (fun i => ⟨i, by simp⟩) (fun c => ⟨φ c, by simp⟩)

/-- Circuits with renamed variables. -/
theorem Computes.rename (f : X → Y) {p : MvPolynomial X F} {s : ℕ} (h : Computes p s) :
    Computes (MvPolynomial.rename f p) s :=
  h.map_gates (MvPolynomial.rename f).toRingHom (fun i => ⟨f i, by simp⟩) (fun c => ⟨c, by simp⟩)

/-- Two circuits side by side, and one more gate. -/
theorem Computes.join {p q r : MvPolynomial X F} {s t : ℕ} (hp : Computes p s) (hq : Computes q t)
    (hr : r = p + q ∨ r = p * q) : Computes r (s + t + 1) := by
  obtain ⟨l, hl, a, ha, rfl⟩ := hp
  obtain ⟨l', hl', b, hb, rfl⟩ := hq
  let L : ℕ → MvPolynomial X F := fun k => if k < s then l k else if k < s + t then l' (k - s) else r
  have L1 : ∀ k < s, L k = l k := fun k hk => if_pos hk
  have L2 : ∀ k < t, L (s + k) = l' k := fun k hk => by
    simp only [L]
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  have L3 : L (s + t) = r := by
    simp only [L]
    rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨L, fun k hk => ?_, s + t, by omega, L3⟩
  rcases lt_or_ge k s with h | h
  · exact (hl k h).reindex id strictMono_id fun i hi => L1 i (hi.trans_lt h)
  · rcases lt_or_ge k (s + t) with h' | h'
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
      have hk' : k < t := by omega
      exact (hl' k hk').reindex (s + ·) (fun _ _ hi => Nat.add_lt_add_left hi s) fun i hi => L2 i (hi.trans_lt hk')
    · obtain rfl : k = s + t := by omega
      unfold IsStep
      rw [L3]
      rcases hr with hr | hr
      · exact Or.inr (Or.inr (Or.inl ⟨a, by omega, s + b, by omega, by rw [L1 a ha, L2 b hb, hr]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨a, by omega, s + b, by omega, by rw [L1 a ha, L2 b hb, hr]⟩))

/-- The polynomial has circuits with s gates and degree at most d. -/
def CSize (p : MvPolynomial X F) (s d : ℕ) : Prop := Computes p s ∧ p.totalDegree ≤ d

namespace CSize

theorem mono {p : MvPolynomial X F} {s d s' d' : ℕ} (h : CSize p s d) (hs : s ≤ s') (hd : d ≤ d') :
    CSize p s' d' := ⟨h.1.mono hs, h.2.trans hd⟩

theorem var (x : X) : CSize (MvPolynomial.X x : MvPolynomial X F) 1 1 := by
  refine ⟨⟨fun _ => MvPolynomial.X x, fun _ _ => Or.inl ⟨x, rfl⟩, 0, by omega, rfl⟩, ?_⟩
  refine (MvPolynomial.totalDegree_monomial_le (R := F) (Finsupp.single x 1) 1).trans ?_
  rw [Finsupp.sum_single_index rfl]
  exact le_rfl

theorem const (a : F) : CSize (MvPolynomial.C a : MvPolynomial X F) 1 0 := by
  refine ⟨⟨fun _ => MvPolynomial.C a, fun _ _ => Or.inr (Or.inl ⟨a, rfl⟩), 0, by omega, rfl⟩, ?_⟩
  rw [MvPolynomial.totalDegree_C]

theorem add {p q : MvPolynomial X F} {s d t : ℕ} (hp : CSize p s d) (hq : CSize q t d) :
    CSize (p + q) (s + t + 1) d :=
  ⟨hp.1.join hq.1 (Or.inl rfl), (MvPolynomial.totalDegree_add p q).trans (max_le hp.2 hq.2)⟩

theorem mul {p q : MvPolynomial X F} {s d t e : ℕ} (hp : CSize p s d) (hq : CSize q t e) :
    CSize (p * q) (s + t + 1) (d + e) :=
  ⟨hp.1.join hq.1 (Or.inr rfl), (MvPolynomial.totalDegree_mul p q).trans (add_le_add hp.2 hq.2)⟩

theorem sum {ι : Type*} (A : Finset ι) {f : ι → MvPolynomial X F} {s d : ℕ} (h : ∀ i ∈ A, CSize (f i) s d) :
    CSize (∑ i ∈ A, f i) (A.card * (s + 1) + 1) d := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have := (const (X := X) (0 : F)).mono (s' := 1) (d' := d) le_rfl (Nat.zero_le _)
    rw [map_zero] at this
    simpa using this
  | insert i A hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    refine ((h i (Finset.mem_insert_self i A)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).mono ?_ le_rfl
    ring_nf
    omega

theorem prod {ι : Type*} (A : Finset ι) {f : ι → MvPolynomial X F} {s d : ℕ} (h : ∀ i ∈ A, CSize (f i) s d) :
    CSize (∏ i ∈ A, f i) (A.card * (s + 1) + 1) (A.card * d) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have := const (X := X) (1 : F)
    rw [map_one] at this
    simpa using this
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    refine ((h i (Finset.mem_insert_self i A)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).mono ?_ ?_
    · ring_nf
      omega
    · ring_nf
      omega

end CSize

end Size

section Subset

variable {F : Type*} [CommSemiring F] {X : Type*}

theorem bits_rename {m : ℕ} (p : MvPolynomial X F) (e : Fin m → Bool) :
    bits (MvPolynomial.rename (Sum.inl : X → X ⊕ Fin m) p) e = p := by
  rw [bits, MvPolynomial.aeval_rename]
  exact MvPolynomial.aeval_X_left_apply p

theorem bits_add {m : ℕ} (p q : MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (p + q) e = bits p e + bits q e := map_add _ _ _

theorem bits_mul {m : ℕ} (p q : MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (p * q) e = bits p e * bits q e := map_mul _ _ _

theorem bits_sum {m : ℕ} {ι : Type*} (A : Finset ι) (f : ι → MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (∑ i ∈ A, f i) e = ∑ i ∈ A, bits (f i) e := map_sum _ _ _

theorem bits_prod {m : ℕ} {ι : Type*} (A : Finset ι) (f : ι → MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (∏ i ∈ A, f i) e = ∏ i ∈ A, bits (f i) e := map_prod _ _ _

theorem bits_C {m : ℕ} (a : F) (e : Fin m → Bool) :
    bits (MvPolynomial.C a : MvPolynomial (X ⊕ Fin m) F) e = MvPolynomial.C a := by
  rw [bits, MvPolynomial.aeval_C]
  rfl

theorem bits_inl {m : ℕ} (x : X) (e : Fin m → Bool) :
    bits (MvPolynomial.X (Sum.inl x) : MvPolynomial (X ⊕ Fin m) F) e = MvPolynomial.X x := by
  simp [bits]

theorem bits_inr {m : ℕ} (i : Fin m) (e : Fin m → Bool) :
    bits (MvPolynomial.X (Sum.inr i) : MvPolynomial (X ⊕ Fin m) F) e = if e i then 1 else 0 := by
  simp [bits]

end Subset

end Nc
