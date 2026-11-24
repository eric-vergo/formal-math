/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Rate
import Paper.Scales
import Paper.HcGrid
import Paper.Transfer
import Paper.ApproxScales
import Nc.Rate.Circuit

/-!
# A coefficientwise lower bound for Hamiltonian cycles and permanents

The field dichotomy and coefficientwise bound come from the original formalization of
Appendices M and N by Claude (Anthropic). Eric Vergo and GPT-6.2 (OpenAI) extracted
the quantitative bound for use by both the exact and approximate endpoints.
-/

namespace Paper

open Finset MvPolynomial Nc Nc.Price Nc.CaseI Ov

universe u

theorem map_genHC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) :
    MvPolynomial.map φ (genHC R m) = genHC S m := by
  simp only [genHC, map_sum, map_prod, map_X]

/-- The permanent with integer coefficients. -/
noncomputable def permInt (m : ℕ) : MvPolynomial (Fin m × Fin m) ℤ :=
  ∑ σ : Equiv.Perm (Fin m), ∏ i, X (σ i, i)

theorem map_permInt (F : Type u) [Field F] (m : ℕ) :
    MvPolynomial.map (Int.castRingHom F) (permInt m) = genPerm F m := by
  simp only [permInt, genPerm, Matrix.permanent, Matrix.of_apply, map_sum, map_prod, map_X]

/-- KK, "the algebraic closure of the prime field of characteristic p". -/
theorem exists_closed (p : ℕ) (hp : p = 0 ∨ p.Prime) : ∃ (K : Type) (_ : Field K), IsAlgClosed K ∧ CharP K p := by
  rcases hp with rfl | hp
  · exact ⟨AlgebraicClosure ℚ, inferInstance, inferInstance, inferInstance⟩
  · have : Fact p.Prime := ⟨hp⟩
    exact ⟨AlgebraicClosure (ZMod p), inferInstance, inferInstance, inferInstance⟩

/-- 2 is not 0 in characteristic other than 2. -/
theorem two_ne_zero_of_char (K : Type) [Field K] (p : ℕ) [CharP K p] (hp : p = 0 ∨ p.Prime) (h2 : p ≠ 2) :
    (2 : K) ≠ 0 := by
  intro h
  have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h3
  rcases hp with rfl | hp
  · simp at h3
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

/-- "The bound of the contracting case, although its constant depends on p, exceeds that of the flat case for large m." -/
theorem thm_allfields_exceeds {P : ℕ → ℕ → Prop}
    (h : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨c, hc, m₁, h⟩ := h
  obtain ⟨m₂, hm₂⟩ := thm_main_calculation (1 / (c * 1600 ^ 2))
  refine ⟨m₁ + m₂, fun m hm s hs => lt_of_le_of_lt ?_ (h m (by omega) s hs)⟩
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_left (hm₂ m (by omega)) hc.le).trans_eq (mul_div_assoc _ _ _).symm)
  field_simp

/-- The bound 2^((log m)^(4/3)/1600²) in the form of the main theorems. -/
theorem beyond_of_rate {m s : ℕ} (hm : 2 ≤ m) (h : (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s) :
    (m : ℝ) ^ (1 / 1600 ^ 2 * Real.logb 2 m ^ (1 / 3 : ℝ)) < s := by
  rwa [thm_main_form hm, one_div_mul_eq_div]

/-- Combine the two family thresholds, imposing the permanent bound only away from
characteristic two. Both bounds then use an index at least two. -/
theorem common_family_threshold {p : ℕ} {H P : ℕ → Prop}
    (hc : ∃ M, ∀ m ≥ M, H m) (hp : p ≠ 2 → ∃ M, ∀ m ≥ M, P m) :
    ∃ M, ∀ m ≥ M, 2 ≤ m ∧ H m ∧ (p ≠ 2 → P m) := by
  obtain ⟨A, hA⟩ := hc
  by_cases he : p = 2
  · exact ⟨max A 2, fun m hm =>
      ⟨le_trans (le_max_right _ _) hm, hA m (le_trans (le_max_left _ _) hm),
        fun h => (h he).elim⟩⟩
  · obtain ⟨B, hB⟩ := hp he
    exact ⟨A + B + 2, fun m hm => ⟨by omega, hA m (by omega), fun _ => hB m (by omega)⟩⟩

theorem coeff_mul_T {R : Type} [CommRing R] (f : LaurentPolynomial R) (N i : ℤ) :
    (f * LaurentPolynomial.T N).coeff i = f.coeff (i - N) := by
  classical
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
  | C_mul_T n a =>
    rw [LaurentPolynomial.mul_T_assoc, ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩

theorem coeff_toLaurent_natCast {R : Type} [CommRing R] (f : Polynomial R) (i : ℕ) :
    (Polynomial.toLaurent f).coeff (i : ℤ) = f.coeff i := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ i

open Ten in
/-- **Paper: Lemma lem:few-approx.** "The lemma on sums with few terms remains true if f_j has coefficients in
k[ε,ε⁻¹] and t is the part of ε⁰ of the sum, no negative powers occurring." -/
theorem lem_few_approx {K : Type} [Field K] {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (φ : Spec K V)
    (P : Finset V) (t : Ten K V) (ht : ∀ q, q ∉ P → Subsingleton (t.ι q)) {J : ℕ} [NeZero J] (T : Fin J → Ten K V)
    (f : ∀ j p, t.ι p → (T j).ι p → LaurentPolynomial K)
    (h : ∀ x (i : ℤ), i ≤ 0 →
      (∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, f j p (x p) (y p)) * LaurentPolynomial.C ((T j).val y)).coeff i =
        if i = 0 then t.val x else 0) :
    φ.F t ≤ (J : ℝ) ^ hexp φ (Subtype.val : P → V) * univ.sup' univ_nonempty fun j => φ.F (T j) := by
  classical
  choose e g hg using fun (z : Σ (j : Fin J) (p : V), t.ι p × (T j).ι p) =>
    LaurentPolynomial.exists_T_pow (f z.1 z.2.1 z.2.2.1 z.2.2.2)
  let Δ : ℕ := univ.sup e
  let L : ∀ j p, t.ι p → (T j).ι p → Polynomial K := fun j p a b =>
    g ⟨j, p, a, b⟩ * Polynomial.X ^ (Δ - e ⟨j, p, a, b⟩)
  have hL : ∀ j p a b, Polynomial.toLaurent (L j p a b) = f j p a b * LaurentPolynomial.T (Δ : ℤ) := by
    intro j p a b
    have hle : e ⟨j, p, a, b⟩ ≤ Δ := Finset.le_sup (mem_univ _)
    simp only [L, map_mul, Polynomial.toLaurent_X_pow, hg, LaurentPolynomial.mul_T_assoc]
    congr 2
    omega
  have hB : BSum (Fintype.card V * Δ) t T := by
    refine ⟨L, fun x i hi => ?_⟩
    have e1 : Polynomial.toLaurent (∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, L j p (x p) (y p)) * Polynomial.C ((T j).val y)) =
        (∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, f j p (x p) (y p)) * LaurentPolynomial.C ((T j).val y)) *
          LaurentPolynomial.T ((Fintype.card V * Δ : ℕ) : ℤ) := by
      simp only [map_sum, map_mul, map_prod, Polynomial.toLaurent_C, hL, Finset.prod_mul_distrib, Finset.prod_const,
        card_univ, LaurentPolynomial.T_pow, Finset.sum_mul, Nat.cast_mul]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [← coeff_toLaurent_natCast, e1, coeff_mul_T, h x _ (by omega)]
    by_cases hid : i = Fintype.card V * Δ
    · rw [ite_eq_left hid, ite_eq_left (by omega)]
    · rw [ite_eq_right hid, ite_eq_right (by omega)]
  have := few φ (Subtype.val : P → V) t (fun q hq => ht q fun hmem => hq ⟨⟨q, hmem⟩, rfl⟩) hB
    (M := univ.sup' univ_nonempty fun j => φ.F (T j)) (fun j => Finset.le_sup' (fun j => φ.F (T j)) (mem_univ j))
  rwa [Fintype.card_fin] at this

/-- **Paper: Lemma lem:few.** "Let P ⊆ V, let t be a tensor on P and T_1, …, T_J tensors on V, and suppose that
t = ∑_j ⟨f_j|T_j⟩, where each f_j consists of one functional at every party outside P. Then φ(t) ≤ J^g(P) max_j φ(T_j)
for every spectral point on V." (A tensor on P is one on V with legs of size at most one outside P.) It is Lemma
lem:few-approx with constant local maps. -/
theorem lem_few {K : Type} [Field K] {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (φ : Spec K V) (P : Finset V)
    (t : Ten K V) (ht : ∀ q, q ∉ P → Subsingleton (t.ι q)) {J : ℕ} [NeZero J] (T : Fin J → Ten K V)
    (h : Ten.SumRestr t T) :
    φ.F t ≤ (J : ℝ) ^ hexp φ (Subtype.val : P → V) * univ.sup' univ_nonempty fun j => φ.F (T j) := by
  obtain ⟨L, hL⟩ := h
  refine lem_few_approx φ P t ht T (fun j p a b => LaurentPolynomial.C (L j p a b)) fun x i _ => ?_
  have e : ∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, LaurentPolynomial.C (L j p (x p) (y p))) *
      LaurentPolynomial.C ((T j).val y) = LaurentPolynomial.C (t.val x) := by
    simp only [← map_prod, ← map_mul, ← map_sum, hL x, Ten.app]
  rw [e, ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp only [eq_comm]

/-- "Cut the constants off": finitely many series can be replaced by Laurent polynomials so that the products of
n of them keep the coefficients of ε^i, i ≤ 0. -/
theorem exists_cut_off {K : Type} [Field K] {ι V : Type} [Fintype ι] [Fintype V] (c : ι → LaurentSeries K) :
    ∃ q : ι → LaurentPolynomial K, ∀ (w : V → ι) (i : ℤ), i ≤ 0 →
      (∏ p, laurentToSeries K (q (w p))).coeff i = (∏ p, c (w p)).coeff i := by
  classical
  let Δ : ℤ := ((univ.sup fun a => (c a).order.natAbs : ℕ) : ℤ)
  have hΔ : 0 ≤ Δ := Int.natCast_nonneg _
  have hc : ∀ a, ∀ i < -Δ, (c a).coeff i = 0 := fun a i hi => HahnSeries.coeff_eq_zero_of_lt_order (by
    have : (c a).order.natAbs ≤ univ.sup fun a => (c a).order.natAbs :=
      Finset.le_sup (f := fun a => (c a).order.natAbs) (mem_univ a)
    omega)
  let N : ℤ := (Fintype.card V : ℤ) * Δ + 1
  choose q hq using fun a => exists_laurentPolynomial_coeff (c a) N
  have hN : -Δ ≤ N := by
    have : 0 ≤ (Fintype.card V : ℤ) * Δ := by positivity
    omega
  refine ⟨q, fun w i hi => ?_⟩
  have key : ∀ S : Finset V,
      (∀ i < -(S.card : ℤ) * Δ, (∏ p ∈ S, c (w p)).coeff i = 0) ∧
      (∀ i < -(S.card : ℤ) * Δ, (∏ p ∈ S, laurentToSeries K (q (w p))).coeff i = 0) ∧
      ∀ i < N - (S.card : ℤ) * Δ, (∏ p ∈ S, laurentToSeries K (q (w p)) - ∏ p ∈ S, c (w p)).coeff i = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [card_empty, Nat.cast_zero, neg_zero, zero_mul, prod_empty, sub_self, HahnSeries.coeff_zero,
        implies_true, and_true]
      exact ⟨fun i hi => by simp [HahnSeries.coeff_one, hi.ne], fun i hi => by simp [HahnSeries.coeff_one, hi.ne]⟩
    | insert a S ha ih =>
      obtain ⟨hC, hQ, hD⟩ := ih
      have hqa : ∀ i < -Δ, (laurentToSeries K (q (w a))).coeff i = 0 := fun i hi => by
        rw [coeff_laurentToSeries, hq (w a) i (by omega)]
        exact hc _ i hi
      have hd : ∀ i < N, (laurentToSeries K (q (w a)) - c (w a)).coeff i = 0 := fun i hi => by
        rw [HahnSeries.coeff_sub, coeff_laurentToSeries, hq (w a) i hi, sub_self]
      simp only [prod_insert ha, card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      refine ⟨fun i hi => coeff_mul_eq_zero (hc (w a)) hC (by linarith), fun i hi => coeff_mul_eq_zero hqa hQ (by linarith),
        fun i hi => ?_⟩
      rw [show laurentToSeries K (q (w a)) * (∏ p ∈ S, laurentToSeries K (q (w p))) - c (w a) * ∏ p ∈ S, c (w p) =
        (laurentToSeries K (q (w a)) - c (w a)) * (∏ p ∈ S, laurentToSeries K (q (w p))) +
          c (w a) * (∏ p ∈ S, laurentToSeries K (q (w p)) - ∏ p ∈ S, c (w p)) by ring, HahnSeries.coeff_add,
        coeff_mul_eq_zero hd hQ (by linarith), coeff_mul_eq_zero (hc (w a)) hD (by linarith), add_zero]
  have h := (key univ).2.2 i (by rw [card_univ]; omega)
  rwa [HahnSeries.coeff_sub, sub_eq_zero] at h

/-- A wire over the Laurent series is the one over k. -/
theorem wire_series {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) (p q : I)
    (y : ∀ r, (Ten.wire K n p q).ι r) :
    (Ten.wire (LaurentSeries K) n p q).val y = HahnSeries.C ((Ten.wire K n p q).val y) := by
  unfold Ten.wire Ten.push Ten.unit
  dsimp only
  split_ifs <;> simp

/-- The hub tensors over the Laurent series are those over k. -/
theorem hubTen_series {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] {k ℓ L : ℕ} (π : End k → I)
    (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k)) (y : ∀ p, (hubTen K ℓ L π hub S).ι p) :
    (hubTen (LaurentSeries K) ℓ L π hub S).val y = HahnSeries.C ((hubTen K ℓ L π hub S).val y) := by
  show (∏ a, (Ten.wire (LaurentSeries K) (2 ^ ℓ) (π a) (hubOf hub S a)).val fun p => (y p).1 a) *
      (Ten.wire (LaurentSeries K) L (hub S true) (hub S false)).val (fun p => (y p).2) =
    HahnSeries.C ((∏ a, (Ten.wire K (2 ^ ℓ) (π a) (hubOf hub S a)).val fun p => (y p).1 a) *
      (Ten.wire K L (hub S true) (hub S false)).val fun p => (y p).2)
  rw [map_mul, map_prod]
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun a _ => wire_series (2 ^ ℓ) (π a) (hubOf hub S a) fun p => (y p).1 a)
    (wire_series L (hub S true) (hub S false) fun p => (y p).2)

/-- The hub decomposition over the Laurent series: the coefficient of an entry is a sum over the balanced sets of the
hub tensors over k, with functionals in k((ε)). -/
theorem hubs_series {K : Type} [Field K] {k ℓ s : ℕ} (hk : 2 ≤ k)
    {Q : MvPolynomial (Fin k × Ix k ℓ) (LaurentSeries K)} (hQ : Computes Q s) (π : End k → RPt k) :
    ∃ M : ∀ (j : Fin (Fintype.card (bal (univ : Finset (Fin k))))) (p : RPt k),
        (Ten.push π (fklTen K k ℓ)).ι p → (hubTen K ℓ s π hubPt (balEnum k j).1).ι p → LaurentSeries K,
      ∀ x : ∀ p, (Ten.push π (fklTen K k ℓ)).ι p, cf univ Q (tables fun a => x (π a) ⟨a, rfl⟩) =
        ∑ j, ∑ y : ∀ p, (hubTen K ℓ s π hubPt (balEnum k j).1).ι p,
          (∏ p, M j p (x p) (y p)) * HahnSeries.C ((hubTen K ℓ s π hubPt (balEnum k j).1).val y) := by
  obtain ⟨M, hM⟩ := (prop_flat_lower_sum hk hQ π hubPt).reindex (balEnum k)
  refine ⟨fun j p a b => M j p a b, fun x => ?_⟩
  have h1 := hM x
  refine Eq.trans ?_ (h1.trans (Finset.sum_congr rfl fun j _ => ?_))
  · rfl
  refine Fintype.sum_equiv (Equiv.refl _) _ _ fun y => ?_
  refine congrArg₂ (· * ·) rfl ?_
  exact hubTen_series (K := K) π hubPt _ _

/-- "So Proposition prop:flat-rate holds for approximating circuits: cut the constants off, and note that Lemma
lem:balanced holds over every commutative ring." -/
theorem flat_rate_approximating {K : Type} [Field K] (hK : Flat K) {k : ℕ} (hk : 2 ≤ k) {ℓ s : ℕ}
    (hℓ : 100 * √k ≤ (ℓ : ℝ)) (hcomp : Approximates (fkl K k ℓ) s) :
    (ℓ : ℝ) * (k * √k) / 14 ≤ Real.logb 2 s := by
  classical
  obtain ⟨Q, hQ, hQf⟩ := hcomp
  have hs : 1 ≤ s := by
    obtain ⟨l, -, a, ha, -⟩ := hQ
    omega
  refine rate_of_someSetPays hK hk hℓ hs fun φ => ?_
  have := bal_nonempty hk
  have : NeZero (Fintype.card (bal (univ : Finset (Fin k)))) := ⟨Fintype.card_ne_zero⟩
  have : Nonempty (RPt k) := ⟨hubPt ∅ true⟩
  let π : End k → RPt k := Sum.inl
  let T : Fin (Fintype.card (bal (univ : Finset (Fin k)))) → Ten K (RPt k) := fun j =>
    hubTen K ℓ s π hubPt (balEnum k j).1
  -- the hub decomposition over the Laurent series
  obtain ⟨M, hM⟩ := hubs_series hk hQ π
  -- and with the functionals cut off
  obtain ⟨q, hq⟩ := exists_cut_off (V := RPt k)
    fun e : Σ j, Σ p : RPt k, (Ten.push π (fklTen K k ℓ)).ι p × (T j).ι p => M e.1 e.2.1 e.2.2.1 e.2.2.2
  refine someSetPays_of_few φ hs (lem_few_approx φ _ _ (fklTen_onEnds K k ℓ) T
    (fun j p a b => q ⟨j, p, a, b⟩) fun x i hi => ?_)
  -- the cut-off functionals give the same coefficients of ε^i, i ≤ 0
  have hterm : ∀ (j) (y : ∀ p, (T j).ι p), (laurentToSeries K ((∏ p, q ⟨j, p, x p, y p⟩) *
      LaurentPolynomial.C ((T j).val y))).coeff i =
        ((∏ p, M j p (x p) (y p)) * HahnSeries.C ((T j).val y)).coeff i := by
    intro j y
    have eC : laurentToSeries K (LaurentPolynomial.C ((T j).val y)) = HahnSeries.C ((T j).val y) := by
      ext n
      rw [coeff_laurentToSeries, ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single, HahnSeries.C_apply,
        HahnSeries.coeff_single, Finsupp.single_apply]
      simp only [eq_comm]
      congr
    rw [map_mul, map_prod, eC, mul_comm _ (HahnSeries.C _), mul_comm _ (HahnSeries.C _),
      HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul,
      hq (fun p => ⟨j, p, x p, y p⟩) i hi]
  have e : (Ten.push π (fklTen K k ℓ)).val x = cf univ (fkl K k ℓ) (tables fun a => x (π a) ⟨a, rfl⟩) :=
    fklTen_val K fun a => x (π a) ⟨a, rfl⟩
  have hx : (cf univ Q (tables fun a => x (π a) ⟨a, rfl⟩)) =
      ∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, M j p (x p) (y p)) * HahnSeries.C ((T j).val y) := hM x
  rw [e, ← coeff_laurentToSeries]
  refine Eq.trans ?_ (hQf (mono univ (tables fun a => x (π a) ⟨a, rfl⟩)) i hi)
  rw [show Q.coeff (mono univ (tables fun a => x (π a) ⟨a, rfl⟩)) = cf univ Q (tables fun a => x (π a) ⟨a, rfl⟩) from rfl,
    hx]
  simp only [map_sum, HahnSeries.coeff_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => hterm j y

/-- **Paper: Proposition prop:flat-rate.** "In the flat case, for k ≥ 2 and ℓ ≥ 100√k every circuit over k for f_{k,ℓ}
has at least 2^(ℓk^(3/2)/16) gates." An exact circuit approximates with the same number of gates. -/
theorem prop_flat_rate {K : Type} [Field K] (hK : Flat K) {k : ℕ} (hk : 2 ≤ k) {ℓ s : ℕ}
    (hℓ : 100 * √k ≤ (ℓ : ℝ)) (hcomp : Computes (fkl K k ℓ) s) :
    (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ s := by
  have hs : 1 ≤ s := by
    obtain ⟨l, -, a, ha, -⟩ := hcomp
    omega
  exact rate_pow hk hs (flat_rate_approximating hK hk hℓ (approximates_of_computes hcomp))

/-- **Paper: Proposition prop:flat-rate**, for f_{k,ℓ} with exactly the printed variables. -/
theorem prop_flat_rate_printed {K : Type} [Field K] (hK : Flat K) {k : ℕ} (hk : 2 ≤ k) {ℓ s : ℕ}
    (hℓ : 100 * √k ≤ (ℓ : ℝ)) (hcomp : Computes (fklExact K k ℓ) s) :
    (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ s :=
  prop_flat_rate hK hk hℓ (fklExact_computes.1 hcomp)

/-- "… and with it Theorem thm:flat-rate", for every family that is complete for grid sums. -/
theorem flat_rate_approx_complete (κ : ℕ) : ∃ m₀ : ℕ, ∀ (K : Type) [Field K], Flat K →
    ∀ G : ∀ S : ℕ, MvPolynomial (Fin S × Fin S) K, GridComplete K G κ →
    ∀ m ≥ m₀, ∀ s : ℕ, Approximates (G m) s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ := rate_of_projection κ
  refine ⟨m₀, fun K _ hK G hG => h _ fun k ℓ m s hk hℓ hℓk hm hs => ?_⟩
  obtain ⟨E, hE, he⟩ := fkl_complete hG hk hℓ hm
  have hap : Approximates (fkl K k ℓ) (5 * s) := he ▸ hs.aeval E hE
  refine rate_pow hk ?_ (flat_rate_approximating hK hk hℓk hap)
  obtain ⟨Q, ⟨l, -, a, ha, -⟩, -⟩ := hap
  omega

/-- Theorem thm:flat-rate for every family that is complete for grid sums ("the factor 3 becomes 40"). -/
theorem flat_rate_complete (κ : ℕ) : ∃ m₀ : ℕ, ∀ (K : Type) [Field K], Flat K →
    ∀ G : ∀ S : ℕ, MvPolynomial (Fin S × Fin S) K, GridComplete K G κ →
    ∀ m ≥ m₀, ∀ s : ℕ, Computes (G m) s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ := flat_rate_approx_complete κ
  exact ⟨m₀, fun K _ hK G hG m hm s hs => h K hK G hG m hm s (approximates_of_computes hs)⟩

/-- **Paper: Theorem thm:flat-rate.** "In the flat case there is m₀ such that for m ≥ m₀ every circuit over k for PERM_m
has more than 2^((log m)^(4/3)/1600²) gates." -/
theorem thm_flat_rate {K : Type} [Field K] (hK : Flat K) (h2 : (2 : K) ≠ 0) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Computes (genPerm K m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨M, h⟩ := flat_rate_complete 3
  exact ⟨M, h K hK _ (gridComplete_perm h2)⟩

/-- **Paper: Theorem thm:flat-simple.** "In the flat case, for every C there is m₀ such that PERM_m has no circuit
over k with m^C gates for m ≥ m₀." -/
theorem thm_flat_simple {K : Type} [Field K] (hK : Flat K) (h2 : (2 : K) ≠ 0) (C : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ¬ Computes (genPerm K m) (m ^ C) := by
  obtain ⟨A, hA⟩ := thm_flat_rate hK h2
  obtain ⟨M, hM⟩ := excludes_poly_size (P := fun m s => Computes (genPerm K m) s)
    (c := 1 / 1600 ^ 2) (by norm_num) (A := A + 2) (fun m hm s hs => by
      rw [thm_main_form (by omega), one_div_mul_eq_div]
      exact hA m (by omega) s hs) C
  exact ⟨M, fun m hm => hM m hm _ le_rfl⟩

/-- The contracting case with the calculation of Theorem thm:contracting. -/
theorem contracting_approx_rate {K : Type} [Field K] (hK : Contracting K)
    {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ} (hG : GridComplete K G κ) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Approximates (G m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  obtain ⟨C, M₁, h⟩ := contracting_approx_complete hK hG
  exact quasi_of_exponents (P := fun m s => Approximates (G m) s)
    (fun _ _ _ hst ⟨Q, hQ, hQf⟩ => ⟨Q, Computes.mono hQ hst, hQf⟩) h

open NS1 in
/-- The contracting case for a family that is complete for grid sums. -/
theorem contracting_complete {K : Type} [Field K] (hK : Contracting K)
    {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ} (hG : Nc.GridComplete K G κ) :
    ∃ C M₁ : ℕ, ∀ M ≥ M₁, ∀ a : ℕ, lg M ^ (C * a) ≤ M → ¬ Nc.Computes (G M) (M ^ a) := by
  obtain ⟨C, M₁, h⟩ := contracting_approx_complete hK hG
  exact ⟨C, M₁, fun M hM a ha hc => h M hM a ha (approximates_of_computes hc)⟩

/-- **Paper: Theorem thm:contracting.** "In the contracting case there are c > 0 and m₀ such that for m ≥ m₀ every
circuit over k for PERM_m has more than 2^(c(log m)²/log log m) gates." -/
theorem thm_contracting {K : Type} [Field K] (hK : Contracting K) (h2 : (2 : K) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Nc.Computes (Nc.genPerm K m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  obtain ⟨c, hc, m₀, h⟩ := contracting_approx_rate hK (gridComplete_perm h2)
  exact ⟨c, hc, m₀, fun m hm s hs => h m hm s (approximates_of_computes hs)⟩

/-- Both cases over KK, for circuits with constants in KK[ε,ε⁻¹]. -/
theorem approx_rate_closed {K : Type} [Field K] {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ}
    (hG : GridComplete K G κ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, ∀ P : MvPolynomial (Fin m × Fin m) (LaurentPolynomial K), Computes P s →
      (∀ d, (∀ i : ℤ, i < 0 → (P.coeff d).coeff i = 0) ∧ (P.coeff d).coeff 0 = (G m).coeff d) →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Approximates (G m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
    rcases thm_alt K with hK | hK
    · obtain ⟨m₀, h⟩ := flat_rate_approx_complete κ
      exact ⟨m₀, h K hK _ hG⟩
    · exact thm_allfields_exceeds (contracting_approx_rate hK hG)
  exact ⟨m₀, fun m hm s P hP hc => h m hm s
    (Approximates.of_laurentPolynomial hP fun d => (coeff_nonpos_iff _ _).2 (hc d))⟩

/-- The uniform circuit bound over each characteristic for coefficientwise approximations. -/
theorem border_rate_allfields : ∀ p : ℕ, p = 0 ∨ p.Prime → ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
    (Approximates (genHC F m) s → (m : ℝ) ^ (1 / 1600 ^ 2 * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) ∧
    (p ≠ 2 → Approximates (genPerm F m) s → (m : ℝ) ^ (1 / 1600 ^ 2 * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) := by
  intro p hp
  obtain ⟨K, _, _, _⟩ := exists_closed p hp
  obtain ⟨M, hM⟩ := common_family_threshold (p := p) (approx_rate_closed (gridComplete_hc K))
    fun hne => approx_rate_closed (gridComplete_perm (two_ne_zero_of_char K p hp hne))
  refine ⟨M, fun F _ _ m hm s => ?_⟩
  obtain ⟨hm₂, hHC, hPerm⟩ := hM m hm
  constructor
  · intro hs
    rw [← map_genHC (Int.castRingHom F)] at hs
    obtain ⟨P, hP, hc⟩ := lem_transfer_approx (KK := K) p (genHC ℤ m) hs
    rw [map_genHC] at hc
    exact beyond_of_rate hm₂ (hHC s P hP hc)
  · intro hne hs
    rw [← map_permInt] at hs
    obtain ⟨P, hP, hc⟩ := lem_transfer_approx (KK := K) p (permInt m) hs
    rw [map_permInt] at hc
    exact beyond_of_rate hm₂ (hPerm hne s P hP hc)

end Paper
