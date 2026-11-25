/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Scales
import Paper.NoAcc
import Paper.Circuit
import Paper.Cuts
import Paper.ApproxRound

/-!
# The paper, appendix "Approximate computation": no approximate accelerators

The approximate scale-up (`prop_approx_acc_scales`) carries an approximate accelerator to
arbitrarily large scales; rescaling keeps every property of the constants in `RescaleStable`.
Theorem thm:noacc (`thm_noacc`) runs it on an exact accelerator whose constants are read as
constant Laurent polynomials, which stay constant, and Proposition prop:approx-acc
(`prop_approx_acc`) runs it on an approximate accelerator and returns to exact values.
-/

set_option linter.unusedSectionVars false

namespace Paper

open NS1
open _root_.NS1.Tree LaurentPolynomial

variable {A : Type} [CommRing A] {θ : List Bool → A} {E : Type} [CommRing E] [Algebra A E]

/-- **Paper: the definition of an approximate accelerator.** "An approximate accelerator is defined as in Definition
def:acc, with constants in R[ε,ε⁻¹] and values only required to lie in pv(z) + εR[ε]." As the values are in R[ε,ε⁻¹],
this says that the difference has no coefficient at an exponent ≤ 0. -/
theorem def_approx_acc (θ : List Bool → A) (R : Type) [CommRing R] [Algebra A R] (H v s : ℕ) :
    HasAccA θ R H v s ↔ ∃ (K : KT R[T;T⁻¹]) (B : ℕ) (D : Tree),
      (∀ z, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧
        ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ v ^ (H - 16) ∧ ∀ p ∈ r.bill, K.InB B p) ∧
      (∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z → ∀ i : ℤ, i ≤ 0 →
        (((evl θ (Fm.ofTree D) z).map fun r => algebraMap A R[T;T⁻¹] r.th * (r.bill.map K.lk).prod).sum -
          algebraMap A R[T;T⁻¹] (pv θ z)).coeff i = 0) ∧
      K.nds ≤ s ∧ D.size ≤ s ∧ K.ht ≤ lg (max (v ^ H) s) ^ 2 ∧ B ≤ lg (max (v ^ H) s) ^ 3 := by
  constructor
  · rintro ⟨K, B, D, ⟨h1, h2⟩, h3, h4, h5, h6⟩
    exact ⟨K, B, D, h1, fun z hz hp i hi => h2 z hz hp i (by omega), h3, h4, h5, h6⟩
  · rintro ⟨K, B, D, h1, h2, h3, h4, h5, h6⟩
    exact ⟨K, B, D, ⟨h1, fun z hz hp i hi => h2 z hz hp i (by omega)⟩, h3, h4, h5, h6⟩

/-- The scales that are large enough. -/
structure LargeScale (h cB U : ℕ) : Prop where
  two : 4 ≤ U
  cst_le : cst ≤ U
  poly : ∀ u, U ≤ u → 1000 * (3 * cB) ^ 3 * lg u ^ 9 ≤ u

/-- The bound of all logarithmic quantities. -/
theorem cube_le {h cB U u X : ℕ} (hL : LargeScale h cB U) (hu : U ≤ u) (hX : X ≤ 3 * cB * lg u ^ 3) :
    1000 * X ^ 3 ≤ u := by
  calc 1000 * X ^ 3 ≤ 1000 * (3 * cB * lg u ^ 3) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX 3)
    _ = 1000 * (3 * cB) ^ 3 * lg u ^ 9 := by ring
    _ ≤ u := hL.poly u hu

set_option maxHeartbeats 1000000 in
/-- **Paper: proof of Proposition prop:approx-acc, One round, repeated from a scale to its fifth power.** "The time again
has a factor u to spare." The new constants keep every property `Q` of the old ones that rescaling keeps. -/
theorem prop_approx_acc_step {h cB U Δ cΔ b₀ : ℕ} (hh : 17 ≤ h) (hC : ∀ u, U ≤ u → CutAt θ (16 * h) u 10)
    (hL : LargeScale h (2 * cB) U) (hcB : 2000 * h ≤ cB) (hcΔ : 4 * cB ≤ cΔ) {Q : E[T;T⁻¹] → Prop}
    (hQ : RescaleStable A Q) {u : ℕ} {K : KT E[T;T⁻¹]} {B : ℕ} {D : Tree}
    (hI : InvA θ h cB U Δ cΔ b₀ u K B D) (hK : K.All Q) :
    ∃ (K' : KT E[T;T⁻¹]) (B' : ℕ) (D' : Tree), InvA θ h cB U Δ cΔ b₀ (u ^ 5) K' B' D' ∧ K'.All Q ∧
      IsAccA θ (16 * h) (u ^ 5) ((u ^ 5) ^ (16 * h - 17)) K' B' D' := by
  have hu := hI.big
  have hcs : cst ≤ u := hL.cst_le.trans hu
  have hu2000 : 2000 ≤ u := by
    rw [cst_def] at hcs
    omega
  have hu1 : 1 ≤ u := by omega
  have hl2 := lg_ge_two (show 4 ≤ u by omega)
  obtain ⟨l, hl⟩ : ∃ l, l = lg u := ⟨_, rfl⟩
  have a1 := hI.B_le
  have a2 := hI.ht
  have a3 := hI.B_lin
  have a4 := hI.ht_lin
  rw [← hl] at hl2 a1 a2 a3 a4
  have hl3 : l ≤ l ^ 3 := Nat.le_self_pow (by norm_num) l
  have h8 : 8 ≤ l ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ l ^ 3 := Nat.pow_le_pow_left hl2 3
  obtain ⟨J, hJ⟩ : ∃ J, J = (80 * h + 1) * l := ⟨_, rfl⟩
  have hJ1 : J ≤ 81 * h * l := by rw [hJ]; exact Nat.mul_le_mul_right _ (by omega)
  have hcl : 2000 * h * l ≤ cB * l ^ 3 := (Nat.mul_le_mul_right _ hcB).trans (Nat.mul_le_mul_left _ hl3)
  have hl1 : 1 ≤ l := by omega
  have hhl : h ≤ h * l := Nat.le_mul_of_pos_right _ hl1
  have e1 : 81 * h * l = 81 * (h * l) := by ring
  have e2 : 2000 * h * l = 2000 * (h * l) := by ring
  have hcl8 : 34000 * 8 ≤ cB * l ^ 3 := Nat.mul_le_mul (le_trans (by omega) hcB) h8
  have e3 : 3 * (2 * cB) * l ^ 3 = 6 * (cB * l ^ 3) := by ring
  obtain ⟨X, hX⟩ : ∃ X, X = B + (2 * 5 + 2) * (J + 1) + K.ht + K.ht + 10 := ⟨_, rfl⟩
  have hX6 : X ≤ 3 * (2 * cB) * l ^ 3 := by omega
  obtain ⟨K', D', hD', hs', hn', hh', hsp, hth⟩ := prop_approx_acc_next hh (α := 5) le_rfl (hC u hu) hcs hI.acc
    (by
      calc K.nds * (4 * 5 + 5) ≤ u * u := Nat.mul_le_mul hI.nds (by omega)
        _ = u ^ 2 := (pow_two u).symm
        _ ≤ u ^ (h * 5) := pow_le_pow hu1 (by omega))
    (hI.size.trans (pow_le_pow hu1 (by omega))) hI.span (Nat.two_pow_pos _) ((rescaleStable_thin Δ).and hQ)
    (hI.thin.and hK) (J := J) (by
      have : 16 * h * 5 + 1 = 80 * h + 1 := by ring
      rw [this, hJ, Nat.mul_comm (80 * h + 1) l, pow_mul, hl]
      exact Nat.pow_lt_pow_left (lt_two_pow_lg u) (by omega)) hX.ge (cube_le hL hu (by rw [← hl]; exact hX6))
  have hlg : 4 * l ≤ lg (u ^ 5) := hl ▸ le_lg_four (by omega)
  have hlg3 : 64 * l ^ 3 ≤ lg (u ^ 5) ^ 3 := by
    calc 64 * l ^ 3 = (4 * l) ^ 3 := by ring
      _ ≤ _ := Nat.pow_le_pow_left hlg 3
  have hc64 : 64 * (cB * l ^ 3) ≤ cB * lg (u ^ 5) ^ 3 := by
    calc 64 * (cB * l ^ 3) = cB * (64 * l ^ 3) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hlg3
  have hd64 : 64 * (cΔ * l ^ 3) ≤ cΔ * lg (u ^ 5) ^ 3 := by
    calc 64 * (cΔ * l ^ 3) = cΔ * (64 * l ^ 3) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hlg3
  have hlin : 2000 * h * l + 2000 * (h * l) ≤ 2000 * h * lg (u ^ 5) := by
    have := Nat.mul_le_mul_left (2000 * h) (show 2 * l ≤ lg (u ^ 5) by omega)
    have e : 2000 * h * (2 * l) = 4000 * (h * l) := by ring
    omega
  have hu5 : u ≤ u ^ 5 := Nat.le_self_pow (by norm_num) u
  have h17 : IsAccA θ (16 * h) (u ^ 5) ((u ^ 5) ^ (16 * h - 17)) K' (B + (2 * 5 + 1) * J) D' := by
    refine hD'.mono ?_ le_rfl
    rw [← pow_mul]
    exact pow_le_pow hu1 (by omega)
  refine ⟨K', _, D', ⟨h17.mono (pow_le_pow (by omega) (by omega)) le_rfl, hu.trans hu5, ?_, hs', by omega, by omega,
    by omega, by omega, ?_, hth.imp fun _ hc => hc.1⟩, hth.imp fun _ hc => hc.2, h17⟩
  · calc K'.nds ≤ K.nds * (4 * 5 + 5) := hn'
      _ ≤ u * u ^ 4 := Nat.mul_le_mul hI.nds (le_trans (by omega) (Nat.le_self_pow (by norm_num) u))
      _ = u ^ 5 := by ring
  · refine hsp.imp fun c hc => hc.mono ?_
    rw [← pow_add, ← pow_mul, ← hl]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : 4 * (cB * l ^ 3) ≤ cΔ * l ^ 3 := by
      calc 4 * (cB * l ^ 3) = 4 * cB * l ^ 3 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ hcΔ
    omega

/-- Arbitrarily large scales, with one power of time to spare; the constants keep every property `Q` of the given ones
that rescaling keeps. -/
theorem prop_approx_acc_all_scales {h cB U Δ cΔ b₀ : ℕ} (hh : 17 ≤ h) (hC : ∀ u, U ≤ u → CutAt θ (16 * h) u 10)
    (hL : LargeScale h (2 * cB) U) (hcB : 2000 * h ≤ cB) (hcΔ : 4 * cB ≤ cΔ) {Q : E[T;T⁻¹] → Prop}
    (hQ : RescaleStable A Q) {u : ℕ} {K : KT E[T;T⁻¹]} {B : ℕ} {D : Tree}
    (hI : InvA θ h cB U Δ cΔ b₀ u K B D) (hK : K.All Q) (n : ℕ) :
    ∃ (u' : ℕ) (K' : KT E[T;T⁻¹]) (B' : ℕ) (D' : Tree), n ≤ u' ∧ InvA θ h cB U Δ cΔ b₀ u' K' B' D' ∧
      K'.All Q ∧ IsAccA θ (16 * h) u' (u' ^ (16 * h - 17)) K' B' D' := by
  induction n with
  | zero =>
    obtain ⟨K', B', D', hI', hK', hA⟩ := prop_approx_acc_step (hI := hI) hh hC hL hcB hcΔ hQ hK
    exact ⟨_, K', B', D', Nat.zero_le _, hI', hK', hA⟩
  | succ n ih =>
    obtain ⟨u', K', B', D', hn, hI', hK', -⟩ := ih
    obtain ⟨K'', B'', D'', hI'', hK'', hA⟩ := prop_approx_acc_step (hI := hI') hh hC hL hcB hcΔ hQ hK'
    refine ⟨u' ^ 5, K'', B'', D'', ?_, hI'', hK'', hA⟩
    have h4 : 4 ≤ u' := hL.two.trans hI'.big
    have : u' * 4 ≤ u' ^ 5 := by
      calc u' * 4 ≤ u' * u' ^ 4 := Nat.mul_le_mul_left _ (h4.trans (Nat.le_self_pow (by norm_num) u'))
        _ = u' ^ 5 := by ring
    omega

set_option maxHeartbeats 1000000 in
/-- **Paper: proof of Proposition prop:approx-acc, Back to exact values, with the sizes.** At a scale that is large against the numbers of the invariant there is an
exact accelerator of size a fixed power of the scale. -/
theorem prop_approx_acc_hasAcc {h cB U Δ cΔ b₀ : ℕ} (hh : 17 ≤ h) {u : ℕ} {K : KT E[T;T⁻¹]} {B : ℕ} {D : Tree}
    (hI : InvA θ h cB U Δ cΔ b₀ u K B D) (hA : IsAccA θ (16 * h) u (u ^ (16 * h - 17)) K B D)
    (hb : b₀ ≤ lg u) (hΔ : Δ ≤ lg u) (hu : 2000 ≤ u)
    (hsmall : 1000 * ((cΔ + 20000 * h + xcst + 1000) * lg u ^ 3) ^ 3 ≤ u) :
    HasAcc θ E (16 * h) u (u ^ (4400 * h + 6)) := by
  have hu1 : 1 ≤ u := by omega
  have hl2 := lg_ge_two (show 4 ≤ u by omega)
  have hltu := lt_two_pow_lg u
  have hspan := hI.span
  have a1 := hI.B_lin
  have a2 := hI.ht_lin
  obtain ⟨l, hl⟩ : ∃ l, l = lg u := ⟨_, rfl⟩
  rw [← hl] at hl2 hltu hspan a1 a2 hb hΔ hsmall
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (cΔ + 20000 * h + xcst + 1000) * l ^ 3 := ⟨_, rfl⟩
  rw [← hZ] at hsmall
  have hl1 : 1 ≤ l := by omega
  have hl3 : l ≤ l ^ 3 := Nat.le_self_pow (by norm_num) l
  have hZ1 : cΔ * l ^ 3 + 20000 * (h * l) + xcst + 1000 ≤ Z := by
    have e : (cΔ + 20000 * h + xcst + 1000) * l ^ 3 = cΔ * l ^ 3 + 20000 * (h * l ^ 3) + xcst * l ^ 3 + 1000 * l ^ 3 := by
      ring
    have := Nat.mul_le_mul_left h hl3
    have := Nat.le_mul_of_pos_right xcst (show 0 < l ^ 3 by omega)
    omega
  have hlhl : l ≤ h * l := Nat.le_mul_of_pos_left _ (by omega)
  have e2 : 2000 * h * l = 2000 * (h * l) := by ring
  obtain ⟨J, hJ⟩ : ∃ J, J = 16 * (h * l) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = B + J + l + 2 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 2 * l + J + B + cΔ * l ^ 3 + 1 := ⟨_, rfl⟩
  have hZ3 : Z ≤ Z ^ 3 := Nat.le_self_pow (by norm_num) Z
  have hZ2 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hJpow : u ^ (16 * h - 17) < 2 ^ J := by
    calc u ^ (16 * h - 17) ≤ u ^ (16 * h) := pow_le_pow hu1 (by omega)
      _ < (2 ^ l) ^ (16 * h) := Nat.pow_lt_pow_left hltu (by omega)
      _ = 2 ^ J := by rw [hJ, ← pow_mul]; congr 1; ring
  obtain ⟨nB, hnB⟩ : ∃ n, n = (K.expand B).nds := ⟨_, rfl⟩
  have hnB2 : nB ≤ u ^ 2 := by
    calc nB ≤ K.nds * (2 * B + 1) := hnB ▸ KT.nds_expand B K
      _ ≤ u * u := Nat.mul_le_mul hI.nds (by omega)
      _ = u ^ 2 := (pow_two u).symm
  have pu : ∀ a, u ^ (a + 1) = u * u ^ a := fun a => by rw [pow_succ]; ring
  have pbig : ∀ a, 2000 * u ^ a ≤ u ^ (a + 1) := fun a => by rw [pu]; exact Nat.mul_le_mul_right _ hu
  have hu2l : u ^ 2 < 2 ^ (2 * l) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left hltu (by norm_num)
  obtain ⟨K', D', hacc, hn', hh', hs'⟩ := prop_approx_acc_exact hA (t' := u ^ (16 * h - 16)) hJpow hI.thin hspan (m := m) (W := W)
    (by
      have h1 : 2 * (2 ^ (B + J) * Δ) + 1 ≤ 4 * (2 ^ (B + J) * 2 ^ l) := by
        have h2 : Δ ≤ 2 ^ l := (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_right (by norm_num) hΔ)
        have h3 := Nat.mul_le_mul_left (2 ^ (B + J)) h2
        have h4 : 1 ≤ 2 ^ (B + J) * 2 ^ l := Nat.one_le_iff_ne_zero.2 (by positivity)
        omega
      refine h1.trans (le_of_eq ?_)
      rw [hm, pow_add _ (B + J + l) 2, pow_add _ (B + J) l]
      ring)
    (by
      rw [← hnB]
      calc nB * 2 ^ J * (2 ^ B * 2 ^ (cΔ * l ^ 3)) < 2 ^ (2 * l) * 2 ^ J * (2 ^ B * 2 ^ (cΔ * l ^ 3)) :=
            Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right (hnB2.trans_lt hu2l) (Nat.two_pow_pos _))
              (by positivity)
        _ = 2 ^ (2 * l + J + B + cΔ * l ^ 3) := by rw [pow_add, pow_add, pow_add]; ring
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega))
    (by
      rw [← hnB]
      have m1 : MM (K.ht + B + J + 1) + 1 ≤ u := by
        unfold MM
        omega
      have m2 : nB * (60 * W + 3 * (J + m) + 100) + 40 * (nB * (J + 1)) + 40 * (W + 1) + 120 ≤ u ^ (16 * h - 17) := by
        have s1 : nB * (60 * W + 3 * (J + m) + 100) ≤ u ^ 2 * u := Nat.mul_le_mul hnB2 (by omega)
        have s2 : nB * (J + 1) ≤ u ^ 2 * u := Nat.mul_le_mul hnB2 (by omega)
        have s3 : u ^ 2 * u = u ^ 3 := by ring
        have s4 : 40 * (W + 1) + 120 ≤ u ^ 3 := (by omega : _ ≤ u).trans (Nat.le_self_pow (by norm_num) u)
        have s5 : 2000 * u ^ 3 ≤ u ^ (3 + 1) := pbig 3
        have s6 : u ^ (3 + 1) ≤ u ^ (16 * h - 17) := pow_le_pow hu1 (by omega)
        omega
      calc nB * (60 * W + 3 * (J + m) + 100) + MM (K.ht + B + J + 1) * u ^ (16 * h - 17) + 40 * (nB * (J + 1)) +
            40 * (W + 1) + 120 ≤ (MM (K.ht + B + J + 1) + 1) * u ^ (16 * h - 17) := by rw [add_mul, one_mul]; omega
        _ ≤ u * u ^ (16 * h - 17) := Nat.mul_le_mul_right _ m1
        _ = u ^ (16 * h - 16) := by rw [← pu]; congr 1; omega)
  rw [← hnB] at hn' hs'
  have h2l : ∀ k, 2 ^ (k * l) ≤ u ^ (2 * k) := by
    intro k
    rw [Nat.mul_comm k l, pow_mul, pow_mul]
    refine Nat.pow_le_pow_left ?_ k
    rw [hl, pow_two]
    exact (two_pow_lg_le_double (by omega)).trans (Nat.mul_le_mul_right _ (by omega))
  have hJm : 2 ^ (J + m + 1) ≤ u ^ (4400 * h) := by
    calc 2 ^ (J + m + 1) ≤ 2 ^ (2200 * h * l) := Nat.pow_le_pow_right (by norm_num) (by
          have e : 2200 * h * l = 2200 * (h * l) := by ring
          omega)
      _ ≤ u ^ (2 * (2200 * h)) := h2l _
      _ = _ := by congr 1; ring
  have hn6 : K'.nds ≤ u ^ (4400 * h + 6) := by
    calc K'.nds ≤ nB * 2 ^ (J + m + 1) := hn'
      _ ≤ u ^ 2 * u ^ (4400 * h) := Nat.mul_le_mul hnB2 hJm
      _ ≤ _ := by rw [← pow_add]; exact pow_le_pow hu1 (by omega)
  have hs6 : D'.size ≤ u ^ (4400 * h + 6) := by
    have p1 : nB * (2 ^ (J + m) * (8 * (K.ht + B + J + m + W) + xcst + 31)) ≤ u ^ (4400 * h + 4) := by
      calc _ ≤ u ^ 2 * (u ^ (4400 * h) * u) := Nat.mul_le_mul hnB2 (Nat.mul_le_mul
            ((Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)).trans hJm) (by omega))
        _ = u ^ (4400 * h + 3) := by rw [pow_add]; ring
        _ ≤ _ := pow_le_pow hu1 (by omega)
    have p2 : D.size ≤ u ^ (4400 * h + 4) := hI.size.trans (pow_le_pow hu1 (by omega))
    have p3 : xcst ≤ u ^ (4400 * h + 4) := (by omega : xcst ≤ u).trans (Nat.le_self_pow (by omega) u)
    have p4 := pbig (4400 * h + 4)
    have p5 : u ^ (4400 * h + 4 + 1) ≤ u ^ (4400 * h + 6) := pow_le_pow hu1 (by omega)
    omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = lg (max (u ^ (16 * h)) (u ^ (4400 * h + 6))) := ⟨_, rfl⟩
  have hY2 : 2200 * (h * l) ≤ Y := by
    rw [hY]
    refine le_trans ?_ (lg_mono (le_max_right _ _))
    refine le_trans ?_ (le_lg_pow (n := u) (k := 4400 * h + 6) (by omega))
    have e : (4400 * h + 6) * (l - 1) = 4400 * (h * (l - 1)) + 6 * (l - 1) := by ring
    rw [← hl, e]
    have : h * l ≤ h * (2 * (l - 1)) := Nat.mul_le_mul_left _ (by omega)
    have e' : h * (2 * (l - 1)) = 2 * (h * (l - 1)) := by ring
    omega
  refine ⟨K', 1, D', hacc, hn6, hs6, ?_, ?_⟩
  · rw [← hY, pow_two]
    calc K'.ht ≤ K.ht + B + J + m := hh'
      _ ≤ 9 * Y := by omega
      _ ≤ Y * Y := Nat.mul_le_mul_right _ (by omega)
  · rw [← hY]
    exact Nat.one_le_pow _ _ (by omega)

set_option maxHeartbeats 1000000 in
/-- **Paper: proof of Proposition prop:approx-acc, the first step**, to a scale at which everything is small, from an
approximate accelerator of size `v ^ a` (the data of `HasAccA θ E (16 * h) v (v ^ a)`). The constants keep every property
`Q` of the given ones that rescaling keeps. -/
theorem prop_approx_acc_first {h : ℕ} (hh : 17 ≤ h) {v a α U : ℕ} (hcut : CutAt θ (16 * h) v (2 * α)) (hα5 : 5 ≤ α)
    (haα : a + 1 ≤ α) (hcs : cst ≤ v) (hU : U ≤ v) (hbig : 1000 * (7000 * (h * α * lg v) ^ 3) ^ 3 ≤ v)
    {K : KT E[T;T⁻¹]} {B : ℕ} {D : Tree} (hD : IsAccA θ (16 * h) v (v ^ (16 * h - 16)) K B D)
    (hKn : K.nds ≤ v ^ a) (hDs : D.size ≤ v ^ a) (hKh : K.ht ≤ lg (max (v ^ (16 * h)) (v ^ a)) ^ 2)
    (hB : B ≤ lg (max (v ^ (16 * h)) (v ^ a)) ^ 3) {Q : E[T;T⁻¹] → Prop} (hQ : RescaleStable A Q)
    (hK : K.All Q) :
    ∃ (Δ cΔ b₀ : ℕ) (K' : KT E[T;T⁻¹]) (B' : ℕ) (D' : Tree),
      4 * (100000 * h ^ 3) ≤ cΔ ∧ InvA θ h (100000 * h ^ 3) U Δ cΔ b₀ (v ^ α) K' B' D' ∧ K'.All Q := by
  obtain ⟨cB, hcB⟩ : ∃ n, n = 100000 * h ^ 3 := ⟨_, rfl⟩
  rw [← hcB]
  obtain ⟨Δ, hΔ⟩ := KT.exists_bound (P := Span) exists_span (fun n m c hnm hc => hc.mono hnm) K
  have hv2000 : 2000 ≤ v := by
    rw [cst_def] at hcs
    omega
  have hv1 : 1 ≤ v := by omega
  have hl2 := lg_ge_two (show 4 ≤ v by omega)
  have hltv := lt_two_pow_lg v
  obtain ⟨l, hl⟩ : ∃ l, l = lg v := ⟨_, rfl⟩
  rw [← hl] at hl2 hltv hbig
  have hl1 : 1 ≤ l := by omega
  have hhα : 17 * α ≤ h * α := Nat.mul_le_mul_right _ hh
  obtain ⟨P, hP⟩ : ∃ P, P = h * α * l := ⟨_, rfl⟩
  rw [← hP] at hbig
  have hP1 : 17 * α * l ≤ P := hP ▸ Nat.mul_le_mul_right _ hhα
  have hVs : lg (max (v ^ (16 * h)) (v ^ a)) ≤ 16 * P := by
    have : max (v ^ (16 * h)) (v ^ a) ≤ v ^ (16 * h * α) := by
      apply max_le
      · exact pow_le_pow hv1 (Nat.le_mul_of_pos_right _ (by omega))
      · refine pow_le_pow hv1 ?_
        have : 1 * α ≤ 16 * h * α := Nat.mul_le_mul_right _ (by omega)
        omega
    have h16 : 16 * h * α = 16 * (h * α) := by ring
    refine (lg_mono this).trans ((lg_pow_le (by omega)).trans (le_of_eq ?_))
    rw [hP, ← hl]
    ring
  have hPpos : 1 ≤ P := by
    have : 17 * 1 * 1 ≤ 17 * α * l := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hl1
    omega
  have hP2 : P ≤ P ^ 2 := Nat.le_self_pow (by norm_num) P
  have hP3 : P ^ 2 ≤ P ^ 3 := Nat.pow_le_pow_right hPpos (by norm_num)
  have hB3 : B ≤ 4096 * P ^ 3 := by
    calc B ≤ (16 * P) ^ 3 := hB.trans (Nat.pow_le_pow_left hVs 3)
      _ = 4096 * P ^ 3 := by ring
  have hK3 : K.ht ≤ 256 * P ^ 3 := by
    calc K.ht ≤ (16 * P) ^ 2 := hKh.trans (Nat.pow_le_pow_left hVs 2)
      _ = 256 * P ^ 2 := by ring
      _ ≤ 256 * P ^ 3 := Nat.mul_le_mul_left _ hP3
  obtain ⟨J, hJ⟩ : ∃ J, J = (16 * h * α + 1) * l := ⟨_, rfl⟩
  have hJP : J ≤ 17 * P := by
    rw [hJ]
    have e : 17 * P = 17 * h * α * l := by rw [hP]; ring
    rw [e]
    refine Nat.mul_le_mul_right _ ?_
    have : 17 * h * α = 16 * h * α + h * α := by ring
    omega
  have hαP : α ≤ P := by
    have : α * 1 ≤ 17 * α * l := Nat.mul_le_mul (by omega) hl1
    omega
  have hJ2 : (2 * α + 2) * (J + 1) ≤ 54 * P ^ 3 := by
    calc (2 * α + 2) * (J + 1) ≤ 3 * P * (18 * P) := Nat.mul_le_mul (by omega) (by omega)
      _ = 54 * P ^ 2 := by ring
      _ ≤ 54 * P ^ 3 := Nat.mul_le_mul_left _ hP3
  obtain ⟨X, hX⟩ : ∃ X, X = B + (2 * α + 2) * (J + 1) + K.ht + K.ht + 10 := ⟨_, rfl⟩
  have hX7 : X ≤ 7000 * P ^ 3 := by
    have : 1 ≤ P ^ 3 := Nat.one_le_pow _ _ hPpos
    omega
  have hXv : 1000 * X ^ 3 ≤ v := (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX7 3)).trans hbig
  have hXv' : X ≤ v := by
    have : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
    omega
  have hK4 : K.nds * (4 * α + 5) ≤ v ^ α := by
    calc K.nds * (4 * α + 5) ≤ v ^ a * v := Nat.mul_le_mul hKn (by
          have : (2 * α + 2) * 1 ≤ (2 * α + 2) * (J + 1) := Nat.mul_le_mul_left _ (by omega)
          have h3 : 1000 * X ≤ 1000 * X ^ 3 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) X)
          omega)
      _ = v ^ (a + 1) := (pow_succ _ _).symm
      _ ≤ v ^ α := pow_le_pow hv1 haα
  have hαh : α ≤ h * α := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨K', D', hacc', hs', hn', hh', hsp, hth⟩ := prop_approx_acc_next hh hα5 hcut hcs hD
    (hK4.trans (pow_le_pow hv1 hαh)) (hDs.trans (pow_le_pow hv1 (by omega))) (M' := 2 ^ Δ)
    (hΔ.imp fun c hc => hc.mono Nat.lt_two_pow_self.le) (Nat.two_pow_pos _) ((rescaleStable_thin Δ).and hQ)
    ((hΔ.imp fun c hc => hc.thin).and hK) (J := J) (by
      rw [hJ, Nat.mul_comm (16 * h * α + 1) l, pow_mul]
      exact Nat.pow_lt_pow_left hltv (by omega)) hX.ge hXv
  have hlgα : α * l ≤ 2 * lg (v ^ α) := by
    have h1 := le_lg_pow (n := v) (k := α) (by omega)
    have h2 : α * (l - 1) = α * l - α := by rw [Nat.mul_sub, Nat.mul_one]
    have h3 : α * 2 ≤ α * l := Nat.mul_le_mul_left _ hl2
    rw [← hl] at h1
    omega
  have hP8 : P ^ 3 ≤ 8 * h ^ 3 * lg (v ^ α) ^ 3 := by
    calc P ^ 3 = h ^ 3 * (α * l) ^ 3 := by rw [hP]; ring
      _ ≤ h ^ 3 * (2 * lg (v ^ α)) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlgα 3)
      _ = 8 * h ^ 3 * lg (v ^ α) ^ 3 := by ring
  have hcBP : 12500 * P ^ 3 ≤ cB * lg (v ^ α) ^ 3 := by
    calc 12500 * P ^ 3 ≤ 12500 * (8 * h ^ 3 * lg (v ^ α) ^ 3) := Nat.mul_le_mul_left _ hP8
      _ = cB * lg (v ^ α) ^ 3 := by rw [hcB]; ring
  have hvα : v ≤ v ^ α := Nat.le_self_pow (by omega) v
  have hJ3 : (2 * α + 1) * J ≤ (2 * α + 2) * (J + 1) := Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨cΔ, hcΔ⟩ : ∃ c, c = 4 * cB + (3 * X + Δ) * (2 * α + 1) := ⟨_, rfl⟩
  refine ⟨Δ, cΔ, B + (2 * α + 1) * J + (K.ht + (2 * α + 1)), K', B + (2 * α + 1) * J, D', by omega,
    ⟨hacc'.mono ?_ le_rfl, hU.trans hvα, hn'.trans hK4, hs', by omega, by omega, by omega, by omega, ?_,
      hth.imp fun _ hc => hc.1⟩, hth.imp fun _ hc => hc.2⟩
  · rw [← pow_mul]
    refine pow_le_pow hv1 ?_
    have : α * (16 * h - 16) = 16 * (h * α) - 16 * α := by
      rw [Nat.mul_sub]
      congr 1
      · ring
      · ring
    have e16 : 16 * h * α = 16 * (h * α) := by ring
    omega
  · refine hsp.imp fun c hc => hc.mono ?_
    rw [← pow_add, ← pow_mul]
    refine Nat.pow_le_pow_right (by norm_num) (le_trans ?_ (Nat.le_mul_of_pos_right _ ?_))
    · omega
    · have : 1 ≤ lg (v ^ α) := by unfold lg; omega
      exact Nat.pow_pos this

set_option maxHeartbeats 1000000 in
/-- **Paper: proof of Proposition prop:approx-acc, all scales.** From an approximate accelerator of size `v ^ a` at a
large scale `v` there are approximate programs with the invariant at arbitrarily large scales, for numbers Δ, cΔ and b₀
that do not depend on the scale. Their constants keep every property `Q` of the given ones that rescaling keeps. -/
theorem prop_approx_acc_scales {h : ℕ} (hh : 17 ≤ h) {C₀ v₀ : ℕ} (hcut : CutHyp θ (16 * h) C₀ v₀) :
    ∃ C v₁ : ℕ, ∀ v, v₁ ≤ v → ∀ a, lg v ^ (C * a) ≤ v → ∀ (E : Type) [CommRing E] [Algebra A E]
      {Q : E[T;T⁻¹] → Prop}, RescaleStable A Q → ∀ (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree),
      IsAccA θ (16 * h) v (v ^ (16 * h - 16)) K B D → K.nds ≤ v ^ a → D.size ≤ v ^ a →
      K.ht ≤ lg (max (v ^ (16 * h)) (v ^ a)) ^ 2 → B ≤ lg (max (v ^ (16 * h)) (v ^ a)) ^ 3 → K.All Q →
      ∃ U Δ cΔ b₀ : ℕ, 4 * (100000 * h ^ 3) ≤ cΔ ∧ ∀ n, ∃ (u : ℕ) (K' : KT E[T;T⁻¹]) (B' : ℕ) (D' : Tree),
        n ≤ u ∧ InvA θ h (100000 * h ^ 3) U Δ cΔ b₀ u K' B' D' ∧ K'.All Q ∧
        IsAccA θ (16 * h) u (u ^ (16 * h - 17)) K' B' D' := by
  obtain ⟨cB, hcB⟩ : ∃ n, n = 100000 * h ^ 3 := ⟨_, rfl⟩
  obtain ⟨n1, hn1⟩ := poly_lg 1 (C₀ * 10)
  obtain ⟨n2, hn2⟩ := poly_lg (1000 * (3 * (2 * cB)) ^ 3) 9
  obtain ⟨cs, hcs⟩ : ∃ n, n = cst := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = v₀ + n1 + n2 + cs + 4 := ⟨_, rfl⟩
  have hh3 : h ≤ h ^ 3 := Nat.le_self_pow (by norm_num) h
  have hL : LargeScale h (2 * cB) U := ⟨by omega, by rw [← hcs]; omega, fun u hu => hn2 u (by omega)⟩
  obtain ⟨C, hCdef⟩ : ∃ n, n = 2 * C₀ + 40 := ⟨_, rfl⟩
  obtain ⟨n3, hn3⟩ := poly_lg 1 (C * 10)
  obtain ⟨cc, hcc⟩ : ∃ n, n = 1000 * (7000 * h ^ 3) ^ 3 := ⟨_, rfl⟩
  refine ⟨2 * C, U + n3 + 2 ^ cc, fun v hv a ha E _ _ Q hQ K B D hD hKn hDs hKh hB hK => ?_⟩
  have hpc : 1 ≤ 2 ^ cc := Nat.one_le_two_pow
  have hUv : U ≤ v := by omega
  have hl2 := lg_ge_two (show 4 ≤ v by omega)
  have hlcc : cc ≤ lg v := (Nat.le_succ _).trans (le_lg_of_two_pow_le (by omega))
  have hn3v := hn3 v (by omega)
  obtain ⟨l, hl⟩ : ∃ l, l = lg v := ⟨_, rfl⟩
  rw [← hl] at ha hl2 hlcc hn3v
  obtain ⟨α, hα⟩ : ∃ α, α = a + 5 := ⟨_, rfl⟩
  have hlog : l ^ (C * α) ≤ v := by
    refine (Nat.pow_le_pow_iff_left (show 2 ≠ 0 by norm_num)).1 ?_
    calc (l ^ (C * α)) ^ 2 = l ^ (2 * C * a) * (1 * l ^ (C * 10)) := by
          rw [one_mul, ← pow_mul, ← pow_add, hα]; congr 1; ring
      _ ≤ v * v := Nat.mul_le_mul ha hn3v
      _ = v ^ 2 := (pow_two v).symm
  have hl1 : 1 ≤ l := by omega
  have hαl : α ≤ l ^ α := (Nat.lt_two_pow_self (n := α)).le.trans (Nat.pow_le_pow_left hl2 α)
  have hbig : 1000 * (7000 * (h * α * l) ^ 3) ^ 3 ≤ v := by
    have s1 : cc ≤ l ^ α := hlcc.trans (Nat.le_self_pow (by omega) l)
    have s2 : α ^ 9 ≤ l ^ (9 * α) := by
      rw [Nat.mul_comm, pow_mul]
      exact Nat.pow_le_pow_left hαl 9
    have s3 : l ^ 9 ≤ l ^ (9 * α) := Nat.pow_le_pow_right hl1 (by omega)
    calc 1000 * (7000 * (h * α * l) ^ 3) ^ 3 = cc * (α ^ 9 * l ^ 9) := by rw [hcc]; ring
      _ ≤ l ^ α * (l ^ (9 * α) * l ^ (9 * α)) := Nat.mul_le_mul s1 (Nat.mul_le_mul s2 s3)
      _ = l ^ (19 * α) := by rw [← pow_add, ← pow_add]; congr 1; ring
      _ ≤ l ^ (C * α) := Nat.pow_le_pow_right hl1 (Nat.mul_le_mul_right _ (by omega))
      _ ≤ v := hlog
  have hcutv : CutAt θ (16 * h) v (2 * α) := hcut.at (by omega) (by
    rw [← hl]
    refine (Nat.pow_le_pow_right hl1 ?_).trans hlog
    have : C * α = C₀ * (2 * α) + 40 * α := by rw [hCdef]; ring
    omega)
  obtain ⟨Δ, cΔ, b₀, K, B, D, hcΔ, hI, hK⟩ := prop_approx_acc_first (U := U) hh hcutv (by omega) (by omega)
    (hL.cst_le.trans hUv) hUv (by rw [← hl]; exact hbig) hD hKn hDs hKh hB hQ hK
  subst hcB
  refine ⟨U, Δ, cΔ, b₀, hcΔ, fun n => ?_⟩
  exact prop_approx_acc_all_scales hh (fun u hu => hcut.at (by omega) (by simpa using hn1 u (by omega)))
    hL (by omega) hcΔ hQ hI hK n

set_option maxHeartbeats 1000000 in
/-- **Paper: Theorem thm:noacc.** "There are C and v₁ such that for all integers a ≥ 0 and v ≥ v₁ with (lg v)^(Ca) ≤ v no
nonzero commutative A-algebra has an accelerator of size v^a at scale v." Over a finite field E an accelerator is an
approximate one whose constants are constant Laurent polynomials; the approximate scale-up keeps them constant, so at a
scale that is large against E its ε⁰ part is an accelerator with the diagonal of `thm_noacc_diagonal`. -/
theorem thm_noacc {h : ℕ} (hh : 17 ≤ h) [Algebra.FiniteType ℤ A] {C₀ v₀ : ℕ} (hcut : CutHyp θ (16 * h) C₀ v₀) :
    ∃ C v₁ : ℕ, ∀ v, v₁ ≤ v → ∀ a, lg v ^ (C * a) ≤ v → ∀ (R : Type) [CommRing R] [Nontrivial R] [Algebra A R],
      ¬ HasAcc θ R (16 * h) v (v ^ a) := by
  obtain ⟨C, v₁, hscales⟩ := prop_approx_acc_scales hh hcut
  obtain ⟨n9, hn9⟩ := poly_lg (1000 * (3 * (100000 * h ^ 3)) ^ 3) 9
  refine ⟨C, v₁, fun v hv a ha R _ _ _ hacc => ?_⟩
  obtain ⟨K, B, D, hD, hKn, hDs, hKh, hB⟩ := hacc
  obtain ⟨E, _, _, _, K₁, hD₁, hn₁, hh₁⟩ := thm_noacc_finite_field hD
  obtain ⟨M, red, hM, hred⟩ := thm_noacc_periodic E
  -- the constants as constant Laurent polynomials
  obtain ⟨_, _, _, _, -, hall⟩ := hscales v hv a ha E rescaleStable_laurentConst
    (K₁.map (laurentConst A E)) B D (hD₁.map _).isAccA (by rw [KT.nds_map]; exact hn₁.trans_le hKn) hDs
    (by rw [KT.ht_map]; exact hh₁.trans_le hKh) hB (K₁.all_true.map fun c _ => ⟨c, rfl⟩)
  obtain ⟨u, K₂, B', D', hu, hI, hK₂, -⟩ := hall (2 ^ (M + 2000 * h) + cst + n9)
  -- at the large scale, the ε⁰ part is an accelerator over E
  obtain ⟨K', rfl⟩ := KT.exists_map_of_all hK₂
  have hacc : IsAccT θ (16 * h) u (u ^ (16 * h - 16)) K' B' D' := hI.acc.isAccT_of_map
  have hn' : K'.nds ≤ u := by simpa only [KT.nds_map] using hI.nds
  have a1 : K'.ht ≤ 100000 * h ^ 3 * lg u ^ 3 := by simpa only [KT.ht_map] using hI.ht
  have a2 := hI.B_le
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = cst := ⟨_, rfl⟩
  rw [← hcs] at hu
  have hp : 1 ≤ 2 ^ (M + 2000 * h) := Nat.one_le_two_pow
  have hu1 : 1 ≤ u := by omega
  have hl : M + 2000 * h + 1 ≤ lg u := le_lg_of_two_pow_le (by omega)
  have hlt := lt_two_pow_lg u
  have hsmall := hn9 u (by omega)
  obtain ⟨L, hL⟩ : ∃ L, L = lg u := ⟨_, rfl⟩
  rw [← hL] at hl hlt hsmall a1 a2
  refine thm_noacc_diagonal hh hacc (by omega) hn' hI.size hM hred (J := 16 * h * L)
    (X := K'.ht + max B' M + 16 * h * L + 10) ?_ (by omega) (by omega) ?_
  · rw [Nat.mul_comm (16 * h) L, pow_mul]
    calc u ^ (16 * h - 15) ≤ u ^ (16 * h) := pow_le_pow hu1 (by omega)
      _ < (2 ^ L) ^ (16 * h) := Nat.pow_lt_pow_left hlt (by omega)
  · refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (m := 3 * (100000 * h ^ 3) * L ^ 3) ?_ 3))
      (le_trans (le_of_eq ?_) hsmall)
    · have h1 : 17 * (h * L) ≤ 100000 * (h ^ 3 * L ^ 3) := Nat.mul_le_mul (by norm_num)
        (Nat.mul_le_mul (Nat.le_self_pow (by norm_num) h) (Nat.le_self_pow (by norm_num) L))
      have h2 : L ≤ h * L := Nat.le_mul_of_pos_left _ (by omega)
      have e1 : 16 * h * L = 16 * (h * L) := by ring
      have e2 : 3 * (100000 * h ^ 3) * L ^ 3 = 3 * (100000 * (h ^ 3 * L ^ 3)) := by ring
      have e3 : 100000 * h ^ 3 * L ^ 3 = 100000 * (h ^ 3 * L ^ 3) := by ring
      omega
    · ring

/-- **Paper: Proposition prop:approx-acc.** "Theorem thm:noacc holds for approximate accelerators." An approximate
accelerator has constants in R[ε,ε⁻¹] and values in pv(z) + ε R[ε]; here R is any nonzero commutative A-algebra. -/
theorem prop_approx_acc [Algebra.FiniteType ℤ A] {h : ℕ} (hh : 17 ≤ h)
    {C₀ v₀ : ℕ} (hcut : CutHyp θ (16 * h) C₀ v₀) :
    ∃ C v₁ : ℕ, ∀ v, v₁ ≤ v → ∀ a, lg v ^ (C * a) ≤ v → ∀ (R : Type) [CommRing R] [Nontrivial R] [Algebra A R],
      ¬ HasAccA θ R (16 * h) v (v ^ a) := by
  obtain ⟨Ce, v₂, hexact⟩ := thm_noacc hh hcut
  obtain ⟨C, v₁, hscales⟩ := prop_approx_acc_scales hh hcut
  refine ⟨C, v₁, fun v hv a ha E _ _ _ hacc => ?_⟩
  obtain ⟨K, B, D, hD, hKn, hDs, hKh, hB⟩ := hacc
  obtain ⟨U, Δ, cΔ, b₀, -, hall⟩ := hscales v hv a ha E (Q := fun _ => True) (fun _ _ _ => trivial)
    K B D hD hKn hDs hKh hB K.all_true
  -- a scale that is large against Δ, cΔ and b₀
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, a₀ = 4400 * h + 6 := ⟨_, rfl⟩
  obtain ⟨n4, hn4⟩ := poly_lg 1 (Ce * a₀)
  obtain ⟨n5, hn5⟩ := poly_lg (1000 * (cΔ + 20000 * h + xcst + 1000) ^ 3) 9
  obtain ⟨u, K', B', D', hn, hI', -, hA⟩ := hall (v₂ + n4 + n5 + 2 ^ (Δ + b₀) + 2000)
  have hp2 : 1 ≤ 2 ^ (Δ + b₀) := Nat.one_le_two_pow
  have hlu : Δ + b₀ ≤ lg u := (Nat.le_succ _).trans (le_lg_of_two_pow_le (by omega))
  have hex := prop_approx_acc_hasAcc (hI := hI') hh hA (by omega) (by omega) (by omega)
    (le_trans (le_of_eq (by ring)) (hn5 u (by omega)))
  rw [← ha₀] at hex
  refine hexact u (by omega) a₀ ?_ E hex
  simpa using hn4 u (by omega)

/-- Proposition prop:approx-acc for "A and H of Theorem thm:cut", in the contracting case. -/
theorem prop_approx_acc_setting {K : Type} [Field K] (hK : Contracting K) :
    ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A) (θ : List Bool → A) (h C₀ v₀ : ℕ),
      Generates θ ∧ 17 ≤ h ∧ CutHyp θ (16 * h) C₀ v₀ ∧
      ∃ C v₁ : ℕ, ∀ v, v₁ ≤ v → ∀ a, lg v ^ (C * a) ≤ v → ∀ (R : Type) [CommRing R] [Nontrivial R] [Algebra A R],
        ¬ HasAccA θ R (16 * h) v (v ^ a) := by
  obtain ⟨A, hA, θ, h, C₀, v₀, hθ, hh, hcut⟩ := exists_setting hK
  exact ⟨A, hA, θ, h, C₀, v₀, hθ, hh, hcut, prop_approx_acc hh hcut⟩

/-- The contracting case for approximating circuits of a family that is complete for grid sums. -/
theorem contracting_approx_complete {K : Type} [Field K] (hK : Contracting K)
    {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ} (hG : Nc.GridComplete K G κ) :
    ∃ C M₁ : ℕ, ∀ M ≥ M₁, ∀ a : ℕ, lg M ^ (C * a) ≤ M → ¬ Nc.Approximates (G M) (M ^ a) := by
  obtain ⟨A, hA, θ, h, C₀, v₀, hθ, hh, -, C₂, v₂, hno⟩ := prop_approx_acc_setting hK
  obtain ⟨B₀, C₁, v₁, hB₀, hacc⟩ := lem_circuit_approx hθ.1 (H := 16 * h) (by omega) κ
  obtain ⟨C, M₁, hscale⟩ := exists_scale B₀ ((C₂ + 1) * C₁) (v₁ + v₂ + 4) hB₀
  refine ⟨C, M₁, fun M hM a ha happ => ?_⟩
  obtain ⟨v, hv, hvM, hsize, hlog⟩ := hscale M hM a ha
  have hl1 : 1 ≤ lg v := Nat.succ_pos _
  refine hno v (by omega) (C₁ * (2 * B₀ * a + 1)) (le_trans (Nat.pow_le_pow_right hl1 ?_) hlog) K
    (hacc K G hG v (by omega) (2 * B₀ * a) (le_trans (Nat.pow_le_pow_right hl1 ?_) hlog) M hvM
      (let ⟨p, hp, hf⟩ := happ; ⟨p, hp.mono hsize, hf⟩))
  · rw [← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
  · exact Nat.mul_le_mul (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) (Nat.le_succ _)

end Paper
