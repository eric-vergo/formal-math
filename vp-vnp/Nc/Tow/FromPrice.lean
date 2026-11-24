/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Relay
import Nc.Price.Norm

/-!
# The laws at the vertices of a tower, from prices

`VLaws`: the laws for one local structure (chambers Fl, near pairs Nr), the same for all towers. They exist by
Paper.thm_laws, see Paper.exists_laws.
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Nc.Price

/-- The laws at the vertices of a tower with the given local structure. -/
def VLaws.toFlag {F : Type} [CommRing F] {Fl Nr : Type} [Fintype Fl] [DecidableEq Fl] [Fintype Nr]
    [DecidableEq Nr] {cN dN : Nr → Fl} {r b : ℕ} (VL : VLaws F cN dN r b) {h D J : ℕ}
    (T : Tower h b D J r) (φ : T.Fl ≃ Fl) (ψ : T.Nr ≃ Nr)
    (hφ : ∀ ν, s(φ (T.cN ν), φ (T.dN ν)) = s(cN (ψ ν), dN (ψ ν))) : FlagLaws F T :=
  { VL with
    ro d := (VL.ro d).trans φ.symm
    cn d := (VL.cn d).trans ψ.symm
    ends d ν := by
      have h1 := hφ (ψ.symm (VL.cn d ν))
      rw [ψ.apply_symm_apply, ← VL.ends d ν] at h1
      have h2 := congrArg (Sym2.map φ.symm) h1
      simpa [Sym2.map_mk] using h2.symm
    L1 n t ht := by
      have hN : vN2 b (fun q : Sym2 Fl => n (Sym2.map φ.symm q)) = T.NN2 n := by
        unfold Tower.NN2 vN2
        congr 1
        let e : Sym2 Fl ≃ Sym2 T.Fl := ⟨Sym2.map φ.symm, Sym2.map φ,
          fun q => by rw [Sym2.map_map]; simp, fun q => by rw [Sym2.map_map]; simp⟩
        refine Fintype.sum_equiv e _ _ fun q => ?_
        have hd : (Sym2.map φ.symm q).IsDiag ↔ q.IsDiag :=
          Sym2.isDiag_map φ.symm.injective
        show (if q.IsDiag then 0 else _) = if (Sym2.map φ.symm q).IsDiag then 0 else _
        simp only [hd]
        rfl
      obtain ⟨d, hd⟩ := VL.L1 (fun q => n (Sym2.map φ.symm q)) t (by rw [hN]; exact ht)
      refine ⟨d, fun q hq => ?_⟩
      have h1 := hd (Sym2.map φ q) (fun h => hq ((Sym2.isDiag_map φ.injective).1 h))
      have h2 : Sym2.map φ.symm (Sym2.map φ q) = q := by
        rw [Sym2.map_map]
        simp
      rw [h2] at h1
      refine h1.trans (Nat.mul_le_mul_right _ (Finset.card_le_card fun e he => ?_))
      rw [Finset.mem_filter] at he ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h3 := congrArg (Sym2.map φ.symm) he.2
      rw [h2] at h3
      simpa [Sym2.map_mk] using h3 }

theorem out_mk {Fl : Type} (q : Sym2 Fl) : s(q.out.1, q.out.2) = q := Quot.out_eq q

/-- Sums over ordered and over unordered pairs. -/
theorem sum_off {Fl : Type} [Fintype Fl] [DecidableEq Fl] (f : Sym2 Fl → ℝ) :
    ∑ p, ∑ q, (if p = q then 0 else f s(p, q)) = 2 * ∑ q : Sym2 Fl, if q.IsDiag then 0 else f q := by
  rw [← Fintype.sum_prod_type' (f := fun p q => if p = q then (0 : ℝ) else f s(p, q)),
    ← Finset.sum_fiberwise (s := Finset.univ) (g := fun x : Fl × Fl => s(x.1, x.2)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  induction q with
  | h a b =>
    by_cases hab : a = b
    · subst hab
      rw [if_pos (Sym2.mk_isDiag_iff.2 rfl), mul_zero]
      refine Finset.sum_eq_zero fun x hx => ?_
      have := (Finset.mem_filter.1 hx).2
      rw [Sym2.eq_iff] at this
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [if_pos (h1.trans h2.symm)]
    · rw [if_neg (fun h => hab (Sym2.mk_isDiag_iff.1 h))]
      have hf : (Finset.univ.filter fun x : Fl × Fl => s(x.1, x.2) = s(a, b)) = {(a, b), (b, a)} := by
        ext ⟨x, y⟩
        simp
      rw [hf, Finset.sum_pair (fun h => hab (Prod.ext_iff.1 h).1), if_neg hab, if_neg (Ne.symm hab),
        Sym2.eq_swap (a := b)]
      ring

end Nc.Tow
