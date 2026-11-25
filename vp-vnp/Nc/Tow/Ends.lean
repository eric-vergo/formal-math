/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Flow

/-!
# The tower plan: holders of units
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T}

/-- The nodes that hold the units of a channel. -/
noncomputable def hN (ν : NM R FL (ch := ch)) : Sym2 (Nd T) :=
  s(partM R ch FL ν.1 ((kindM R ch FL ν.1).c ν.2), partM R ch FL ν.1 ((kindM R ch FL ν.1).d ν.2))

/-- The nodes that hold an initial unit. -/
def hB (ch : Fin AA ↪ T.X 0) (a c : Fin AA) : Sym2 (Nd T) := s(nd T 0 (Nat.zero_le _) (ch a), nd T 0 (Nat.zero_le _) (ch c))

/-- The nodes that hold the units with a target. -/
noncomputable def hT (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) : Tg T m AA → Sym2 (Nd T)
  | .done => s(none, none)
  | .edge j e => s(nd T j (Nat.le_of_lt_succ j.2) (T.e0 e), nd T j (Nat.le_of_lt_succ j.2) (T.e1 e))
  | .nxt x => s(tri T R ch x 0, tri T R ch x 2)
  | .seg j i ω q => q.map fun f => nd T (j + 1) j.2 (atv j.2 i ω f)

theorem edgeO_hold {c c' γ : T.X 0} {s : ℕ} (hs : s < R.pl c c' γ) :
    (edgeO T ((R.path c c' γ)[s]?) : Tg T m AA) ≠ .done ∧
    hT R ch (edgeO T ((R.path c c' γ)[s]?) : Tg T m AA) =
      s(nd T 0 (Nat.zero_le _) (R.pn c c' γ s), nd T 0 (Nat.zero_le _) (R.pn c c' γ (s + 1))) := by
  obtain ⟨e, h1, h2, -⟩ := R.exists_edge c c' γ hs
  rw [h1]
  refine ⟨by simp [edgeO], ?_⟩
  have := congrArg (Sym2.map (nd T 0 (Nat.zero_le _))) h2
  simp only [Sym2.map_mk] at this
  exact this

/-- Initial units. -/
theorem hB_eq {a c : Fin AA} {k : ℕ} (hd : tgB T R ch a c k ≠ .done) : hB ch a c = hT R ch (tgB T R ch a c k) := by
  unfold tgB at hd ⊢
  by_cases hac : a = c
  · rw [ite_eq_left hac] at hd
    exact absurd rfl hd
  · rw [ite_eq_right hac] at hd ⊢
    have hne : ch a ≠ ch c := fun hh => hac (ch.injective hh)
    have hpos := R.pl_pos hne (gam T ch a k)
    have hle := (R.pl_le (ch a) (ch c) (gam T ch a k)).trans (R.length_path _ _ _)
    by_cases hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (gam T ch a k)
    · rw [dite_eq_left hs]
      rfl
    · rw [dite_eq_right hs]
      have h1 : R.pl (ch a) (ch c) (gam T ch a k) = 1 := by
        by_contra h1
        exact hs ⟨by omega, by omega⟩
      rw [(edgeO_hold (ch := ch) (AA := AA) (m := m) hpos).2]
      have h2 := R.pn_pl (ch a) (ch c) (gam T ch a k)
      rw [h1] at h2
      rw [h2]
      rfl

theorem seg_hold {j : ℕ} (hj : j < J) (i : Fin h) (c : T.X j) :
    (s(T.co i (hst T i c), T.co i c) : Sym2 T.Fl).map (fun f => nd T (j + 1) hj (atv hj i (T.πV (T.vx i c)) f)) =
      s(nd T (j + 1) hj (hst T i c), nd T (j + 1) hj (T.π c)) := by
  rw [Sym2.map_mk]
  have h1 : atv hj i (T.πV (T.vx i c)) (T.co i (hst T i c)) = hst T i c := by
    rw [← T.host_vx hj i (T.vx i c)]
    exact atv_eq hj i _
  have h2 : atv hj i (T.πV (T.vx i c)) (T.co i c) = T.π c := by
    rw [← T.π_vx hj i c, ← T.π_co hj i c]
    exact atv_eq hj i _
  simp only [h1, h2]

/-- Units of channels. -/
theorem hN_eq (ν : NM R FL (ch := ch)) (hd : tgM R ch FL ν.1 ν.2 ≠ .done) : hN ν = hT R ch (tgM R ch FL ν.1 ν.2) := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · revert hd
    revert ν
    intro (ν : Bool) hd
    have e0 : hN (⟨.inl ⟨x, hx⟩, ν⟩ : NM R FL (ch := ch)) =
        if ν then s(tri T R ch x 1, tri T R ch x 2) else s(tri T R ch x 0, tri T R ch x 1) := by
      cases ν <;> rfl
    rw [e0]
    change tgR T R ch x ν ≠ .done at hd
    change _ = hT R ch (tgR T R ch x ν)
    rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
    · obtain ⟨hac, hs⟩ := hx
      have hle := (R.pl_le (ch a) (ch c) γ).trans (R.length_path _ _ _)
      rcases tgR_start_cases (R := R) (ch := ch) a c γ s ν with
        ⟨_, rfl, ht⟩ | ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, hlast, rfl⟩, ht⟩
      · rw [ht]; rfl
      · rw [ht, (edgeO_hold (ch := ch) (AA := AA) (m := m) (by omega)).2]; rfl
      · rw [ht, (edgeO_hold (ch := ch) (AA := AA) (m := m) hs).2]
        have hlen : R.pl (ch a) (ch c) γ = s.1 + 1 + 1 := by omega
        have hend := R.pn_pl (ch a) (ch c) γ
        rw [hlen] at hend
        rw [hend]
        rfl
    · exact absurd rfl hd
    · rcases tgR_mid_cases (R := R) (ch := ch) j e s ν with ht | ⟨rfl, rfl, ht⟩ | ⟨rfl, rfl, ht⟩ |
        ⟨rfl, rfl, ht⟩ | ⟨rfl, rfl, _, ht⟩ | ⟨⟨rfl, hh⟩ | rfl, rfl, ht⟩ | ⟨rfl, rfl, _, ht⟩
      · exact (hd ht).elim
      all_goals rw [ht]
      · exact (seg_hold j.2 (T.ty e) (T.e0 e)).symm
      · exact (congrArg (Sym2.map (nd T (j + 1) j.2)) (T.π_ends j.2 e)).symm
      · exact Sym2.eq_swap.trans (seg_hold j.2 (T.ty e) (T.e1 e)).symm
      · rfl
      · change s(nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e)), _) = s(nd T (j + 1) j.2 (T.π (T.e0 e)), _)
        rw [hh]; rfl
      · rfl
      · rfl
    · exact absurd rfl hd
  · change s(nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).c ν))),
      nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).d ν)))) = _
    set p := (T.nr l.1.2 l.2.1).symm (l.2.2.1, FL.cn l.2.2.2 ν) with hp
    have hp2 : T.nr l.1.2 l.2.1 p = (l.2.2.1, FL.cn l.2.2.2 ν) := by rw [hp, Equiv.apply_symm_apply]
    have h0 := T.nr_vx0 l.1.2 l.2.1 p
    have h1 := T.nr_vx1 l.1.2 l.2.1 p
    have h2 := T.nr_co l.1.2 l.2.1 p
    rw [hp2] at h0 h1 h2
    have h3 := (FL.ends l.2.2.2 ν).trans h2.symm
    have h4 := congrArg (Sym2.map fun f => nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 f)) h3
    simp only [Sym2.map_mk] at h4
    rw [h4]
    have e1 : atv l.1.2 l.2.1 l.2.2.1 (T.co l.2.1 (T.e0 p.1)) = T.e0 p.1 := by
      have := atv_eq l.1.2 l.2.1 (T.e0 p.1)
      rwa [h0] at this
    have e2 : atv l.1.2 l.2.1 l.2.2.1 (T.co l.2.1 (T.e1 p.1)) = T.e1 p.1 := by
      have := atv_eq l.1.2 l.2.1 (T.e1 p.1)
      rwa [h1] at this
    rw [e1, e2]
    rfl

end Nc.Tow
