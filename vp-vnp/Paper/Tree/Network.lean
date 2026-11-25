/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Tower
import Paper.Laws

/-!
# Network values and the thin-tree specification
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset Nc Nc.G Nc.Tow Nc.Vp Unc
open Nc.Tower (U x NN ee JJ tower SL2 gen XX npair npair_sym)
open NS1 (lg)

/-- The units of a network with n a c units from a to c. -/
abbrev NetUnit {AA : ℕ} (n : Fin AA → Fin AA → ℕ) := Σ a c : Fin AA, Fin (n a c)

/-- A table of the node a, with values in R, of the contents of the units at a. -/
abbrev NodeTable (R : Type) {AA : ℕ} (n : Fin AA → Fin AA → ℕ) (ℓ : ℕ) (a : Fin AA) :=
  ({u : NetUnit n // u.1 = a ∨ u.2.1 = a} → Fin ℓ → Bool) → R

/-- The value of a network: the sum over all contents of the units of the product of the tables. -/
def netValue {R : Type} [CommRing R] {AA ℓ : ℕ} {n : Fin AA → Fin AA → ℕ} (tab : ∀ a, NodeTable R n ℓ a) : R :=
  ∑ w : NetUnit n → Fin ℓ → Bool, ∏ a, tab a fun u => w u.1

/-- A law over A is a law over every A-algebra. -/
noncomputable def lawMap {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (L : G.Law A) : G.Law R :=
  { L with
    tab p i s y := f (L.tab p i s y)
    law X := @laws_over_algebras A _ L R _ f.toAlgebra X }

/-- The laws at the vertices of a tower, over an A-algebra. -/
noncomputable def flagMap {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {h b D J r : ℕ} {T : Tower h b D J r}
    (FL : FlagLaws A T) : FlagLaws R T :=
  { FL with L := fun d => lawMap f (FL.L d) }

theorem TCst_map {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {h b D J r : ℕ} {T : Tower h b D J r}
    {FL : FlagLaws A T} {laws : List (G.Law A)} {c p q : ℕ} {ρ : ℝ} (hC : TCst FL laws c ρ p q) :
    TCst (flagMap f FL) (laws.map (lawMap f)) c ρ p q where
  r_pos := hC.r_pos
  b_pos := hC.b_pos
  h_pos := hC.h_pos
  bD := hC.bD
  ρ_pos := hC.ρ_pos
  ρ_lt := hC.ρ_lt
  gain := hC.gain
  two := hC.two
  near := hC.near
  h_le := hC.h_le
  b_le := hC.b_le
  r_le := hC.r_le
  nr_le := hC.nr_le
  g_le := hC.g_le
  di_le := hC.di_le
  fl_le := hC.fl_le
  sl_le := hC.sl_le
  bot := hC.bot
  bot_pos := hC.bot_pos
  cst := hC.cst
  inv := hC.inv
  pq := hC.pq
  pow := hC.pow
  mem d := List.mem_map.2 ⟨_, hC.mem d, rfl⟩
  len L hL := by
    obtain ⟨L', h1, rfl⟩ := List.mem_map.1 hL
    exact ⟨⟨(hC.len L' h1).1.len_le⟩, (hC.len L' h1).2⟩

section Start

variable {R : Type} [CommRing R] {AA A' E N U1 ℓ : ℕ} {S : Sys R (AA + A') E} {n : Fin AA → Fin AA → Fin (N + 1)}

/-- The tables with which the moves start: every node of the network has its table, applied to the units at it, and
every other node the table 1. -/
noncomputable def startTab (S : Sys R (AA + A') E) (U1 : ℕ) (n : Fin AA → Fin AA → Fin (N + 1))
    (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) : Fin (AA + A') → (Uid AA N S.N U1 → UW ℓ) → R :=
  Fin.addCases (motive := fun _ => (Uid AA N S.N U1 → UW ℓ) → R)
    (fun a y => if ∀ u : {u : NetUnit (fun a c => (n a c).1) // u.1 = a ∨ u.2.1 = a},
        y (.init u.1.1 u.1.2.1 (Fin.castLE (Nat.le_of_lt_succ (n u.1.1 u.1.2.1).2) u.1.2.2)) ≠ none then
        tab a fun u => (y (.init u.1.1 u.1.2.1 (Fin.castLE (Nat.le_of_lt_succ (n u.1.1 u.1.2.1).2) u.1.2.2))).getD
          fun _ => false
      else 0)
    (fun _ _ => 1)

theorem startTab_congr (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) (p : Fin (AA + A'))
    {y y' : Uid AA N S.N U1 → UW ℓ} (h : ∀ b c k, y (.init b c k) = y' (.init b c k)) :
    startTab S U1 n tab p y = startTab S U1 n tab p y' := by
  refine Fin.addCases (fun a => ?_) (fun e => ?_) p
  · simp only [startTab, Fin.addCases_left, h]
  · simp only [startTab, Fin.addCases_right]

theorem startTab_ne_none (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) (p : Fin (AA + A'))
    (y : Uid AA N S.N U1 → UW ℓ) (h : startTab S U1 n tab p y ≠ 0) :
    ∀ id ∈ seen0 (N := S.N) (U1 := U1) n, Holds (hold0 S.np) (hold1 S.np) p id → y id ≠ none := by
  intro id hid hh
  rcases id with ⟨b, c, k⟩ | ⟨ν, k⟩
  swap
  · simp [seen0] at hid
  have hk : k.1 < (n b c).1 := by simpa [seen0] using hid
  revert h hh
  refine Fin.addCases (fun a => ?_) (fun e => ?_) p
  · intro h hh
    simp only [startTab, Fin.addCases_left] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    have ha : b = a ∨ c = a := by
      rcases hh with hh | hh
      · exact Or.inl (Fin.castAdd_injective _ _ hh).symm
      · exact Or.inr (Fin.castAdd_injective _ _ hh).symm
    exact hc ⟨⟨b, c, ⟨k.1, hk⟩⟩, ha⟩
  · intro h hh
    rcases hh with hh | hh <;> exact absurd (congrArg Fin.val hh) (by simp [hold0, hold1, cparty]; omega)

open Classical in
/-- The position with which the moves start has the value of the network. -/
theorem posVal_start (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) :
    posVal (hold0 S.np) (hold1 S.np) (none : UW ℓ) (seen0 (N := S.N) (U1 := U1) n) (seen0 n)
      (fun y => ∏ p, startTab S U1 n tab p (y p)) = netValue tab := by
  have e0 : posVal (hold0 S.np) (hold1 S.np) (none : UW ℓ) (seen0 (N := S.N) (U1 := U1) n) (seen0 n)
      (fun y => ∏ p, startTab S U1 n tab p (y p)) = ∑ z ∈ Common (none : UW ℓ) (seen0 (N := S.N) (U1 := U1) n),
        ∏ p, startTab S U1 n tab p (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) z p) := by
    have h1 := sum_contents_union (hold0 S.np) (hold1 S.np) (none : UW ℓ) ∅ (seen0 (N := S.N) (U1 := U1) n)
      (disjoint_empty_left _) (fun y => ∏ p, startTab S U1 n tab p (y p))
    rw [empty_union] at h1
    rw [posVal, h1]
    have h2 : Contents (hold0 S.np) (hold1 S.np) (none : UW ℓ) (∅ : Finset (Uid AA N S.N U1)) = {fun _ _ => none} := by
      ext y
      simp [Contents, funext_iff]
    rw [h2, Finset.sum_singleton]
  rw [e0]
  have hne : ∀ z, (∏ p, startTab S U1 n tab p (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) z p)) ≠ 0 →
      ∀ id ∈ seen0 (N := S.N) (U1 := U1) n, z id ≠ none := by
    intro z hz id hid
    have h1 : startTab S U1 n tab (hold0 S.np id) (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) z
        (hold0 S.np id)) ≠ 0 := fun h => hz (Finset.prod_eq_zero (mem_univ _) h)
    have h2 := startTab_ne_none tab _ _ h1 id hid (Or.inl rfl)
    rwa [ext_self hid (Or.inl rfl)] at h2
  let un : NetUnit (fun a c => (n a c).1) → Uid AA N S.N U1 := fun u =>
    .init u.1 u.2.1 (Fin.castLE (Nat.le_of_lt_succ (n u.1 u.2.1).2) u.2.2)
  have hun : ∀ u, un u ∈ seen0 (N := S.N) (U1 := U1) n := fun u => by
    simp [un, seen0]
  let W : (NetUnit (fun a c => (n a c).1) → Fin ℓ → Bool) → Uid AA N S.N U1 → UW ℓ := fun w id => match id with
    | .init a c k => if hk : k.1 < (n a c).1 then some (w ⟨a, c, ⟨k.1, hk⟩⟩) else none
    | .new _ _ => none
  have hW : ∀ w u, W w (un u) = some (w u) := by
    rintro w ⟨a, c, k⟩
    simp [W, un]
  rw [← Finset.sum_filter_of_ne (p := fun z => ∀ id ∈ seen0 (N := S.N) (U1 := U1) n, z id ≠ none) fun z _ hz => hne z hz]
  symm
  unfold netValue
  refine Finset.sum_bij' (fun w _ => W w) (fun z _ u => (z (un u)).getD fun _ => false) ?_ ?_ ?_ ?_ ?_
  · intro w _
    simp only [Finset.mem_filter, mem_common_iff]
    constructor
    · intro id hid
      rcases id with ⟨a, c, k⟩ | ⟨ν, k⟩
      · simp only [W]
        rw [dite_eq_right]
        simpa [seen0] using hid
      · rfl
    · intro id hid
      rcases id with ⟨a, c, k⟩ | ⟨ν, k⟩
      · simp only [W]
        rw [dite_eq_left (by simpa [seen0] using hid)]
        exact Option.some_ne_none _
      · simp [seen0] at hid
  · intro z _
    exact mem_univ _
  · intro w _
    funext u
    simp [hW]
  · intro z hz
    simp only [Finset.mem_filter, mem_common_iff] at hz
    funext id
    rcases id with ⟨a, c, k⟩ | ⟨ν, k⟩
    · simp only [W]
      split_ifs with hk
      · have h1 := hz.2 (.init a c k) (by simp [seen0, hk])
        have e : un ⟨a, c, ⟨k.1, hk⟩⟩ = .init a c k := rfl
        rw [e]
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h1
        rw [hv]
        rfl
      · exact (hz.1 _ (by simp [seen0, hk])).symm
    · exact (hz.1 _ (by simp [seen0])).symm
  · intro w _
    rw [Fin.prod_univ_add]
    have e2 : ∀ e : Fin A', startTab S U1 n tab (Fin.natAdd AA e)
        (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) (W w) (Fin.natAdd AA e)) = 1 := fun e => by
      simp only [startTab, Fin.addCases_right]
    rw [Finset.prod_congr rfl (fun e _ => e2 e), Finset.prod_const_one, mul_one]
    refine Finset.prod_congr rfl fun a _ => ?_
    have e3 : ∀ u : {u : NetUnit (fun a c => (n a c).1) // u.1 = a ∨ u.2.1 = a},
        ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) (W w) (Fin.castAdd A' a) (un u.1) = some (w u.1) := by
      rintro ⟨u, hu⟩
      rw [ext_self (hun u), hW]
      rcases hu with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    simp only [startTab, Fin.addCases_left, un] at e3 ⊢
    simp [e3]

end Start

open Classical in
/-- The moves shared by a thin tree and its pieces, with their causal plan and outcome test. -/
structure NetworkMoves (R : Type) [CommRing R] (AA N ℓ b G₁ : ℕ) where
  /-- the number of further nodes -/
  A' : ℕ
  /-- the number of moves -/
  E : ℕ
  /-- a bound for outcomes -/
  U1 : ℕ
  U1_pos : 0 < U1
  /-- the moves -/
  sys : Sys R (AA + A') E
  /-- the units given in the moves, their numbers, and the good outcomes -/
  plan : Plan sys N U1
  /-- a bound for the units of one move -/
  cap : ℕ
  /-- the plan is causal and gives only current units between the ends of their slots -/
  ok : plan.Ok cap
  /-- is the move a law move? -/
  isLaw : Fin E → Bool
  /-- what good means -/
  good_iff : ∀ n o x, plan.good n o x ↔ if isLaw x then
      b * ∑ ν : (sys.kind x).Cn, (o ⟨x, ν⟩).val ^ 2 ≤ G₁ * plan.num n o x ^ 2 ∧
        ∀ ν : (sys.kind x).Cn, plan.num n o x ≤ o ⟨x, ν⟩
    else ∀ ν : (sys.kind x).Cn, (o ⟨x, ν⟩).val = plan.num n o x
  /-- every possible outcome is good -/
  poss_good : ∀ n o x, plan.Poss n o ℓ x → plan.good n o x

open Classical in
/-- The networks on trees of Theorem thm:tree, for networks on AA nodes with units of ℓ bits, at
most N units at a node and at most M nodes, over R, with the exponent C, the gain γ and the integer
G₁ of the test for good outcomes. The nodes are the parties 0, ..., AA + A' − 1. For numbers n of
units and outcomes o the units of the tree are those that are current at the end, plan.cur. A unit
from a node to itself is allowed; it stays at its node, whose value sums over it.

The fields are the clauses of the theorem, except that the two bounds of (b) on the units of the
tree, for one node and in all, are the theorems `ThinTrees.node_le` and `ThinTrees.total_le`, which
follow from `edge`, `between_le`, `up_node` and `up_total`. The last sentence of (c), that the
numbers of layers of the law moves at a node add up to at most the number of bits of all units that
it ever holds, is not a field. -/
structure ThinTrees (R : Type) [CommRing R] (laws : List (G.Law R)) (AA N ℓ M b G₁ C : ℕ) (γ : ℝ)
    extends NetworkMoves R AA N ℓ b G₁ where
  /-- the stage of a node -/
  stage : Fin (AA + A') → ℕ
  /-- the depth of the tree -/
  depth : ℕ
  /-- the root -/
  root : Fin (AA + A')
  /-- the parent of a node -/
  par : (Fin AA → Fin AA → Fin (N + 1)) → (sys.N → Fin U1) → Fin (AA + A') → Fin (AA + A')
  /-- the number of units between a node and its parent, as the program bounds it: the load at the node -/
  up : (Fin AA → Fin AA → Fin (N + 1)) → (sys.N → Fin U1) → Fin (AA + A') → ℕ
  /-- the dead units -/
  dead : (sys.N → Fin U1) → Finset (Uid AA N sys.N U1)
  depth_le : depth ≤ lg M ^ C
  stage_le : ∀ p, stage p ≤ depth
  stage_given : ∀ a, stage (Fin.castAdd A' a) = 0
  stage_root : ∀ p, stage p = depth ↔ p = root
  stage_par : ∀ n o p, p ≠ root → stage (par n o p) = stage p + 1
  children_le : ∀ n o q, q ≠ root → (univ.filter fun p => p ≠ root ∧ par n o p = q).card ≤ b
  root_children_le : ∀ n o, (univ.filter fun p => p ≠ root ∧ par n o p = root).card ≤ C
  dead_le : ∀ o, (dead o).card ≤ M ^ C
  kinds : ∀ x, if isLaw x then sys.kind x ∈ laws else sys.kind x = relay R
  law_stage : ∀ r : sys.R, isLaw r.1 = true → 0 < stage (sys.rp r)
  edge : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∀ u ∈ cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E \ dead o),
      ∃ p, p ≠ root ∧ s(hold0 sys.np u, hold1 sys.np u) = s(p, par n o p)
  between_le : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) → ∀ p, p ≠ root →
    ((cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E \ dead o)).filter
      (fun u => s(hold0 sys.np u, hold1 sys.np u) = s(p, par n o p))).card ≤ up n o p
  up_node : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∀ p, ((up n o p + ∑ q ∈ univ.filter (fun q => q ≠ root ∧ par n o q = p), up n o q : ℕ) : ℝ) ≤
      (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2)
  up_total : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∑ p, up n o p ≤ lg M ^ C * M * (N + M ^ 2)
  /-- copies: what a node ever holds, with the zeros in slots and the counts of the moves, against the units that it
  has in the end -/
  copies_le : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) → ∀ p,
    ((Plan.seenAt n o E).filter (Holds (hold0 sys.np) (hold1 sys.np) p)).card +
        ∑ r ∈ univ.filter (fun r : sys.R => sys.rp r = p),
          (1 + Fintype.card ((sys.kind r.1).SlAt r.2)) * plan.num n o r.1 ≤
      C * (up n o p + ∑ q ∈ univ.filter (fun q => q ≠ root ∧ par n o q = p), up n o q) +
        (if (p : ℕ) < AA then lg M ^ C * N else 0) +
        C * ((dead o).filter (Holds (hold0 sys.np) (hold1 sys.np) p)).card
  value : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) →
    ∀ tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a,
      netValue tab = ∑ o : sys.N → Fin U1, if ∀ x, plan.good n o x then
        ∑ w ∈ Common (none : UW ℓ) (cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E)), ∏ p,
          groupVal (hold0 sys.np) (hold1 sys.np) none (Plan.seenAt n o E) (plan.cur n o E) id
            (fun a => partyTab plan n o (startTab sys U1 n tab a) a) p w
        else 0
  computed : ∃ (D steps : ℕ) (inp : (Fin AA × Fin AA) ⊕ sys.N → (Fin AA → Fin AA → Fin (N + 1)) × (sys.N → Fin U1) → Fin D)
      (H : Set ((Fin AA → Fin AA → Fin (N + 1)) × (sys.N → Fin U1) → ℕ)),
    D ≤ (M * N) ^ C ∧ steps ≤ (M * N) ^ C ∧ AA + A' ≤ (M * N) ^ C ∧ E ≤ (M * N) ^ C ∧ U1 ≤ (M * N) ^ C ∧
    Fintype.card (Uid AA N sys.N U1) ≤ (M * N) ^ C ∧
    (∀ a c x, (inp (.inl (a, c)) x : ℕ) = x.1 a c) ∧ (∀ ν x, (inp (.inr ν) x : ℕ) = x.2 ν) ∧ SlpN inp steps H ∧
    (∀ p q, (ind fun x => par x.1 x.2 p = q) ∈ H) ∧ (∀ u, (ind fun x => u ∈ plan.cur x.1 x.2 E) ∈ H) ∧
    (∀ z u, (ind fun x => u ∈ plan.cons x.1 x.2 z) ∈ H) ∧ (∀ y, (fun x => plan.num x.1 x.2 y) ∈ H) ∧
    (∀ p, (fun x => up x.1 x.2 p) ∈ H) ∧ ∀ y, (ind fun x => plan.good x.1 x.2 y) ∈ H

namespace ThinTrees

variable {R : Type} [CommRing R] {laws : List (G.Law R)} {AA N ℓ M b G₁ C : ℕ} {γ : ℝ}
  (TT : ThinTrees R laws AA N ℓ M b G₁ C γ)

open Classical in
/-- **Paper: Theorem thm:tree(b), for one node.** "All other units join a node and its parent. Their
number is at most ΛM^(1−γ)(N+M²) for one node, its children included." A unit of the tree that a
node holds joins it to its parent or to a child (`edge`), so the bound is that of the loads
(`between_le`, `up_node`). -/
theorem node_le (n : Fin AA → Fin AA → Fin (N + 1)) (hv : ∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N)
    (o : TT.sys.N → Fin TT.U1) (hg : ∀ x, TT.plan.good n o x) (p : Fin (AA + TT.A')) :
    (((cutUnits (hold0 TT.sys.np) (hold1 TT.sys.np) id (TT.plan.cur n o TT.E \ TT.dead o)).filter
        (Holds (hold0 TT.sys.np) (hold1 TT.sys.np) p)).card : ℝ) ≤
      (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2) := by
  set T := cutUnits (hold0 TT.sys.np) (hold1 TT.sys.np) id (TT.plan.cur n o TT.E \ TT.dead o)
  set Ch := univ.filter fun q => q ≠ TT.root ∧ TT.par n o q = p
  have hsub : T.filter (Holds (hold0 TT.sys.np) (hold1 TT.sys.np) p) ⊆
      ((insert p Ch).filter (· ≠ TT.root)).biUnion fun q =>
        T.filter fun u => s(hold0 TT.sys.np u, hold1 TT.sys.np u) = s(q, TT.par n o q) := by
    intro u hu
    obtain ⟨hu, hp⟩ := mem_filter.1 hu
    obtain ⟨q, hq, he⟩ := TT.edge n hv o hg u hu
    have hm : p ∈ s(q, TT.par n o q) := he ▸ Sym2.mem_iff.2 hp
    refine mem_biUnion.2 ⟨q, mem_filter.2 ⟨?_, hq⟩, mem_filter.2 ⟨hu, he⟩⟩
    rcases Sym2.mem_iff.1 hm with rfl | h
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.2 ⟨mem_univ _, hq, h.symm⟩)
  refine le_trans ?_ (TT.up_node n hv o hg p)
  refine Nat.cast_le.2 ((card_le_card hsub).trans (card_biUnion_le.trans ?_))
  refine (sum_le_sum fun q hq => TT.between_le n hv o hg q (mem_filter.1 hq).2).trans ?_
  refine (sum_le_sum_of_subset (filter_subset _ _)).trans ?_
  by_cases hp : p ∈ Ch
  · rw [insert_eq_of_mem hp]
    exact Nat.le_add_left _ _
  · rw [sum_insert hp]

open Classical in
/-- **Paper: Theorem thm:tree(b), in all.** "All other units join a node and its parent. Their
number is … at most ΛM(N+M²) in all." Every unit of the tree joins some node other than the root
to its parent (`edge`), so the bound is that of all loads (`between_le`, `up_total`). -/
theorem total_le (n : Fin AA → Fin AA → Fin (N + 1)) (hv : ∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N)
    (o : TT.sys.N → Fin TT.U1) (hg : ∀ x, TT.plan.good n o x) :
    (cutUnits (hold0 TT.sys.np) (hold1 TT.sys.np) id (TT.plan.cur n o TT.E \ TT.dead o)).card ≤
      lg M ^ C * M * (N + M ^ 2) := by
  set T := cutUnits (hold0 TT.sys.np) (hold1 TT.sys.np) id (TT.plan.cur n o TT.E \ TT.dead o)
  have hsub : T ⊆ (univ.filter (· ≠ TT.root)).biUnion fun q =>
      T.filter fun u => s(hold0 TT.sys.np u, hold1 TT.sys.np u) = s(q, TT.par n o q) := by
    intro u hu
    obtain ⟨q, hq, he⟩ := TT.edge n hv o hg u hu
    exact mem_biUnion.2 ⟨q, mem_filter.2 ⟨mem_univ _, hq⟩, mem_filter.2 ⟨hu, he⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  refine (sum_le_sum fun q hq => TT.between_le n hv o hg q (mem_filter.1 hq).2).trans ?_
  exact (sum_le_sum_of_subset (filter_subset _ _)).trans (TT.up_total n hv o hg)

end ThinTrees

/-- The integer of the test for good outcomes: "the test for good outcomes compare[s] integers, as C₀ is an integer". -/
noncomputable def goodBound (C₁ : ℝ) (a₁ : ℕ) : ℕ := ⌊2 * C₁ * (a₁ : ℝ) ^ 2⌋₊

/-- Without units from a node to itself every current unit joins two nodes: thin trees give the printed formula. -/
theorem cutUnits_id_cur {R : Type} [CommRing R] {AA A' E N U1 : ℕ} {S : Sys R (AA + A') E} (P : Plan S N U1)
    {n : Fin AA → Fin AA → Fin (N + 1)} (hn : ∀ a, n a a = 0) (o : S.N → Fin U1) :
    cutUnits (hold0 S.np) (hold1 S.np) id (P.cur n o E) = P.cur n o E := by
  unfold cutUnits
  rw [filter_true_of_mem]
  intro u hu he
  have hseen := (Plan.mem_cur.1 hu).1
  cases u with
  | init a b k =>
    have hk := Plan.init_mem_seenAt.1 hseen
    have hab : a = b := Fin.castAdd_injective _ _ he
    subst hab
    rw [hn a] at hk
    exact Nat.not_lt_zero _ hk
  | new ν k => exact (S.kind ν.1).cd ν.2 (S.inj ν.1 he)

/-- **Paper: the paragraph before Theorem thm:tree.** "An outcome is good if ‖o‖_* ≤ √C₁a₁t and o_e ≥ t for all e":
at a law move the integer test of the trees of thm_tree implies this, and is equivalent to it when 2C₁a₁² is an
integer, as it is for C₁ = 4C₀ with the integer C₀ of the laws. -/
theorem thm_tree_good {R : Type} [CommRing R] {laws : List (G.Law R)} {AA N ℓ M b C a₁ : ℕ} {γ C₁ : ℝ}
    (T : ThinTrees R laws AA N ℓ M b (goodBound C₁ a₁) C γ) (hC : 0 ≤ C₁) {n o x} (hlaw : T.isLaw x = true) :
    let printed := √((b : ℝ) / 2 * ∑ ν : (T.sys.kind x).Cn, ((o ⟨x, ν⟩).val : ℝ) ^ 2) ≤ √C₁ * a₁ * T.plan.num n o x ∧
      ∀ ν : (T.sys.kind x).Cn, T.plan.num n o x ≤ o ⟨x, ν⟩
    (T.plan.good n o x → printed) ∧
      ((∃ g : ℕ, 2 * C₁ * (a₁ : ℝ) ^ 2 = g) → printed → T.plan.good n o x) := by
  intro printed
  have h3 : 0 ≤ √C₁ * (a₁ : ℝ) * (T.plan.num n o x : ℝ) := by positivity
  have e : printed ↔ (b : ℝ) * ∑ ν : (T.sys.kind x).Cn, ((o ⟨x, ν⟩).val : ℝ) ^ 2 ≤
      2 * C₁ * (a₁ : ℝ) ^ 2 * (T.plan.num n o x : ℝ) ^ 2 ∧ ∀ ν : (T.sys.kind x).Cn, T.plan.num n o x ≤ o ⟨x, ν⟩ := by
    refine and_congr_left fun _ => ?_
    rw [Real.sqrt_le_left h3, mul_pow, mul_pow, Real.sq_sqrt hC]
    constructor <;> intro h <;> linarith
  rw [e, T.good_iff n o x, ite_eq_left hlaw]
  refine ⟨fun h => ⟨?_, h.2⟩, fun ⟨g, hg⟩ h => ⟨?_, h.2⟩⟩
  · have h2 : (b : ℝ) * ∑ ν : (T.sys.kind x).Cn, ((o ⟨x, ν⟩).val : ℝ) ^ 2 ≤
        goodBound C₁ a₁ * (T.plan.num n o x : ℝ) ^ 2 := by exact_mod_cast h.1
    exact h2.trans (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (sq_nonneg _))
  · have h2 := h.1
    rw [hg] at h2
    have h4 : goodBound C₁ a₁ = g := by rw [goodBound, hg, Nat.floor_natCast]
    calc b * ∑ ν : (T.sys.kind x).Cn, (o ⟨x, ν⟩).val ^ 2 ≤ g * T.plan.num n o x ^ 2 := by exact_mod_cast h2
      _ = _ := by simp only [h4]

end Paper
