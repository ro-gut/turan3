/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rodrigo Gutierrez, Yves Jäckle
-/

import Mathlib.Topology.Basic

import Mathlib
variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

/-- Vertice Set (V), Edge Set (E), Graphs order (n)-/
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "n" => Fintype.card α

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

set_option autoImplicit true -- I need this∈v.4.18

open Finset SimpleGraph

/-- Structure FunToMax : Represents a weight function on the vertices of the graph that sums to 1.
Mirroring the probability distribution in the informal proof-/
structure FunToMax (G : SimpleGraph α) [Fintype α] where
  w   : α → NNReal
  h_w : ∑ v∈(Finset.univ : Finset α), w v = 1

/-- Definition vp : Computes the weight contribution of an edge -/
def vp (w : α → NNReal) (e : Sym2 α) :=
  Quot.liftOn e (λ pair : α × α => w pair.1 * w pair.2)
    (by intros x y h; cases h;
        · apply refl
        · apply mul_comm)

namespace FunToMax

/-- computes the total edge weight  of the graph with respect to the weight function `W`
by summing `vp W.w e` over all edges-/
def fw {G : SimpleGraph α} [DecidableRel G.Adj] (W : FunToMax G) : NNReal :=
  ∑ e∈G.edgeFinset, vp W.w e

end FunToMax

-- section Section_1
/-!
## Section 1: Concentrating weight on a clique

From the written proof: starting from any weight function `W`, we “improve” it without decreasing `fw`
until its support is a clique.

1. We have an improved wegith function `Better` with
   • zeros preserved
   • support size = m
   • Better.fw ≥ W.fw

2. `m` finds the minimal support size (for `Better`) we can achieve without decreasing the total edge weight `Better.fw ≥ W.fw`.

3. Defining a function `Improve` we move all weight from one vertex `loose` to another `gain` (non adjacent).
   • `Improve_total_weight_nondec`: shoes the total value `fw` is equal or greater
   • `ImproveReducesSupportSize`: support size strictly decreases under `Improve`

4. By minimality of `m`, `Better_forms_clique` shows the final support forms a clique.
-/

/--
States that for any weight function `W : FunToMax G`, there exists a natural number `m` and a new weight
function (called `better`) such that:
  + The support of the new weight function is included in that of `W` (vertices with weight 0 remain 0 under `better`),
  + The number of vertices with positive weight is exactly `m`, and
  + The total edge weight of the new weight function is equal or greater than that of `W`.
-/
theorem exists_better_distribution (W : FunToMax G) :
  ∃ num : ℕ,
  ∃ better : FunToMax G,
    (∀ i, W.w i = 0 → better.w i = 0) ∧ -- support is included∈that of W
    (((Finset.univ : Finset α).filter (fun i => better.w i > 0)).card = num) ∧ -- support has size m
    (W.fw ≤ better.fw) -- has better weights
    := by
    let num := ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card
    use num
    let better := W
    use better
    have hP : ∀ (i : α), W.w i = 0 → better.w i = 0 := by
      intro i h_w_zero
      have better_eq : better.w = W.w := rfl
      rw [better_eq]
      exact h_w_zero
    have hQ : (Finset.filter (fun i => better.w i > 0) Finset.univ).card = num := by
      exact rfl
    have hR : W.fw ≤ better.fw := by
      have better_fw_eq : better.fw = W.fw := rfl
      rw [better_fw_eq]
    exact ⟨hP, ⟨hQ, hR⟩⟩

open Classical

/-- This definition computes the smallest possible "m" satisfying the properties under `exists_better_distribution` for a weight function `W` -/
noncomputable
def m (W : FunToMax G) := Nat.find (exists_better_distribution G W)

/-- Guarantees that for a distribution W, an "improved" one `better` exist where :
- vertices with weight 0 remain 0,
- Support size (vertices with positive weight) is equal to `m` (smallest possible "m" satisfying `exists_better_distribution` for a weight function `W)
- Has non decreasing total weight (`fw`) than the original distribution. -/
lemma exists_better_distribution_min_support (W : FunToMax G):
  ∃ better : FunToMax G,
    (∀ i, W.w i = 0 → better.w i = 0) ∧ -- support is included∈that of W
    (((Finset.univ : Finset α).filter (fun i => better.w i > 0)).card = (m G W)) ∧ -- support has size m
    (W.fw ≤ better.fw) -- has better weights
    := Nat.find_spec (exists_better_distribution G W)

/-- Returns an improved weight function under the conditions of `exists_better_distribution_min_support`
- vertices with weight 0 remain 0,
- Support size (vertices with positive weight) is equal to `m`
- Has non decreasing total weight (`fw`) than the original distribution..-/
noncomputable
def Better (W : FunToMax G) : FunToMax G := Classical.choose (exists_better_distribution_min_support G W)

/-- Ensures that vertices with weght 0 remain 0 under `Better`-/
lemma Better_support_included (W : FunToMax G)  (i : α) (hi : W.w i = 0) : (Better G W).w i = 0 :=
  (Classical.choose_spec (exists_better_distribution_min_support G W)).1 i hi

/-- Ensures that the support is size `m` under `Better`-/
lemma Better_support_size (W : FunToMax G) : ((Finset.univ : Finset α).filter (fun i => (Better G W).w i > 0)).card = (m G W) :=
  (Classical.choose_spec (exists_better_distribution_min_support G W)).2.1

/-- Ensures that the total edge weight computed by `Better` is equal or larger as that of W.-/
lemma Better_non_decr (W : FunToMax G) : W.fw ≤ (Better G W).fw :=
  (Classical.choose_spec (exists_better_distribution_min_support G W)).2.2

/--Constructs a new weight function by redistributing weight from one vertex (loose) to
another (gain) (distinct vertices). The new function zeros out the weight at
loose and adds it to gain (thus preserving the total weight).-/
def Improve (W : FunToMax G) (loose gain : α) (h_neq : gain  ≠ loose) : FunToMax G where
  w := fun i =>
          if i = loose
          then 0
          else if i = gain
               then W.w gain + W.w loose
               else W.w i
  h_w := by
    have remember := W.h_w
    rw [sum_ite]
    simp
    rw[Finset.sum_ite]
    have : filter (fun x => x = gain) (filter (fun x => ¬x = loose) univ) = {gain} := by
      rw[Finset.filter_filter]; ext a
      constructor
      · intro h; rw[Finset.mem_filter] at h; simp only [Finset.mem_singleton]
        exact h.2.2
      · intro h; simp only [Finset.mem_singleton] at h; rw[Finset.mem_filter]
        constructor
        · exact Finset.mem_univ a
        · constructor
          · intro contra; rw[h] at contra; exact h_neq contra
          · exact h
    rw[this, Finset.sum_singleton, Finset.filter_filter]
    let S := filter (fun x => x ≠ gain ∧ x ≠ loose) univ
    have h_sum : ∑ x ∈ univ, W.w x = (W.w gain + W.w loose) + ∑ x ∈ S, W.w x := by
      rw[←Finset.sum_add_sum_compl (filter (fun x => x = gain ∨ x = loose) univ), Finset.filter_or, Finset.sum_union]
      · have gain_filter : filter (fun x => x = gain) univ = {gain} := by ext x; simp[Finset.mem_filter, Finset.mem_univ]
        have loose_filter : filter (fun x => x = loose) univ = {loose} := by
          ext x; simp[Finset.mem_filter, Finset.mem_univ]
        rw[gain_filter, loose_filter, Finset.sum_singleton, Finset.sum_singleton]
        have compl_eq : ({gain} ∪ {loose})ᶜ = S := by ext x; simp [Finset.mem_compl, Finset.mem_union, Finset.mem_singleton, S]
        rw[compl_eq]
      · rw[Finset.disjoint_left]
        intros x hx h'x
        rw[Finset.mem_filter] at hx h'x
        have contra : gain = loose := by rw[←hx.2, h'x.2]
        exact h_neq contra
    have filter_eq_S : filter (fun a => ¬a = loose ∧ ¬a = gain) univ = S := by
      ext x; simp[Finset.mem_filter]
      constructor
      · intro h; rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ x, ⟨h.2, h.1⟩⟩
      · intro h
        rw [Finset.mem_filter] at h; exact ⟨h.2.2, h.2.1⟩
    rw[filter_eq_S, ←h_sum, remember]

/-- Helper lemma: Given that an edge e is part of gain's incidence set, this lemma proves that gain is in e.-/
lemma helper_gain_mem (e : Sym2 α) (he : e ∈ G.incidenceFinset gain) :
  gain ∈ e := by
  rw [mem_incidenceFinset] at he
  let e' : G.edgeSet := ⟨e, G.incidenceSet_subset _ he⟩
  have wow : ↑e' ∈ G.incidenceSet gain := he
  rw [edge_mem_incidenceSet_iff] at wow
  exact wow

/-- Helper lemma : Calculates the value (`vp`) of an edge e, where gain is one of the vertices in e, as the product of gain and the other vertex v, in e.-/
lemma gain_edge_decomp (W : FunToMax G) (gain : α)
  (e : Sym2 α) (he : e ∈ G.incidenceFinset gain) :
  vp W.w e = (W.w gain) * (W.w (Sym2.Mem.other (helper_gain_mem G e he))) := by
  revert he
  apply @Sym2.inductionOn α (fun e => ∀ he : e ∈ G.incidenceFinset gain, vp W.w e = (W.w gain) * (W.w (Sym2.Mem.other (helper_gain_mem G e he))))
  intro x y he
  dsimp [vp]
  have help := (Sym2.other_spec (helper_gain_mem _ _ he))
  apply @Eq.ndrec _ (s(gain, Sym2.Mem.other (helper_gain_mem G s(x, y) he))) (fun X =>
    Quot.liftOn X (fun pair => W.w pair.1 * W.w pair.2) (vp.proof_1 W.w) = W.w gain * W.w (Sym2.Mem.other (helper_gain_mem G s(x, y) he))
    ) _ s(x,y) help
  rw [Quot.liftOn_mk]

/-- Helper lemma : Shows that the sum of values of the edges incident to gain is equal to
the product of the weight of gain and the sum of the other vertices incident to gain. -/
lemma gain_edge_sum (W : FunToMax G) (gain : α) :
    ∑ e∈G.incidenceFinset gain, vp W.w e =
    (W.w gain) * ∑ e∈(G.incidenceFinset gain).attach, W.w (Sym2.Mem.other (helper_gain_mem G e.val e.prop)) := by
  rw [mul_sum, ← sum_attach]; apply sum_congr
  · rfl
  · intro x _; apply gain_edge_decomp _ _ gain _ x.prop

/-- Helper lemma : Shows that the sum of values of the edges incident to loose is equal to
the product of the weight of loose and the sum of the other vertices incident to loose. -/
lemma loose_edge_sum (W : FunToMax G) (loose : α) :
    ∑ e∈G.incidenceFinset loose, vp W.w e =
    (W.w loose) * ∑ e∈(G.incidenceFinset loose).attach, (W.w (Sym2.Mem.other (helper_gain_mem G e.val e.prop))) := by
  apply gain_edge_sum

/-- Helper lemma : Shows that two vertices are adjacent if and only if there exists an edge in the edge set corresponding to them. -/
lemma edge_mem_iff {v w : α} : G.Adj v w ↔ ∃ e ∈ G.edgeSet, e = Sym2.mk (v, w) := by
  constructor
  · intro h; use Sym2.mk (v, w)
    simp [h]
  · rintro ⟨e, he, rfl⟩; simp at he; exact he

/-- Helper lemma : States that the incidence set of any vertex is a subset of the entire edge set.-/
lemma incidenceFinset_subset (v : α) : G.incidenceFinset v ⊆ G.edgeFinset := by
  intro e he
  simp [incidenceFinset] at he
  rw [mem_edgeFinset]
  exact he.1

/-- Helper lemma: shows that the weight function created by `Improve W loose gain h_neq` is equal to its "lambda-if function" -/
@[simp]
lemma Improve_w_eq (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  (Improve G W loose gain h_neq).w = (fun i => if i = loose then 0 else if i = gain then W.w gain + W.w loose else W.w i) :=
by rfl

/-- Helper lemma : shows that the value computed by the function vp is exactly w(a) * w(b) -/
@[simp]
lemma vp_sym2_mk (w : α → NNReal) (a b : α) :
    vp w (Sym2.mk (a, b)) = w a * w b := by
  dsimp [vp]

/-- Helper lemma: Shows that the weight at the vertex “loose” is 0 after `Improve`. -/
lemma Improve_loose_weight_zero (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  (Improve G W loose gain h_neq).w loose = 0 := by
  dsimp [Improve]; simp only [if_pos rfl]
  split_ifs
  · rfl
  · rfl

/-- Helper lemma: Shows that the incidence sets of gain and loose are disjoint (Assuming they are not adjacent). -/
lemma Improve_gain_loose_disjoint {loose gain : α} (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  Disjoint (G.incidenceFinset gain) (G.incidenceFinset loose) := by
    simp_rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem, mem_inter]
    rintro x ⟨xg,xl⟩
    rw [incidenceFinset_eq_filter, mem_filter, mem_edgeFinset] at *
    apply h_adj
    rw [adj_iff_exists_edge]
    exact ⟨h_neq,⟨x,xg.1,xg.2,xl.2 ⟩⟩

/-- With the help of `Improve_gain_loose_disjoint`, introduces the set `changed` as the disjoint union of all edges
that are incident to the vertex “gain” and all edges that are incident to “loose.”
Shows that the whole edge Set (`G.edgeFinset`) can be partitioned as the disjoint union of
`changed` and `G.edgeFinset` \ `changed`. -/
lemma Improve_edgeFinset_partition (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  let changed :=
    disjUnion
      (G.incidenceFinset gain)
      (G.incidenceFinset loose)
      (Improve_gain_loose_disjoint G h_neq h_adj)
  G.edgeFinset = disjUnion changed (G.edgeFinset \ changed) (disjoint_sdiff) := by
  intro changed
  have h_disj_union : changed = G.incidenceFinset gain ∪ G.incidenceFinset loose :=
    Finset.disjUnion_eq_union _ _ _
  ext e
  simp only [Finset.mem_disjUnion, Finset.mem_union, Finset.mem_sdiff, h_disj_union, Finset.mem_coe]
  apply Iff.intro
  · intro he
    by_cases h' : e ∈ G.incidenceFinset gain ∨ e ∈ G.incidenceFinset loose
    · exact Or.inl h'
    · exact Or.inr ⟨he, h'⟩
  · intro h
    rcases h with (h_left | h_right)
    rcases h_left with (h_gain | h_loose)
    · apply incidenceFinset_subset at h_gain
      exact h_gain
    · apply incidenceFinset_subset at h_loose
      exact h_loose
    · exact h_right.left

/-- Using the same definition  `changed`, translates the partition into an equality of Sums.
Shows that the toal edge weight is equal to
- The sum over the edges incident to gain
- The sum over the edges incident to loose
- The sum over the remaining edges (the ones in `G\changed`) -/
lemma Improve_partition_sum_split (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  let changed :=
    disjUnion
      (G.incidenceFinset gain)
      (G.incidenceFinset loose)
      (Improve_gain_loose_disjoint G h_neq h_adj)
  ∑ e∈G.edgeFinset, vp W.w e =
    ∑ e∈G.incidenceFinset gain, vp W.w e +
    ∑ e∈G.incidenceFinset loose, vp W.w e +
    ∑ e∈(G.edgeFinset \ changed), vp W.w e := by
  intro changed
  have h_disj_union : changed = G.incidenceFinset gain ∪ G.incidenceFinset loose := by
    apply Finset.disjUnion_eq_union
  have h_disj_sdiff : Disjoint changed (G.edgeFinset \ changed) := Finset.disjoint_sdiff
  have h_changed_sub : changed ⊆ G.edgeFinset := by
    intro e he
    rw [Finset.mem_disjUnion] at he
    cases he with
    | inl hg =>
      exact incidenceFinset_subset G gain hg
    | inr hl =>
      exact incidenceFinset_subset G loose hl
  calc
    ∑ e∈G.edgeFinset, vp W.w e
      = ∑ e∈changed ∪ (G.edgeFinset \ changed), vp W.w e
        := by rw [Finset.union_sdiff_of_subset h_changed_sub]
    _ = ∑ e∈changed, vp W.w e + ∑ e∈(G.edgeFinset \ changed), vp W.w e
        := Finset.sum_union h_disj_sdiff
    _ = ∑ e∈(G.incidenceFinset gain ∪ G.incidenceFinset loose), vp W.w e
        + ∑ e∈(G.edgeFinset \ changed), vp W.w e
        := by rw [h_disj_union]
    _ = (∑ e∈G.incidenceFinset gain, vp W.w e
        + ∑ e∈G.incidenceFinset loose, vp W.w e)
        + ∑ e∈(G.edgeFinset \ changed), vp W.w e
        := by rw [Finset.sum_union (Improve_gain_loose_disjoint G h_neq h_adj)]
    _ = ∑ e∈G.incidenceFinset gain, vp W.w e
        + ∑ e∈G.incidenceFinset loose, vp W.w e
        + ∑ e∈(G.edgeFinset \ changed), vp W.w e
        := by rw [add_assoc]

/-- Shows that after `Improve` the total edge value over the edges incident to gain increases exactly
by the weight of loose multiplied by the sum of the ("other") vertex weights incident to gain. -/
lemma Improve_gain_contribution_increase (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
    ∑ e∈G.incidenceFinset gain, vp (Improve G W loose gain h_neq).w e =
    ∑ e∈G.incidenceFinset gain, vp W.w e
    + (W.w loose)  * ∑ e∈(G.incidenceFinset gain).attach, W.w (Sym2.Mem.other (helper_gain_mem G e.val e.prop)) := by
    rw [mul_sum, ← sum_attach]
    nth_rewrite 2 [← sum_attach]
    rw [← sum_add_distrib]
    apply sum_congr
    · rfl
    · intro x xdef
      have tec := Subtype.prop x
      revert tec
      have tec2 : (↑x ∈ G.incidenceFinset gain → vp (Improve G W loose gain h_neq).w ↑x = vp W.w ↑x + W.w loose * W.w (Sym2.Mem.other (helper_gain_mem G (↑x) (Subtype.prop x))))
        = ((P : ↑x ∈ G.incidenceFinset gain) → vp (Improve G W loose gain h_neq).w ↑x = vp W.w ↑x + W.w loose * W.w (Sym2.Mem.other (helper_gain_mem G (↑x) (P)))) :=
          by exact rfl
      rw [tec2]
      clear tec2
      apply @Sym2.inductionOn _ (fun X => ∀ (P : X ∈ G.incidenceFinset gain),
  vp (Improve G W loose gain h_neq).w X = vp W.w X + W.w loose * W.w (Sym2.Mem.other (helper_gain_mem G X P )))
      intro y z Pyz
      dsimp [vp,Quot.liftOn, Improve]
      have help := Sym2.mk_eq_mk_iff.mp (Sym2.other_spec (helper_gain_mem _ _ Pyz))
      rw [mem_incidenceFinset, mk'_mem_incidenceSet_iff] at Pyz
      cases' help with help help
      · rw [Prod.ext_iff] at help
        dsimp at help
        simp_rw [← help.1]
        rw [if_neg h_neq]
        rw [if_pos True.intro]
        rw [if_neg]
        swap
        · intro con
          apply h_adj
          rw [help.1, ← con]
          exact Pyz.1
        · rw [if_neg]
          swap
          · intro con
            rw [← help.2] at con
            apply Sym2.other_ne _ _ con
            dsimp [Sym2.IsDiag]
            apply G.ne_of_adj Pyz.1
          · rw [add_mul]
            congr
            convert help.2.symm
            exact help.1
      · dsimp! [Prod.swap] at help
        rw [Prod.ext_iff] at help
        dsimp at help
        rw [if_neg]
        swap
        · intro con
          apply h_adj
          rw [help.1, ← con]
          exact Pyz.1.symm
        · rw [if_neg]
          swap
          · apply G.ne_of_adj
            rw [help.1]
            exact Pyz.1
          · rw [if_neg]
            swap
            · intro con
              apply h_neq
              rw [help.1, ← con]
            · rw [if_pos help.1.symm]
              rw [mul_add]
              congr 1
              · rw [help.1]
              · rw [mul_comm]
                congr
                convert help.2.symm

/-- Shows that after `Improve`, the sum of edge
values over the incidence set of loose is zero. -/
lemma Improve_loose_contribution_zero (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) :
    ∑ e∈G.incidenceFinset loose, vp (Improve G W loose gain h_neq).w e = 0 := by
  let newW := (Improve G W loose gain h_neq).w
  have hl : newW loose = 0 := Improve_loose_weight_zero G W loose gain h_neq
  apply Finset.sum_eq_zero
  intro e he
  have h_mem : loose ∈ e := by
    exact helper_gain_mem G e he
  rcases Sym2.mem_iff_exists.mp h_mem with ⟨x, h_or⟩
  rcases h_or with rfl | rfl
  rw [vp_sym2_mk newW loose x, hl]
  simp

/-- Shows that the edges not incident to gain or loose (not in `changed`)
have the same weightw under the `Improve` function -/
lemma Improve_unchanged_edge_sum (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  let changed :=
    disjUnion
      (G.incidenceFinset gain)
      (G.incidenceFinset loose)
      (Improve_gain_loose_disjoint G h_neq h_adj)
  ∑ e∈(G.edgeFinset \ changed), vp (Improve G W loose gain h_neq).w e
  = ∑ e∈(G.edgeFinset \ changed), vp W.w e := by
  intro changed
  simp [vp, Quot.liftOn]
  apply Finset.sum_congr rfl
  intro e he
  apply @Sym2.inductionOn α (fun e => e ∈ G.edgeFinset \ changed →
    Quot.lift
      (fun pair =>
         if pair.2 = loose then 0
         else if pair.2 = gain then
           if pair.1 = loose then 0
           else if pair.1 = gain then (W.w gain + W.w loose) * (W.w gain + W.w loose)
           else W.w pair.1 * (W.w gain + W.w loose)
         else if pair.1 = loose then 0
         else if pair.1 = gain then (W.w gain + W.w loose) * W.w pair.2
         else W.w pair.1 * W.w pair.2)
      _ e =
    Quot.lift (fun pair => W.w pair.1 * W.w pair.2) _ e)
  intro x y he_diff
  dsimp
  have h_edge : s(x,y) ∈ G.edgeFinset := by
    rw[Finset.mem_sdiff] at he_diff
    exact he_diff.1
  /- Case: y = loose -/
  by_cases h_y_loose : y = loose
  have h_y_in : y ∈ s(x,y) := by
    simp[h_y_loose]
  have h_loose : loose ∈ s(x,y) := by
    rw[← h_y_loose]
    exact h_y_in
  have h_inc : s(x,y) ∈ G.incidenceFinset loose := by
    rw[mem_incidenceFinset]
    rw[h_y_loose]
    rw[mk'_mem_incidenceSet_iff]
    constructor
    · rw[edge_mem_iff]
      rw[h_y_loose] at h_edge
      use s(x, loose)
      constructor
      · rw [mem_edgeFinset] at h_edge
        exact h_edge
      · rfl
    · exact Or.inr rfl
  · exfalso
    rw [Finset.mem_sdiff] at he_diff
    have h_not_in_changed : s(x,y) ∉ changed := he_diff.2
    have h_changed_eq : changed = G.incidenceFinset gain ∪ G.incidenceFinset loose := by
      apply Finset.ext
      intro e
      simp only [Finset.mem_union, SimpleGraph.incidenceFinset, Finset.mem_image]
      apply Iff.intro
      · intro h
        have h_union : e ∈ G.incidenceFinset gain ∨ e ∈ G.incidenceFinset loose :=
          Finset.mem_disjUnion.mp h
        cases h_union with
        | inl h_gain => exact Or.inl h_gain
        | inr h_loose => exact Or.inr h_loose
      · intro h_disj
        cases h_disj with
        | inl h_gain =>
            rw [Finset.mem_disjUnion]; left; exact h_gain
        | inr h_loose =>
            rw [Finset.mem_disjUnion]; right; exact h_loose
    have h_in_changed : s(x,y) ∈ changed := by
      rw[h_changed_eq]
      apply Finset.mem_union_right
      exact h_inc
    contradiction
  /- Case: y = gain -/
  by_cases h_y_gain : y = gain
  have h_y_in : y ∈ s(x,y) := by
    simp[h_y_gain]
  have h_gain : gain ∈ s(x,y) := by
    rw[← h_y_gain]
    exact h_y_in
  have h_inc : s(x,y) ∈ G.incidenceFinset gain := by
    rw[mem_incidenceFinset]
    rw[h_y_gain]
    rw[mk'_mem_incidenceSet_iff]
    constructor
    · rw[edge_mem_iff]
      rw[h_y_gain] at h_edge
      use s(x, gain)
      constructor
      · rw [mem_edgeFinset] at h_edge
        exact h_edge
      · rfl
    · exact Or.inr rfl
  · exfalso
    rw [Finset.mem_sdiff] at he_diff
    have h_not_in_changed : s(x,y) ∉ changed := he_diff.2
    have h_changed_eq : changed = G.incidenceFinset gain ∪ G.incidenceFinset loose := by
      apply Finset.ext
      intro e
      simp only [Finset.mem_union, SimpleGraph.incidenceFinset, Finset.mem_image]
      apply Iff.intro
      · intro h
        have h_union : e ∈ G.incidenceFinset gain ∨ e ∈ G.incidenceFinset loose :=
          Finset.mem_disjUnion.mp h
        cases h_union with
        | inl h_gain => exact Or.inl h_gain
        | inr h_loose => exact Or.inr h_loose
      · intro h_disj
        cases h_disj with
        | inl h_gain =>
            rw [Finset.mem_disjUnion]; left; exact h_gain
        | inr h_loose =>
            rw [Finset.mem_disjUnion]; right; exact h_loose
    have h_in_changed : s(x,y) ∈ changed := by
      rw[h_changed_eq]
      apply Finset.mem_union_left
      exact h_inc
    contradiction
  /- Case: x = loose -/
  by_cases h_x_loose : x = loose
  · have h_x_in : x ∈ s(x,y) := by
      simp[h_x_loose]
    have h_loose : loose ∈ s(x,y) := by
      rw[← h_x_loose]
      exact h_x_in
    have h_inc : s(x,y) ∈ G.incidenceFinset loose := by
      rw[mem_incidenceFinset]
      rw[h_x_loose]
      rw[mk'_mem_incidenceSet_iff]
      constructor
      · rw[edge_mem_iff]
        rw[h_x_loose] at h_edge
        use s(loose, y)
        constructor
        · rw [mem_edgeFinset] at h_edge
          exact h_edge
        · rfl
      · exact Or.inl rfl
    · exfalso
      rw [Finset.mem_sdiff] at he_diff
      have h_not_in_changed : s(x,y) ∉ changed := he_diff.2
      have h_changed_eq : changed = G.incidenceFinset gain ∪ G.incidenceFinset loose := by
        apply Finset.ext
        intro e
        simp only [Finset.mem_union, SimpleGraph.incidenceFinset, Finset.mem_image]
        apply Iff.intro
        · intro h
          have h_union : e ∈ G.incidenceFinset gain ∨ e ∈ G.incidenceFinset loose :=
            Finset.mem_disjUnion.mp h
          cases h_union with
          | inl h_gain => exact Or.inl h_gain
          | inr h_loose => exact Or.inr h_loose
        · intro h_disj
          cases h_disj with
          | inl h_gain =>
              rw [Finset.mem_disjUnion]; left; exact h_gain
          | inr h_loose =>
              rw [Finset.mem_disjUnion]; right; exact h_loose
      have h_in_changed : s(x,y) ∈ changed := by
        rw[h_changed_eq]
        apply Finset.mem_union_right
        exact h_inc
      contradiction
  /- Case: x = gain -/
  by_cases h_x_gain : x = gain
  · have h_x_in : x ∈ s(x,y) := by
      simp[h_x_gain]
    have h_gain : gain ∈ s(x,y) := by
      rw[← h_x_gain]
      exact h_x_in
    have h_inc : s(x,y) ∈ G.incidenceFinset gain := by
      rw[mem_incidenceFinset]
      rw[h_x_gain]
      rw[mk'_mem_incidenceSet_iff]
      constructor
      · rw[edge_mem_iff]
        rw[h_x_gain] at h_edge
        use s(gain, y)
        constructor
        · rw [mem_edgeFinset] at h_edge
          exact h_edge
        · rfl
      · exact Or.inl rfl
    exfalso
    rw [Finset.mem_sdiff] at he_diff
    have h_not_in_changed : s(x,y) ∉ changed := he_diff.2
    have h_changed_eq : changed = G.incidenceFinset gain ∪ G.incidenceFinset loose := by
      apply Finset.ext
      intro e
      simp only [Finset.mem_union, SimpleGraph.incidenceFinset, Finset.mem_image]
      apply Iff.intro
      · intro h
        have h_union : e ∈ G.incidenceFinset gain ∨ e ∈ G.incidenceFinset loose :=
          Finset.mem_disjUnion.mp h
        cases h_union with
        | inl h_gain => exact Or.inl h_gain
        | inr h_loose => exact Or.inr h_loose
      · intro h_disj
        cases h_disj with
        | inl h_gain =>
            rw [Finset.mem_disjUnion]; left; exact h_gain
        | inr h_loose =>
            rw [Finset.mem_disjUnion]; right; exact h_loose
    have h_in_changed : s(x,y) ∈ changed := by
      rw[h_changed_eq]
      apply Finset.mem_union_left
      exact h_inc
    contradiction
  simp [if_neg h_y_loose, if_neg h_y_gain, if_neg h_x_loose, if_neg h_x_gain]
  exact he

/-- Assumption h mirrors the assumption s_1 ≤ s_2 in the informal proof.
This lemma shows that the total edge weight does not decrease under `Improve`, using the previous lemmas:
- `Improve_partition_sum_split`: splits the edge set into the sum of : edges incident to gain, edges incident to loose, the remaining edges
- `Improve_unchanged_edge_sum`: shows all edges not incident to "loose" or "gain" remain unchanged.
- `Improve_gain_contribution_increase`: shows that gain’s contribution increases by the weight of loose times the other values incident to "gain"
- `Improve_loose_contribution_zero`: shows that loose’s new contribution is zero
- `loose_edge_sum`: expresses the original contribution of loose  as `W.w loose * sum of its neighbors`.
--/
lemma Improve_total_weight_nondec (W : FunToMax G) (loose gain : α)
  (h : ∑ e∈(G.incidenceFinset gain).attach,
      (W.w (Sym2.Mem.other (helper_gain_mem G e.val e.prop))) ≥
      ∑ e∈(G.incidenceFinset loose).attach, (W.w (Sym2.Mem.other
      (helper_gain_mem G e.val e.prop))))
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  (Improve G W loose gain h_neq).fw ≥ W.fw := by
  simp_rw [FunToMax.fw]
  rw [Improve_partition_sum_split G (Improve G W loose gain h_neq) loose gain h_neq h_adj]
  rw [Improve_partition_sum_split G W loose gain h_neq h_adj]
  rw [Improve_unchanged_edge_sum G W loose gain h_neq h_adj]
  apply add_le_add_right
  rw [Improve_gain_contribution_increase G W loose gain h_neq h_adj, Improve_loose_contribution_zero G W loose gain h_neq]
  rw [add_zero]
  apply add_le_add_left
  rw [loose_edge_sum]
  apply mul_le_mul_of_nonneg_left h (by exact zero_le (W.w loose))

/-- Shows that if a vertex has weight 0 , then the weight remains 0 under the Improved function. -/
lemma Improve_support_remains_zero (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_supp : 0 < W.w gain) :
  ∀ i, W.w i = 0 → (Improve G W loose gain h_neq).w i = 0 := by
  intro i h_zero
  simp only [Improve, FunToMax.w]
  split_ifs with _ H
  · rfl
  · rw [H] at h_zero; rw [h_zero] at h_supp; exfalso; apply lt_irrefl 0 h_supp
  · exact h_zero

/-- Using `Improve_support_remains_zero`, shows that the support under `Improve` is strictly smaller than
that of the original weight function W -/
lemma Improve_support_strictly_reduced (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_supp1 : 0 < W.w gain)
  (h_supp2: 0 < W.w loose) :
  ((Finset.univ : Finset α).filter (fun i => (Improve G W loose gain h_neq).w i > 0)).card
  < ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card := by
      apply card_lt_card
      rw [ssubset_iff_of_subset]
      · use loose
        constructor
        · rw [Finset.mem_filter]
          constructor
          · exact Finset.mem_univ loose
          · exact h_supp2
        · rw [Finset.mem_filter] at *
          intro H
          rcases H with ⟨H_univ, H_pos⟩
          have H_zero : (Improve G W loose gain h_neq).w loose = 0 := Improve_loose_weight_zero G W loose gain h_neq
          rw [gt_iff_lt] at H_pos
          rw [H_zero] at H_pos
          exact lt_irrefl 0 H_pos
      · intro x xmem
        rw [mem_filter] at *
        simp_rw [@pos_iff_ne_zero NNReal] at xmem
        simp_rw [@pos_iff_ne_zero NNReal]
        refine' ⟨xmem.1, _ ⟩
        replace xmem := xmem.2
        contrapose! xmem
        exact Improve_support_remains_zero G W loose gain h_neq h_supp1 x xmem

/--
Proves that the support of `Better` is a clique.  If two support vertices (gain,loose)
 were non‑adjacent, shows wlog that `loose` has at least as large a neighbor‐sum as `gain`, then
applies `Improve` to move all the weight from `loose` to `gain`.  By
- `Improve_total_weight_nondec`: `fw` does not decrease, and
- `Improve_support_strictly_reduced`: the support strictly shrinks,

this contradicts the minimality of `Better`’s support size `m`.
Therefore no such non‑adjacent pair exists.
-/
lemma Better_forms_clique (W : FunToMax G) :
  G.IsClique ((Finset.univ : Finset α).filter (fun i => (Better G W).w i > 0)) := by
  by_contra con
  dsimp [IsClique, Set.Pairwise] at con
  push_neg at con
  obtain ⟨x,xdef,y,ydef,xny,xyAdj⟩ := con
  wlog wlog : ∑ e∈(G.incidenceFinset x).attach, ((Better G W).w (Sym2.Mem.other (helper_gain_mem G e.val e.prop)))
                ≥ ∑ e∈(G.incidenceFinset y).attach, ((Better G W).w (Sym2.Mem.other (helper_gain_mem G e.val e.prop)))  with SymCase
  · push_neg at wlog
    specialize SymCase G W y ydef x xdef (ne_comm.mp xny) (by rw [G.adj_comm] ; exact xyAdj)
    have H : ∑ e∈(G.incidenceFinset y).attach, (Better G W).w (Sym2.Mem.other (helper_gain_mem G e.val e.prop))
      ≥ ∑ e∈(G.incidenceFinset x).attach, (Better G W).w (Sym2.Mem.other (helper_gain_mem G e.val e.prop)) := le_of_lt wlog
    exact SymCase H
  have h_pos_x : (Better G W).w x > 0 := (Finset.mem_filter.mp xdef).2
  have h_pos_y : (Better G W).w y > 0 := (Finset.mem_filter.mp ydef).2
  · have con :
      (fun X => ∃ even_better : FunToMax G,
        (∀ i, W.w i = 0 → even_better.w i = 0) ∧
        (((Finset.univ : Finset α).filter (fun i => even_better.w i > 0)).card = X) ∧
        (W.fw ≤ even_better.fw))
        (#(filter (fun i => (Improve G (Better G W) y x xny).w i > 0) univ)) :=
        by
        use (Improve G (Better G W) y x xny)
        constructor
        · intro i wi
          apply Improve_support_remains_zero
          · have h_x_pos : (Better G W).w x > 0 := (Finset.mem_filter.mp xdef).2
            exact h_x_pos -- xdef
          · apply Better_support_included _ _ _ wi
        · constructor
          · rfl
          · apply le_trans (Better_non_decr _ W)
            exact Improve_total_weight_nondec G (Better G W) y x wlog xny xyAdj
    have ohoh := @Nat.find_le (#(filter (fun i => (Improve G (Better G W) y x xny).w i > 0) univ)) _ _ (exists_better_distribution G W) con
    have nono := Improve_support_strictly_reduced G (Better G W) y x xny h_pos_x h_pos_y
    rw [Better_support_size G W] at nono
    apply not_lt_of_le ohoh nono

-- end Section_1

-- section Section_2
/-!
Section 2: Second weight moving argument in a clique configuration

We aim to show that any non‑uniform weight distribution on a clique can be further improved by a small transfer:

1. Define `Enhance` to move a tiny ε (with 0 < ε < W.w loose – W.w gain) from `loose` to `gain`.

2. Proves with `Enhance_total_weight_nondec` that under `Enhance`:
   - the support remains the same clique,
   - only `loose` and `gain` change weight,
   - the total edge‐weight `fw` does not decrease (and strictly increases unless W was already uniform).

-- Applying `Enhance`, will force all positive weights on the clique to become equal.-/

/-- Helper lemma Shows that the support of a weight distribution is nonempty -/
lemma support_size_nonempty (W : FunToMax G) : ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card ≠ 0 := by
  intro h_empty
  have all_zero : ∀ i, W.w i = 0 :=
    fun i =>
      if h_pos : W.w i > 0 then
        let mem_i : i ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_pos⟩
        have card_pos : 0 < (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) :=
          Finset.card_pos.mpr ⟨i, mem_i⟩
        by linarith
      else
        le_antisymm (not_lt.mp h_pos) (zero_le (W.w i))
  have sum0 : ∑ i∈(Finset.univ : Finset α), W.w i = 0 :=
    Finset.sum_eq_zero (fun i hi => all_zero i)
  rw [W.h_w] at sum0
  have hcontra : (1 : NNReal) ≠ 0 := by simp
  exact hcontra sum0

/-- There exists an improved weight function with: weights that were 0 remain 0 (support included)
support forms a clique an has exactly m vertices with 1/m weight each,
and that the total edge weight does not decrease.-/
@[reducible]
def exists_uniform_clique (W : FunToMax G) :=
  (fun m =>
    ∃ better : FunToMax G,
      (∀ i, W.w i = 0 ↔ better.w i = 0) ∧
      (G.IsClique ((Finset.univ : Finset α).filter (fun i => better.w i > 0))) ∧
      (((Finset.univ : Finset α).filter (fun i => better.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card = m) ∧ -- number of weights being 1/k is m
      (W.fw ≤ better.fw))

open Classical

/-- Using `exists_uniform_clique`, computes the largest number m for which there exists a weight function (with support contained in that of W)
whose support forms a clique, has improved total edge weight, and has exactly m vertices with weight 1/k (support size). -/
noncomputable
def max_uniform_support (W : FunToMax G) :=
  Nat.findGreatest (exists_uniform_clique G W) ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card

/--Provides the specification for the `Nat.findGreates` in `max_uniform_support`. Shows that for any weight function whose support forms a clique
There is an improved weight function (with the specified support and uniform weights) with improved total edge weight value
having exactly m vertices with 1/m  support size-/
lemma exists_best_uniform (W : FunToMax G)
  (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  (fun m =>
    ∃ better : FunToMax G,
      (∀ i, W.w i = 0 ↔ better.w i = 0) ∧
      (G.IsClique ((Finset.univ : Finset α).filter (fun i => better.w i > 0))) ∧
      (((Finset.univ : Finset α).filter (fun i => better.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card = m) ∧ -- number of weights being 1/k is m
      (W.fw ≤ better.fw))
      (max_uniform_support G W)
    :=
    @Nat.findGreatest_spec ((Finset.univ : Finset α).filter (fun i => W.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card (exists_uniform_clique G W) _
      ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card
      (by
        apply card_le_card
        intros i hi
        rw [Finset.mem_filter] at *
        constructor
        · exact hi.1
        · rw [hi.2]
          let j := (#(filter (fun i => W.w i > 0) univ))
          have j_nonzero : j ≠ 0 :=
            @support_size_nonempty α G (inferInstance : Fintype α)
            (inferInstance : DecidableEq α) (inferInstance : DecidableRel G.Adj) W
          have j_pos : j > 0 := Nat.pos_of_ne_zero j_nonzero
          rw [div_eq_mul_inv]
          rw [one_mul]
          have h1 : ((j : NNReal)⁻¹) = 1 / (j : NNReal) := by rw [inv_eq_one_div]
          rw [h1]
          have h_j_pos : (j : NNReal) > 0 := by exact_mod_cast j_pos
          have h1_real : (1 : ℝ) / ((j : NNReal) : ℝ) > 0 := div_pos zero_lt_one (by exact_mod_cast j_pos)
          exact_mod_cast h1_real)
      (by
        dsimp [exists_uniform_clique]
        use W
        constructor
        · intro i
          exact Iff.rfl
        constructor
        · exact hW
        constructor
        · rfl
        · exact le_refl W.fw)

/-- For a given weight function W, whose support forms a clique (hW), UniformBetter gives a new weight function (using `exists_best_uniform`)
with same support but where every vertex has the same weight (1/m, where m is the support size). Total edge
value does not decrease -/
noncomputable
def UniformBetter (W : FunToMax G) (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) : FunToMax G := Classical.choose (exists_best_uniform G W hW)

/-- Ensures if a vertex is zero in W if and only if it is zero in `UniformBetter` W -/
lemma UniformBetter_support_zero (W : FunToMax G) (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (i : α) : W.w i = 0 ↔ (UniformBetter G W hW).w i = 0 :=
  (Classical.choose_spec (exists_best_uniform G W hW)).1 i

/-- States that the number of vertices with weight 1/m (m being support size) in `UniformBetter W` is exactly m-/
lemma UniformBetter_support_size (W : FunToMax G) (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
 ((Finset.univ : Finset α).filter (fun i => (UniformBetter G W hW).w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card = (max_uniform_support G W) :=
  (Classical.choose_spec (exists_best_uniform G W hW)).2.2.1

/-- States that the total edge weight of `UniformBetter` is equal or greater than that of `W`-/
lemma UniformBetter_fw_ge (W : FunToMax G) (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) : W.fw ≤ (UniformBetter G W hW).fw :=
  (Classical.choose_spec (exists_best_uniform G W hW)).2.2.2

/-- Confirms that the support of `UniformBetter` forms a clique in the Graph -/
lemma UniformBetter_clique (W : FunToMax G) (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
   G.IsClique ((Finset.univ : Finset α).filter (fun i => (UniformBetter G W hW).w i > 0)) :=
  (Classical.choose_spec (exists_best_uniform G W hW)).2.1

/-- Constructs a new weight function by moving a small amount of weight `ε < W(loose) - W(gain)` from vertex loose to vertex gain
assuming W.w gain < W.w loose. It preservers the total weight improving the weight function-/
noncomputable
def Enhance (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (_ : 0 < ε) (elt : ε < W.w loose - W.w gain) : FunToMax G where
  w := fun i =>
          if i = loose
          then W.w loose - ε
          else if i = gain
               then W.w gain + ε
               else W.w i
  h_w := by
    let S : Finset α := {loose, gain}
    have split_univ : S ∪ (univ \ S) = univ :=
      Finset.union_sdiff_of_subset (Finset.subset_univ S)
    have disj : Disjoint S (univ \ S) := Finset.disjoint_sdiff
    rw [← split_univ, Finset.sum_union disj]
    have eq_S : S = {loose} ∪ {gain} := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_insert] at hx
        rw [Finset.mem_union, Finset.mem_singleton]
        rcases hx with (h_loose | h_gain)
        · left
          exact h_loose
        · right
          exact h_gain
      · intro hx
        rw [Finset.mem_union] at hx
        rcases hx with (h_loose | h_gain)
        · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h_loose))
        · exact Finset.mem_insert.mpr (Or.inr h_gain)
    rw [eq_S]
    have disj2 : Disjoint ({loose} : Finset α) ({gain} : Finset α) := by
      rw [Finset.disjoint_singleton_left, Finset.mem_singleton]
      intro eq
      subst eq
      apply lt_irrefl (W.w loose)
      exact h_lt
    rw [Finset.sum_union disj2, Finset.sum_singleton, Finset.sum_singleton]
    simp only [if_pos rfl, if_neg (λ h => absurd h (ne_of_lt h_lt))] at *
    ring_nf
    have h_ne : gain ≠ loose := by
      intro h_neq
      rw[h_neq] at h_lt
      exact lt_irrefl (W.w loose) h_lt
    simp only [if_true, if_false] at *
    have h_simpl : ∀ x ∈ univ \ ({loose} ∪ {gain}),
  (if x = loose then W.w loose - ε else if x = gain then W.w gain + ε else W.w x) = W.w x :=
      by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        by_cases hxl : x = loose
        · exfalso
          rw[hxl] at hx
          have mem_union : loose ∈ {loose} ∪ {gain} := Finset.mem_union_left {gain} (Finset.mem_singleton_self loose)
          exact hx.2 mem_union
        by_cases hxg : x = gain
        · exfalso
          rw [hxg] at hx
          have mem_union : gain ∈ ({loose} : Finset α) ∪ ({gain} : Finset α) :=
      Finset.mem_union_right ({loose} : Finset α) (Finset.mem_singleton_self gain)
          exact hx.2 mem_union
        simp [hxl, hxg]
    rw [Finset.sum_congr rfl h_simpl]
    simp only [if_neg h_ne] at *
    calc
      (W.w loose - ε + (W.w gain + ε)) + (univ \ ({loose} ∪ {gain})).sum W.w
          = (W.w loose + W.w gain) + (univ \ ({loose} ∪ {gain})).sum W.w :=
        by
          rw [add_comm (W.w gain) ε]
          rw [← add_assoc]
          have h_tec : ε ≤ W.w loose := by
            replace elt := add_le_of_le_tsub_left_of_le (le_of_lt h_lt) (le_of_lt elt)
            apply le_trans (le_add_of_nonneg_left (W.w gain).prop) elt
          rw [tsub_add_cancel_iff_le.mpr h_tec]
      _ = (∑ x∈{loose} ∪ {gain}, W.w x) + (univ \ ({loose} ∪ {gain})).sum W.w := by
        rw [Finset.sum_union disj2, Finset.sum_singleton, Finset.sum_singleton]
      _ = ∑ x∈({loose} ∪ {gain}) ∪ (univ \ ({loose} ∪ {gain})), W.w x :=
        by rw [← split_univ, Finset.sum_union (Finset.disjoint_sdiff)]
      _ = ∑ x∈univ, W.w x := by rw [← eq_S, split_univ]
      _ = 1 := by exact W.h_w

/-- Helper lemma: deduces that if gain and loose have different weights then gain and loose arent the same vertex-/
lemma neq_of_W_lt {W : FunToMax G} {loose gain : α} (h_neq : W.w gain < W.w loose) : gain ≠ loose :=
  by
  intro con
  rw [con] at h_neq
  apply lt_irrefl _ h_neq

 /-- Helper lemma: if (NNReal) is not positive it must be 0-/
lemma NNReal.eq_zero_of_ne_pos {x : NNReal} (h : ¬ x > 0) : x = 0 := by
  rw [← NNReal.coe_inj, eq_comm]
  simp_rw [← NNReal.coe_pos] at h
  have := x.prop
  apply eq_of_le_of_not_lt this h

/-- Shows that after applying `Enhance`, vertices that had weight 0, remain with the same weight 0 (Support is preserved). -/
lemma Enhance_nsupport_unchanged (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) (ah : 0 < W.w gain)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ i, W.w i = 0 ↔ (Enhance G W loose gain h_lt ε epos elt).w i = 0 := by
    intro i
    dsimp[Enhance]
    split_ifs with h_loose h_gain
    · rw[h_loose]
      constructor
      · intro wl0
        rw[wl0]
        rw[wl0] at h_lt
        have h_nonneg : 0 ≤ W.w gain := (W.w gain).prop
        apply zero_tsub
      · intro h
        rw [tsub_eq_zero_iff_le] at h
        exfalso
        have this_should_be_a_lemma : ε < W.w loose := by
          apply lt_of_lt_of_le elt ; exact tsub_le_self
        rw [← not_le] at this_should_be_a_lemma
        exact this_should_be_a_lemma h
    · rw[h_gain]
      constructor
      · intro h
        exfalso
        rw [h] at ah
        apply lt_irrefl _ ah
      · intro h
        have h_zero : W.w gain = 0 ∧ ε = 0 := by exact AddLeftCancelMonoid.add_eq_zero.mp h
        exact h_zero.1
    · rfl

/-- Complement of Enhance_support_zero: shows that a vertex has positive weight
 in W if and only if it has positive weight in the Enhanced function (Support is preserved). -/
lemma Enhance_support_unchanged (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) (ah : 0 < W.w gain)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ i, W.w i > 0 ↔ (Enhance G W loose gain h_lt ε epos elt).w i > 0 := by
    intro i
    rw [← not_iff_not]
    constructor
    · intro h
      intro con
      replace h := NNReal.eq_zero_of_ne_pos  h
      rw [Enhance_nsupport_unchanged G W loose gain h_lt ah ε epos elt] at h
      rw [h] at con
      exact lt_irrefl _ con
    · intro h
      intro con
      replace h := NNReal.eq_zero_of_ne_pos  h
      rw [← Enhance_nsupport_unchanged G W loose gain h_lt ah ε epos elt] at h
      rw [h] at con
      exact lt_irrefl _ con

/-- Proves that after applying `Enhance` the support still forms a clique -/
lemma Enhance_clique (W : FunToMax G) (loose gain : α)
  (h_lt : W.w gain < W.w loose) (ah : 0 < W.w gain)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  G.IsClique ((Finset.univ : Finset α).filter
              (fun i => (Enhance G W loose gain h_lt ε epos elt).w i > 0)) := by
    dsimp [IsClique]
    intros x hx y hy xny
    let F : α → NNReal := FunToMax.w W
    let Wloose : NNReal := F loose
    let Wgain  : NNReal := F gain
    let Wloose : NNReal := (FunToMax.w W) loose
    let Wgain  : NNReal := (FunToMax.w W) gain
    let hx₀ := Finset.mem_coe.mp hx
    rcases Finset.mem_filter.mp hx₀ with ⟨_, xPosNew⟩
    let hy₀ := Finset.mem_coe.mp hy
    rcases Finset.mem_filter.mp hy₀ with ⟨_, yPosNew⟩
    rw [← Enhance_support_unchanged G W loose gain h_lt ah ε epos elt] at xPosNew yPosNew
    apply hc
    · simp only [gt_iff_lt, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      exact xPosNew
    · simp only [gt_iff_lt, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      exact yPosNew
    · exact xny

/-- Helper definition: Defines that an edge (element of the structur Sym2 α) is "Supported" if both of its vertices have positive
weight (according to a weight function W)-/
def Sym2.inSupport (W : FunToMax G) (e : Sym2 α) : Prop :=
  @Quot.lift _ (Sym2.Rel α) Prop (fun x => W.w x.1 > 0 ∧ W.w x.2 > 0)
    (by
     intro a b rel
     dsimp
     rw [Sym2.rel_iff'] at rel
     cases' rel with rel rel
     · rw [rel]
     · rw [rel]
       dsimp
       nth_rewrite 1 [and_comm]
       rfl) e

/-- Helper lemma : states the explicit characterization of an edge being in the Support, meaning both vertices
must have positive weights. -/
lemma Sym2.inSupport_explicit (W : FunToMax G) {x y : α} : s(x,y).inSupport G W ↔ (W.w x > 0 ∧ W.w y > 0) := by
  dsimp [inSupport]
  rfl

/-- Helper lemma: If an edge e is not in the support,  then the value of e (using vp) is 0. -/
lemma Sym2.notinSupport (W : FunToMax G) {e : Sym2 α} (h : ¬ e.inSupport G W ) : vp W.w e = 0 := by
  dsimp [inSupport] at h
  revert h
  apply @Sym2.inductionOn _ (fun e => ¬ Quot.lift (fun x => W.w x.1 > 0 ∧ W.w x.2 > 0) (inSupport.proof_1 G W) e → vp W.w e = 0) e
  intro x y h
  dsimp at h
  dsimp [vp]
  rw [not_and_or] at h
  cases' h with h h
  · rw [NNReal.eq_zero_of_ne_pos h, zero_mul]
  · rw [NNReal.eq_zero_of_ne_pos h, mul_zero]

/--  Helper lemma: Shows that if an edge e is in support and a vertex x belongs to e, then x has positive weight -/
lemma Sym2.inSupport_mem (W : FunToMax G) {x : α} {e : Sym2 α} (hm : x ∈ e) (hs : e.inSupport G W) : W.w x > 0 := by
  revert hs hm
  apply @Sym2.ind _ (fun e => x ∈ e → inSupport G W e → W.w x > 0)
  intro y z hm hs
  rw [Sym2.mem_iff] at hm
  rw [Sym2.inSupport_explicit] at hs
  cases' hm with hm hm
  · rw [hm] ; exact hs.1
  · rw [hm] ; exact hs.2

/--  Helper lemma: Shows that if an edge e is in support and x is part of e, then the weight of the other vertice in e is positive.-/
lemma Sym2.inSupport_other (W : FunToMax G) {x : α} {e : Sym2 α} (hm : x ∈ e) (hs : e.inSupport G W) : W.w (Sym2.Mem.other hm) > 0 := by
  revert hs hm
  apply @Sym2.ind _ (fun e => (hm : x ∈ e) → inSupport G W e → W.w (Sym2.Mem.other hm) > 0)
  intro y z hm hs
  have := Sym2.other_spec hm
  rw [Sym2.eq, Sym2.rel_iff'] at this
  rw [Sym2.inSupport_explicit] at hs
  cases' this with this this
  · rw [Prod.ext_iff] at this ; dsimp at this ; rw [this.2] ; exact hs.2
  · rw [Prod.ext_iff] at this ; dsimp at this ; rw [this.2] ; exact hs.1

/--  Helper lemma: Proves that if all vertices in an edge e have positives weights, then e is in the support. -/
lemma Sym2.inSupport_rec (W : FunToMax G) {e : Sym2 α} (h : ∀ x ∈ e, W.w x > 0) : e.inSupport G W := by
  revert h
  apply @Sym2.ind _ (fun e => (∀ x ∈ e, W.w x > 0) → e.inSupport G W) _ e
  intro x y h
  rw [Sym2.inSupport_explicit]
  exact ⟨h x (Sym2.mem_mk_left _ _), h y (Sym2.mem_mk_right _ _)⟩

/-- definition: Defines the subset of a vertex's incident set, that consists of supported edges -/
noncomputable
def SimpleGraph.supIncidenceFinset (W : FunToMax G) (v : α) :=
  (G.incidenceFinset v).filter (Sym2.inSupport G W)

/-- definition: Defines the subset of the whole edge set, where the edges are supported-/
noncomputable
def SimpleGraph.supEdgeFinset (W : FunToMax G) :=
  G.edgeFinset.filter (Sym2.inSupport G W)

/-- Helper lemma:  Explicitly characterizes the definition of supIncidenceFinset:
- edges are incident to the vertex
- edges are supported -/
lemma SimpleGraph.mem_supIncidenceFinset {W : FunToMax G} {v : α} {e : Sym2 α} :
  e ∈ G.supIncidenceFinset W v ↔ e ∈ (G.incidenceFinset v) ∧ e.inSupport G W := by
  dsimp [supIncidenceFinset] ; rw [mem_filter]

/--  Helper lemma: Explicitly caracterizes the definition of supEdgeFinset :
- edges are in the edge set of the graph
- edges are supported
-/
lemma SimpleGraph.mem_supEdgeFinset {W : FunToMax G} {e : Sym2 α} :
  e ∈ G.supEdgeFinset W ↔ e ∈ (G.edgeFinset) ∧ e.inSupport G W := by
  dsimp [supEdgeFinset] ; rw [mem_filter]

/--  Helper lemma: Shows that any edge part of an supported incident set of a vertex, is also part of whole incident set of v. -/
lemma SimpleGraph.small_helpI {W : FunToMax G} {v : α} {e : Sym2 α} (h : e ∈ G.supIncidenceFinset W v) :
  e ∈ (G.incidenceFinset v) := by
  rw [mem_supIncidenceFinset] at h ; exact h.1

/--  Helper lemma: Shows that any edge in the supported edge set is indeed an edge of the graph. -/
lemma SimpleGraph.small_helpE {W : FunToMax G} {e : Sym2 α} (h : e ∈ G.supEdgeFinset W) : e ∈ (G.edgeFinset) := by
  rw [mem_supEdgeFinset] at h ; exact h.1

/-- Helper lemma: Shows that the supported incidence set of a vertex is subset of its full incident set -/
lemma supIncidenceFinset_subset (W : FunToMax G) (v : α) :
  (G.supIncidenceFinset W v) ⊆ G.incidenceFinset v :=
Finset.filter_subset (fun e => Sym2.inSupport G W e) (G.incidenceFinset v)

/-- Helper lemma : extracts from the fact that an element a belongs to the set difference s \ t that a is indeed in s. -/
lemma in_sdiff_left {s t : Finset α} {a : α} (h : a ∈ s \ t) : a ∈ s := by
  rw [Finset.mem_sdiff] at h; exact h.1

----

/-- Shows that for a weight function W (and distinct loose and gain), the supported incidence sets of gain and loose
(without the edge (gain,loose) are disjoint) -/
lemma disjoint_supported_incidence (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  Disjoint ((G.supIncidenceFinset W gain) \ {s(loose,gain)}) ((G.supIncidenceFinset W loose) \ {s(loose,gain)}) := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
  intro x hx
  let h_int := Finset.mem_inter.mp hx
  let h_gain := Finset.mem_sdiff.mp h_int.left
  let h_loose := Finset.mem_sdiff.mp h_int.right
  have h_loose_inc : x ∈ G.incidenceFinset loose :=
  ((SimpleGraph.mem_supIncidenceFinset (W := W) (v := loose) (e := x)).mp h_loose.left).1
  have h_gain_inc : x ∈ G.incidenceFinset gain :=
  ((SimpleGraph.mem_supIncidenceFinset (W := W) (v := gain) (e := x)).mp h_gain.left).1
  have h_both : loose ∈ x ∧ gain ∈ x := ⟨helper_gain_mem G x h_loose_inc, helper_gain_mem G x h_gain_inc⟩
  apply h_gain.2
  rw [mem_singleton]
  apply Sym2.eq_of_ne_mem h_neq h_both.2 h_both.1
  · apply Sym2.mem_mk_right
  · apply Sym2.mem_mk_left

/-- Using `disjoint_supported_incidence` defines the disjoint union of the supported incidence sets of gain (without edge (gain,loose))
and that of loose (without edge (gain, loose)).-/
noncomputable
def incidence_loose_gain (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) : Finset (Sym2 α) :=
  disjUnion
    ((G.supIncidenceFinset W gain) \ {s(loose,gain)})
    ((G.supIncidenceFinset W loose) \ {s(loose,gain)})
    (disjoint_supported_incidence G W loose gain h_neq)

/-- shows that the set incidence_loose_gain is disjoint from the singleton s(loose, gain) -/
lemma disjoint_inci_singleton (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  Disjoint (incidence_loose_gain G W loose gain h_neq) {s(loose,gain)} := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
  intro x
  rw [Finset.mem_inter]
  rintro ⟨x_in_inci, x_in_singleton⟩
  rw [Finset.mem_singleton] at x_in_singleton
  subst x_in_singleton
  rw [incidence_loose_gain, Finset.mem_disjUnion] at x_in_inci
  cases x_in_inci
  case inl leftMem =>
    rw [Finset.mem_sdiff] at leftMem
    exact leftMem.2 (Finset.mem_singleton_self _)
  case inr rightMem =>
    rw [Finset.mem_sdiff] at rightMem
    exact rightMem.2 (Finset.mem_singleton_self _)

/-- Extends incidence_loose_gain by taking its disjoint union with s(loose,gain) (using `disjoint_inci_singleton`)-/
noncomputable
def inci_loose_gain_full (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) : Finset (Sym2 α) :=
  disjUnion
    (incidence_loose_gain G W loose gain h_neq) {s(loose,gain)}
    (disjoint_inci_singleton G W loose gain h_neq)

/-- Shows that if gain and loose are adjacent (and their weights are positive), then the supported edge set can be
decomposed as a disjoint union of `inci_loose_gain_full` and its complement-/
lemma supported_edge_partition (W : FunToMax G) (loose gain : α) (h_adj : G.Adj gain loose) (h_supp : W.w loose > 0 ∧ W.w gain > 0) :
  G.supEdgeFinset W =
  disjUnion (inci_loose_gain_full G W loose gain (G.ne_of_adj h_adj))
  (G.supEdgeFinset W \ (inci_loose_gain_full G W loose gain (G.ne_of_adj h_adj))) (disjoint_sdiff) := by
  rw [Finset.disjUnion_eq_union]
  ext e
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_coe]
  apply Iff.intro
  · intro he
    by_cases hin : e ∈ inci_loose_gain_full G W loose gain (G.ne_of_adj h_adj)
    · exact Or.inl hin
    · right
      constructor
      · exact he
      · exact hin
  · intro he
    cases he with
    | inl h_in =>
      unfold supEdgeFinset
      unfold inci_loose_gain_full incidence_loose_gain supIncidenceFinset at h_in
      rcases Finset.mem_disjUnion.mp h_in with (h_left | h_rest)
      · rcases Finset.mem_disjUnion.mp h_left with (h_gain_branch | h_loose_branch)
        · rcases Finset.mem_sdiff.mp h_gain_branch with ⟨h_gain, h_not⟩
          have h_incid : e ∈ G.incidenceFinset gain := (Finset.mem_filter.mp h_gain).1
          exact mem_filter.mpr ⟨incidenceFinset_subset G gain h_incid, (Finset.mem_filter.mp h_gain).2⟩
        · rcases Finset.mem_sdiff.mp h_loose_branch with ⟨h_loose, h_not⟩
          have h_incid := (Finset.mem_filter.mp h_loose).1
          exact mem_filter.mpr ⟨incidenceFinset_subset G loose h_incid, (Finset.mem_filter.mp h_loose).2⟩
      · rw[mem_singleton] at h_rest
        subst h_rest
        apply mem_filter.mpr
        constructor
        · rw [mem_edgeFinset]
          rw [← SimpleGraph.adj_comm] at h_adj
          rcases (@edge_mem_iff α G _ _).mp h_adj with ⟨e, he, heq⟩
          have h_eq : s(loose, gain) = e := by rw [heq]
          rw [h_eq]
          exact he
        · rw [Sym2.inSupport_explicit]; exact h_supp
    | inr h =>
      exact h.1

/-- Using `disjoint_supported_incidence` `disjoint_inci_singleton` `supported_edge_partition`,
decomposes the sum of edge values over the supported set of W into:
- supported incidence set of gain (withouth s(loose,gain))
- supported incidence set of loose (withouth s(loose,gain))
- the edge (loose,gain)
- other edges
-/
lemma supported_sum_split (W : FunToMax G) (loose gain : α) (h_adj : G.Adj gain loose) (h_supp : W.w loose > 0 ∧ W.w gain > 0) :
  ∑ e∈G.supEdgeFinset W, vp W.w e =
    ((∑ e∈((G.supIncidenceFinset W gain) \ {s(loose,gain)}) , vp W.w e +
      ∑ e∈((G.supIncidenceFinset W loose) \ {s(loose,gain)}) , vp W.w e) +
     ∑ e∈{s(loose,gain)}, vp W.w e) +
    ∑ e∈(G.supEdgeFinset W \ (inci_loose_gain_full G W loose gain (G.ne_of_adj h_adj))), vp W.w e := by
  rw [supported_edge_partition G W loose gain h_adj h_supp]
  rw [Finset.sum_disjUnion disjoint_sdiff]
  rw [inci_loose_gain_full, Finset.disjUnion_eq_union]
  rw [Finset.sum_union (disjoint_inci_singleton G W loose gain (G.ne_of_adj h_adj))]
  rw [incidence_loose_gain, Finset.disjUnion_eq_union]
  rw [Finset.sum_union (disjoint_supported_incidence G W loose gain (G.ne_of_adj h_adj))]
  rw [Finset.disjUnion_eq_union]
  rw [Finset.union_sdiff_of_subset]
  intro e eMem
  rw [Finset.mem_union, Finset.mem_union, or_assoc] at eMem
  cases eMem with
  | inl memGain =>
    rw [Finset.mem_sdiff] at memGain
    rcases memGain with ⟨memFiltered, _notSingleton⟩
    rw [mem_supIncidenceFinset] at memFiltered
    rcases memFiltered with ⟨h_incid, h_inSupp⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact incidenceFinset_subset G gain h_incid
    · exact h_inSupp
  | inr or =>
    cases or with
    | inl memLoose =>
      rw [Finset.mem_sdiff] at memLoose
      rcases memLoose with ⟨memFiltered, _notSingleton⟩
      rw [mem_supIncidenceFinset] at memFiltered
      rcases memFiltered with ⟨h_incid, h_inSupp⟩
      apply mem_filter.mpr
      constructor
      · exact incidenceFinset_subset G loose h_incid
      · exact h_inSupp
    | inr memSingleton =>
      apply Finset.mem_filter.mpr
      constructor
      · rw [mem_edgeFinset]
        rw [Finset.mem_singleton] at memSingleton
        subst memSingleton
        rw [adj_comm] at h_adj
        exact h_adj
      · rw [Finset.mem_singleton] at memSingleton
        subst memSingleton
        apply Sym2.inSupport_rec
        intro x slg
        apply pos_iff_ne_zero.mpr
        intro w0
        have hx_or : x = loose ∨ x = gain := Sym2.mem_iff.mp slg
        let mem_in_filter := s(loose, gain) ∈ G.edgeFinset.filter (Sym2.inSupport G W)
        have hInSup : s(loose, gain).inSupport G W := by
          rw [Sym2.inSupport_explicit]
          exact h_supp
        cases hx_or with
        | inl hxl =>
          rw [hxl] at w0
          rw [Sym2.inSupport_explicit] at hInSup
          exact (pos_iff_ne_zero.mp hInSup.left) w0
        | inr hxg =>
          rw [hxg] at w0
          rw [Sym2.inSupport_explicit] at hInSup
          exact (pos_iff_ne_zero.mp hInSup.right) w0

/-- Shows that the total edge value obtained by summing vp W.w e over the whole edge set is the
same as the sum taken only over the supported edges, (those in supEdgeFinset).  -/
lemma sum_over_support (W : FunToMax G):
  ∑ e∈G.edgeFinset, vp W.w e = ∑ e∈G.supEdgeFinset W, vp W.w e := by
  rw [eq_comm]
  apply sum_subset
  · unfold supEdgeFinset
    apply filter_subset
  · intro x xInEdges xNotSup
    rw [mem_supEdgeFinset] at xNotSup
    apply Sym2.notinSupport
    intro supp
    apply xNotSup
    exact ⟨xInEdges, supp⟩

/-- Given an edge e in the set difference of the supported incidence set of gain
(and not in a  dummy edge), this lemma shows that the value vp of e factors as the product
of the weight of gain and the weight of the “other” vertex of the edge -/
lemma vp_gain_edge (W : FunToMax G) (gain : α) (dummy : Sym2 α)
  (e : Sym2 α) (he : e ∈ ((G.supIncidenceFinset W gain) \ {dummy})) :
  vp W.w e = (W.w gain) * (W.w (Sym2.Mem.other (helper_gain_mem G e (G.small_helpI (in_sdiff_left he))))) := by
  rw [Finset.mem_sdiff] at he
  convert (gain_edge_decomp G W gain e (G.small_helpI he.1))

/-- Shows that the sum of the edge values of the supported incidence set of gain with a dummy edge removed
can be expressed  as the product of gain's weight and the sum over the incidence set of the weights on the
"other" vertices without the dummy edge (Proved using `vp_gain_edge`) -/
lemma sum_gain_factor (W : FunToMax G) (gain : α) (dummy : Sym2 α) :
    ∑ e∈((G.supIncidenceFinset W gain) \ {dummy}), vp W.w e =
    (W.w gain) * ∑ e∈((G.supIncidenceFinset W gain) \ {dummy}).attach, W.w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))) := by
  rw [mul_sum]
  rw [← sum_attach]
  apply sum_congr
  · rfl
  · intro x _
    apply vp_gain_edge _ _ gain dummy _ x.prop

/-- Proves that for each edge in the supported incidence set of gain (with s(loose,gain) 1
removed) the weight of the "other" vertex remains unchanged under `Enhance` transformation-/
lemma Enhance_other_at_gain_unchanged (W : FunToMax G) (loose: α) (gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ e ∈ ((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach,
    (Enhance G W loose gain h_lt ε epos elt).w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))) =
    W.w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))) := by
  intro e he
  let x := Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))
  dsimp [Enhance] at *
  have h_loose_nonneg : 0 ≤ W.w loose := (W.w loose).prop
  have h_gain_le : W.w gain ≤ W.w loose := le_of_lt h_lt
  have h_tec : ε ≤ W.w loose := by
            replace elt := add_le_of_le_tsub_left_of_le (le_of_lt h_lt) (le_of_lt elt)
            apply le_trans (le_add_of_nonneg_left (W.w gain).prop) elt
  split_ifs with h_xloose h_xgain
  · exfalso
    have := Sym2.other_spec (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))
    rw [h_xloose] at this
    have tmp := e.prop
    rw [mem_sdiff] at tmp
    apply tmp.2
    rw [mem_singleton, ← this]
    exact Sym2.eq_swap
  · exfalso
    apply Sym2.other_ne _ _ h_xgain
    have dummy := e.prop
    revert dummy
    apply @Sym2.inductionOn _ (fun e => e ∈ G.supIncidenceFinset W gain \ {s(loose, gain)} → ¬(e).IsDiag) e.val
    intro x y useful
    rw [Sym2.mk_isDiag_iff]
    apply G.ne_of_adj
    rw [Finset.mem_sdiff] at useful
    rcases useful with ⟨supInc, _⟩
    rw [mem_supIncidenceFinset] at supInc
    rcases supInc with ⟨incid, _support⟩
    rw [mem_incidenceFinset] at incid
    rcases incid with ⟨inEdges, _memXY⟩
    rw[mem_edgeSet] at *
    exact inEdges
  · rfl

/-- ) Shows that for every edge in the supported incidence set of `loose`(without s(loose,gain)),
the value of the other vertex remains unchanged under `Enhance` transformation-/
lemma Enhance_other_at_loose_unchanged (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach,
    (Enhance G W loose gain h_lt ε epos elt).w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))) =
    W.w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))) := by
  intro e he
  let x := Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))
  dsimp [Enhance] at *
  have h_loose_nonneg : 0 ≤ W.w loose := (W.w loose).prop
  have h_gain_le : W.w gain ≤ W.w loose := le_of_lt h_lt
  have h_tec : ε ≤ W.w loose := by
            replace elt := add_le_of_le_tsub_left_of_le (le_of_lt h_lt) (le_of_lt elt)
            apply le_trans (le_add_of_nonneg_left (W.w gain).prop) elt
  split_ifs with h_xloose h_xgain
  · exfalso
    apply Sym2.other_ne _ _ h_xloose
    have dummy := e.prop
    revert dummy
    apply @Sym2.inductionOn _ (fun e => e ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} → ¬(e).IsDiag) e.val
    intro x y useful
    rw [Sym2.mk_isDiag_iff]
    apply G.ne_of_adj
    rw [Finset.mem_sdiff] at useful
    rcases useful with ⟨supInc, _⟩
    rw [mem_supIncidenceFinset] at supInc
    rcases supInc with ⟨incid, _support⟩
    rw [mem_incidenceFinset] at incid
    rcases incid with ⟨inEdges, _memXY⟩
    rw[mem_edgeSet] at *
    exact inEdges
  · exfalso
    have := Sym2.other_spec (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))
    rw [h_xgain] at this
    have tmp := e.prop
    rw [mem_sdiff] at tmp
    apply tmp.2
    rw [mem_singleton, ← this]
  · rfl

/-- Shows that the sum over the supported incidence set of gain (without s(loose,gain)) after
`Enhance` transformation, equals the original sum plus ε times the sum over the gain-attached
incident set-/
lemma Enhance_gain_sum (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∑ e∈((G.supIncidenceFinset W gain) \ {s(loose,gain)}), vp (Enhance G W loose gain h_lt ε epos elt).w e =
  ∑ e∈((G.supIncidenceFinset W gain) \ {s(loose,gain)}), vp W.w e +
  ε * ∑ e∈((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))) := by
  rw [mul_sum, ← sum_attach]
  let S := G.supIncidenceFinset W gain \ {s(loose, gain)}
  rw [← Finset.sum_attach S (λ e => vp W.w e)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have dummy := x.prop
  revert dummy
  have tec : (↑x ∈ G.supIncidenceFinset W gain \ {s(loose, gain)} →
    vp (Enhance G W loose gain h_lt ε epos elt).w ↑x = vp W.w ↑x + ε * W.w (Sym2.Mem.other (helper_gain_mem G (↑x) (small_helpI G (in_sdiff_left (Subtype.prop x))))))
    = (fun X => ((HX : X ∈ G.supIncidenceFinset W gain \ {s(loose, gain)}) →
    vp (Enhance G W loose gain h_lt ε epos elt).w X = vp W.w X + ε * W.w (Sym2.Mem.other (helper_gain_mem G (X) (small_helpI G (in_sdiff_left (HX)))))))
      ↑x := by
    dsimp
  rw [tec]
  clear tec
  dsimp
  apply @Sym2.inductionOn α (fun X => ∀ (HX : X ∈ G.supIncidenceFinset W gain \ {s(loose, gain)}), vp (Enhance G W loose gain h_lt ε epos elt).w X = vp W.w X + ε * W.w (Sym2.Mem.other (helper_gain_mem G (X) (small_helpI G (in_sdiff_left HX))))) ↑x
  intro a b hab
  dsimp! [vp]
  rw [mem_sdiff, not_mem_singleton, mem_supIncidenceFinset,mem_incidenceFinset, mk'_mem_incidenceSet_iff] at hab
  obtain ⟨⟨⟨abAdj,Q⟩,abSupp⟩,abnot⟩ := hab
  cases' Q with Q Q
  · dsimp [Enhance]
    rw [if_neg (show ¬ a = loose by intro con ; rw [Q,← con] at h_lt ; apply lt_irrefl _ h_lt)]
    rw [if_pos Q.symm]
    rw [if_neg (show ¬ b = loose by intro con ;rw [Q,← con] at abnot ; apply abnot ; apply Sym2.eq_swap)]
    rw [if_neg (show ¬ b = gain by intro con ;rw [← Q,← con] at abAdj ; apply G.ne_of_adj abAdj ; rfl)]
    rw [add_mul]
    have tec : Sym2.Mem.other (helper_gain_mem G s(a, b) (small_helpI G (in_sdiff_left hab))) = b := by
      have := Sym2.other_spec (helper_gain_mem G s(a, b) (small_helpI G (in_sdiff_left hab)))
      rw [Sym2.mk_eq_mk_iff] at this
      cases' this with q q
      · rw [Prod.ext_iff] at q
        exact q.2
      · rw [Prod.ext_iff] at q
        dsimp at q
        exfalso
        apply G.ne_of_adj abAdj
        rw [← Q, ← q.1]
    rw [tec, Q]
  · dsimp [Enhance]
    rw [if_neg (show ¬ b = loose by intro con ; rw [Q,← con] at h_lt ; apply lt_irrefl _ h_lt)]
    rw [if_pos Q.symm]
    rw [if_neg (show ¬ a = loose by intro con ;rw [Q,← con] at abnot ; apply abnot ; rfl)]
    rw [if_neg (show ¬ a = gain by intro con ;rw [← Q,← con] at abAdj ; apply G.ne_of_adj abAdj ; rfl)]
    rw [mul_add]
    have tec : Sym2.Mem.other (helper_gain_mem G s(a, b) (small_helpI G (in_sdiff_left hab))) = a := by
      have := Sym2.other_spec (helper_gain_mem G s(a, b) (small_helpI G (in_sdiff_left hab)))
      rw [Sym2.mk_eq_mk_iff] at this
      cases' this with q q
      · rw [Prod.ext_iff] at q
        dsimp at q
        exfalso
        apply G.ne_of_adj abAdj
        rw [← Q, ← q.1]
      · rw [Prod.ext_iff] at q
        exact q.2
    rw[tec, Q]; rw [mul_comm (W.w a) ε]

/-- Helper: provides a bound: for any edge in the supported incidence set of `loose` (without s(loose,gain)), the
product of ε and the weight of the "other" vertex is bounded by the edge's value -/
lemma epsilon_weight_bound (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ e ∈ (G.supIncidenceFinset W loose \ {s(loose, gain)}).attach,
    ε * (W.w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop))))) ≤ vp W.w e := by
  intro x _
  have dummy := x.prop
  revert dummy
  have tec : (↑x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} →
    ε * W.w (Sym2.Mem.other (helper_gain_mem G (↑x) (small_helpI G (in_sdiff_left (Subtype.prop x))))) ≤ vp W.w ↑x )
    = (fun X => ((HX : X ∈ G.supIncidenceFinset W loose \ {s(loose, gain)}) →
      ε * W.w (Sym2.Mem.other (helper_gain_mem G (X) (small_helpI G (in_sdiff_left (HX)))))≤ vp W.w X ))
      ↑x := by
    dsimp
  rw [tec]
  clear tec
  dsimp
  apply @Sym2.inductionOn α (fun X => ∀ (HX : X ∈ G.supIncidenceFinset W loose \ {s(loose, gain)}), ε * W.w (Sym2.Mem.other (helper_gain_mem G (X) (small_helpI G (in_sdiff_left (HX)))))≤ vp W.w X) ↑x
  intro a b hab
  dsimp [vp]
  rw [mem_sdiff, not_mem_singleton, mem_supIncidenceFinset,mem_incidenceFinset, mk'_mem_incidenceSet_iff] at hab
  obtain ⟨⟨⟨abAdj,Q⟩,abSupp⟩,abnot⟩ := hab
  have h_tec : ε ≤ W.w loose := by
            replace elt := add_le_of_le_tsub_left_of_le (le_of_lt h_lt) (le_of_lt elt)
            apply le_trans (le_add_of_nonneg_left (W.w gain).prop) elt
  cases' Q with Q Q
  · have tec : Sym2.Mem.other (helper_gain_mem G s(a, b) (small_helpI G (in_sdiff_left hab))) = b := by
      have := Sym2.other_spec (helper_gain_mem G s(a, b) (small_helpI G (in_sdiff_left hab)))
      rw [Sym2.mk_eq_mk_iff] at this
      cases' this with q q
      · rw [Prod.ext_iff] at q
        exact q.2
      · rw [Prod.ext_iff] at q
        dsimp at q
        exfalso
        apply G.ne_of_adj abAdj
        rw [← Q, ← q.1]
    rw[tec, mul_comm, mul_comm (W.w a)]; rw[Q] at h_tec
    exact mul_le_mul_of_nonneg_left h_tec (W.w b).prop
  · have tec : Sym2.Mem.other (helper_gain_mem G s(a, b) (small_helpI G (in_sdiff_left hab))) = a := by
      have := Sym2.other_spec (helper_gain_mem G s(a, b) (small_helpI G (in_sdiff_left hab)))
      rw [Sym2.mk_eq_mk_iff] at this
      cases' this with q q
      · rw [Prod.ext_iff] at q
        dsimp at q
        exfalso
        apply G.ne_of_adj abAdj
        rw [← Q, ← q.1]
      · rw [Prod.ext_iff] at q
        exact q.2
    rw[tec, mul_comm]; rw[Q] at h_tec
    exact mul_le_mul_of_nonneg_left h_tec (W.w a).prop

/-- Shows that the sum over the supported incidence set of loose (without s(loose,gain)) after `Enhance` transformation, equals
the original sum minus ε times the sum over the attached incident set of loose.-/
lemma Enhance_loose_sum (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∑ e∈((G.supIncidenceFinset W loose) \ {s(loose,gain)}), vp (Enhance G W loose gain h_lt ε epos elt).w e =
  ∑ e∈((G.supIncidenceFinset W loose) \ {s(loose,gain)}), vp W.w e -
  ε * ∑ e∈((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))) := by
  rw [mul_sum]
  have h_tec : ε ≤ W.w loose := by
    replace elt := add_le_of_le_tsub_left_of_le (le_of_lt h_lt) (le_of_lt elt)
    apply le_trans (le_add_of_nonneg_left (W.w gain).prop) elt
  nth_rewrite 2 [← sum_attach]
  rw [← sum_tsub_distrib _ (epsilon_weight_bound G W loose gain h_lt ε epos elt)]
  rw [← sum_attach]
  apply Finset.sum_congr rfl
  intro x hx
  have dummy := x.prop
  revert dummy
  have tec : (↑x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} →
    vp (Enhance G W loose gain h_lt ε epos elt).w ↑x = vp W.w ↑x - ε * W.w (Sym2.Mem.other (helper_gain_mem G (↑x) (small_helpI G (in_sdiff_left (Subtype.prop x))))))
    = (fun X => ((HX : X ∈ G.supIncidenceFinset W loose \ {s(loose, gain)}) →
    vp (Enhance G W loose gain h_lt ε epos elt).w X = vp W.w X - ε * W.w (Sym2.Mem.other (helper_gain_mem G (X) (small_helpI G (in_sdiff_left (HX)))))))
      ↑x := by
    dsimp
  rw [tec]
  clear tec
  dsimp
  apply @Sym2.inductionOn α (fun X => ∀ (HX : X ∈ G.supIncidenceFinset W loose \ {s(loose, gain)}),
    vp (Enhance G W loose gain h_lt ε epos elt).w X =
    vp W.w X - ε * W.w (Sym2.Mem.other (helper_gain_mem G (X) (small_helpI G (in_sdiff_left HX))))) ↑x
  intro a b hab
  dsimp! [vp]
  rw [mem_sdiff, not_mem_singleton, mem_supIncidenceFinset, mem_incidenceFinset, mk'_mem_incidenceSet_iff] at hab
  obtain ⟨⟨⟨abAdj, Q⟩, abSupp⟩, abnot⟩ := hab
  cases' Q with Q1 Q2
  · have nb : b ≠ loose := by
      intro h; subst h; subst Q1; exact (G.ne_of_adj abAdj) rfl
    have ng : b ≠ gain := by
      intro h; subst h;
      rw [Q1] at abnot
      exact abnot (Eq.refl (s(a, b)))
    dsimp [Enhance] at *
    subst Q1
    simp only [↓reduceIte, mul_ite, Sym2.other_eq_other']
    rw [if_neg nb, if_neg ng]
    have tec : Sym2.Mem.other' (helper_gain_mem G s(loose, b) (small_helpI G (in_sdiff_left hab))) = b := by
      have := Sym2.other_spec' (helper_gain_mem G s(loose, b) (small_helpI G (in_sdiff_left hab)))
      rw [Sym2.mk_eq_mk_iff] at this
      cases' this with q q
      · rw [Prod.ext_iff] at q
        exact q.2
      · rw [Prod.ext_iff] at q
        dsimp at q
        exfalso
        apply G.ne_of_adj abAdj
        exact q.1
    rw [tec]; rw [@tsub_mul]
  · have na : a ≠ loose := by
      intro h; subst h; subst Q2; exact (G.ne_of_adj abAdj) rfl
    have ng : a ≠ gain := by
      intro h; subst h;
      rw [Q2] at abnot; rw[←Sym2.eq_swap] at abnot
      exact abnot (Eq.refl (s(b, a)))
    dsimp [Enhance] at *
    subst Q2
    simp only [↓reduceIte, mul_ite, Sym2.other_eq_other']
    rw [if_neg na, if_neg ng]
    have tec : Sym2.Mem.other' (helper_gain_mem G s(a, loose) (small_helpI G (in_sdiff_left hab))) = a := by
      have := Sym2.other_spec' (helper_gain_mem G s(a, loose) (small_helpI G (in_sdiff_left hab)))
      rw [Sym2.mk_eq_mk_iff] at this
      cases' this with q q
      · rw [Prod.ext_iff] at q
        simp only [Prod.mk.injEq] at q
        obtain ⟨h1, h2⟩ := q
        simp [h1] at h2
        exact False.elim (na (id (Eq.symm h1)))
      · rw [Prod.ext_iff] at q
        simp only [Prod.mk.injEq] at q
        obtain ⟨h1, h2⟩ := q
        exact h2
    rw [tec]; rw [@mul_tsub]; rw[mul_comm ε  (W.w a)]

/- Provides a bijection between the supported incidence edges at `loose` (without s(loose, gain))
and the supported incidence edges at `gain` (without s(loose, gain)). -/
noncomputable
def the_bij (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (h_supp : W.w loose > 0 ∧ W.w gain > 0) :
  (e : { x // x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} }) → (e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach) → { x // x ∈ G.supIncidenceFinset W gain \ {s(loose, gain)} } :=
  fun e h =>
    ⟨(s(gain,(Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))))),
     (by
        rw [mem_sdiff, not_mem_singleton, mem_supIncidenceFinset,mem_incidenceFinset, mk'_mem_incidenceSet_iff]
        have tec := e.prop
        rw [mem_sdiff, not_mem_singleton, mem_supIncidenceFinset,mem_incidenceFinset] at tec
        obtain ⟨⟨⟨eAdj,Q⟩,eSupp⟩,enot⟩ := tec
        constructor
        · constructor
          · constructor
            · apply hc
              · simp only [gt_iff_lt, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
                exact h_supp.2
              · simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
                apply Sym2.inSupport_other
                exact eSupp
              · contrapose! enot
                have := Sym2.other_spec (helper_gain_mem G (↑e) (small_helpI G (in_sdiff_left (Subtype.prop e))) )
                rw [← this]
                rw [Sym2.mk_eq_mk_iff]
                left
                rw [Prod.ext_iff]
                dsimp
                exact ⟨rfl, enot.symm⟩
            · left ; rfl
          · dsimp [Sym2.inSupport]
            constructor
            · exact h_supp.2
            · apply Sym2.inSupport_other
              exact eSupp
        · intro con
          rw [Sym2.mk_eq_mk_iff] at con
          cases' con with q q
          · rw [Prod.ext_iff] at q
            dsimp at q
            exfalso
            rw [q.1] at h_lt
            apply lt_irrefl _ h_lt
          · rw [Prod.ext_iff] at q
            dsimp at q
            apply Sym2.other_ne _ _ q.2
            revert eAdj
            apply @Sym2.inductionOn α (fun e => e ∈ G.edgeSet → ¬(e).IsDiag)
            intro a b hab
            dsimp [Sym2.IsDiag]
            rw [mem_edgeSet] at hab
            apply G.ne_of_adj hab)⟩

/--
For every element e in the incidence set of loose (excluding s(loose, gain)),
 `the_bij` maps e into the attached part of the incidence finset of gain.
-/
lemma the_bij_maps (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (h_supp : W.w loose > 0 ∧ W.w gain > 0) :
    ∀ (e : { x // x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} })
      (he : e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach),
        (the_bij G W loose gain h_lt ε epos elt hc h_supp) e he ∈ ((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach := by
  intro e he
  apply mem_attach

/-- Injetcitivy of the_bij -/
lemma the_bij_inj (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (h_supp : W.w loose > 0 ∧ W.w gain > 0) :
    ∀ (a₁ : { x // x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} })
      (ha₁ : a₁ ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach)
      (a₂ : { x // x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} })
      (ha₂ : a₂ ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach),
      (the_bij G W loose gain h_lt ε epos elt hc h_supp) a₁ ha₁ = (the_bij G W loose gain h_lt ε epos elt hc h_supp) a₂ ha₂ →
      a₁ = a₂ := by
  intro a₁ ha₁ a₂ ha₂ h
  rcases a₁ with ⟨e₁, he₁⟩
  rcases a₂ with ⟨e₂, he₂⟩
  dsimp [the_bij] at  h
  injection h with h1
  simp [the_bij]
  have := Sym2.other_spec (the_bij.proof_1 G W loose gain ⟨e₁, he₁⟩)
  dsimp at this
  rw [← this]
  have that := Sym2.other_spec (the_bij.proof_1 G W loose gain ⟨e₂, he₂⟩)
  dsimp at that
  rw [← that]
  rw [Sym2.mk_eq_mk_iff] at *
  cases h1 with
  | inl h_eq =>
    left
    have h_snd : Sym2.Mem.other (the_bij.proof_1 G W loose gain ⟨e₁, he₁⟩) =
                Sym2.Mem.other (the_bij.proof_1 G W loose gain ⟨e₂, he₂⟩) :=
      congrArg Prod.snd h_eq
    exact congrArg (fun w => (loose, w)) h_snd
  | inr swapped =>
    right
    exfalso
    dsimp at swapped
    rw [Prod.ext_iff] at swapped
    dsimp at swapped
    rw [← swapped.left] at that
    rw [mem_sdiff] at he₂
    apply he₂.2
    rw [← that]
    apply mem_singleton_self

/-- Surjectivity of the_bij -/
lemma the_bij_surj (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (h_supp : W.w loose > 0 ∧ W.w gain > 0) :
    ∀ b ∈ ((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach,
      ∃ a, ∃ (ha : a ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach),
        (the_bij G W loose gain h_lt ε epos elt hc h_supp) a ha = b := by
  intro b hb
  rcases b with ⟨e, he⟩
  let x := Sym2.Mem.other (helper_gain_mem G e (G.small_helpI (in_sdiff_left he)))
  have that := Sym2.other_spec (helper_gain_mem G e (G.small_helpI (in_sdiff_left he)))
  have hx : s(loose,x) ∈ (G.supIncidenceFinset W loose \ {s(loose, gain)}) := by
    rw [mem_sdiff, mem_supIncidenceFinset]
    split_ands
    · rw [mem_sdiff] at he
      obtain ⟨he_in_sup, he_not_eq⟩ := he
      rw [mem_supIncidenceFinset] at he_in_sup
      obtain ⟨he_in_inc, he_support⟩ := he_in_sup
      rw [mem_incidenceFinset] at he_in_inc
      obtain ⟨he_in_edges, ge⟩ := he_in_inc
      rw [← that] at he_in_edges
      rw [mem_incidenceFinset]
      rw [mem_incidenceSet]
      have e_in_edges : e ∈ G.edgeSet := that ▸ he_in_edges
      have s_gx_in : s(gain, x) ∈ G.edgeSet := that ▸ e_in_edges
      have gain_adj_x : G.Adj gain x := G.mem_edgeSet.mp s_gx_in
      apply hc
      · exact Finset.mem_filter.mpr (⟨Finset.mem_univ loose, h_supp.1⟩)
      · have sgx_support : s(gain, x).inSupport G W := that.symm ▸ he_support
        rw [Sym2.inSupport_explicit] at sgx_support
        exact Finset.mem_filter.mpr (⟨Finset.mem_univ x, sgx_support.2⟩)
      · intro h_eq
        let eq_g := congrArg (fun z => s(gain, z)) h_eq
        have eq_slg : s(loose, gain) = e := by
          calc
            s(loose, gain)
              = s(gain, loose)    := by exact Sym2.eq_swap
            _ = s(gain, x)        := by rw [h_eq]
            _ = e                 := that
        exfalso
        apply he_not_eq
        exact mem_singleton.mpr (id (Eq.symm eq_slg))
    · dsimp
      rw [mem_sdiff] at he
      obtain ⟨he_in_sup, _⟩ := he
      rw [mem_supIncidenceFinset] at he_in_sup
      obtain ⟨_, he_support⟩ := he_in_sup
      rw [Sym2.inSupport] at he_support
      rw [← that] at he_support
      obtain ⟨h1, h2⟩ := he_support
      have hx_pos : W.w x > 0 := h2
      exact h_supp.1
    · dsimp
      apply Sym2.inSupport_mem G W (Sym2.other_mem (helper_gain_mem G e (G.small_helpI (in_sdiff_left he))))
      rw [mem_sdiff, mem_supIncidenceFinset] at he
      exact he.1.2
    · intro s
      simp at s
      cases s with
      | inl xEqGain =>
        have eq_sgg : s(gain, x) = s(gain, gain) :=
          congrArg (fun z => s(gain, z)) xEqGain
        have eq_loop : e = s(gain, gain) :=
          Eq.trans that.symm eq_sgg
        rw [Finset.mem_sdiff] at he
        let ⟨he_in, _he_not_slg⟩ := he
        dsimp [SimpleGraph.supIncidenceFinset] at he_in
        rw [Finset.mem_filter] at he_in
        rcases he_in with ⟨incid, _inSupp⟩
        rw [SimpleGraph.mem_incidenceFinset] at incid
        rcases incid with ⟨e_in_eset, gain_in_e⟩
        have s_gg_in : s(gain, gain) ∈ G.edgeSet := eq_loop ▸ e_in_eset
        let loopAdj := G.mem_edgeSet.mp s_gg_in
        apply G.ne_of_adj loopAdj
        rfl
      | inr h =>
        exfalso
        let ⟨looseEqGain, _xEqLoose⟩ := h
        rw [looseEqGain] at h_lt
        apply lt_irrefl (W.w gain)
        exact h_lt
  use ⟨s(loose,x), hx⟩
  use (by apply mem_attach)
  dsimp [the_bij]
  congr
  have := Sym2.other_spec (the_bij.proof_1 G W loose gain ⟨s(loose, x), hx⟩ )
  dsimp at this
  rw [Sym2.mk_eq_mk_iff] at this
  cases' this with q q
  · rw [Prod.ext_iff] at q
    dsimp at q
    rw [q.2]
    exact that
  · dsimp at q
    rw [Prod.ext_iff] at q
    dsimp at q
    exfalso
    apply G.ne_of_adj _ q.1
    have inc : s(loose, x) ∈ G.edgeSet := by
      rw [mem_sdiff] at hx
      let ⟨hx_in, _⟩ := hx
      rw [mem_supIncidenceFinset] at hx_in
      let ⟨incid, _⟩ := hx_in
      rw [mem_incidenceFinset] at incid
      let ⟨inEdges, _looseIn⟩ := incid
      exact inEdges
    exact inc

/-- Shows that `the_bij` preserves the "other" weight: for any edge from the supported incidence set of loose, the weight
at the "other" vertex equals that in its image uneder the bijection-/
lemma the_bij_same (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (h_supp : W.w loose > 0 ∧ W.w gain > 0) :
  ∀ (e : { x // x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} })
      (he : e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach) ,
      (W.w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))))
      = (fun e => W.w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))))
        ((the_bij G W loose gain h_lt ε epos elt hc h_supp) e he) := by
  dsimp[Enhance]
  intro e he
  congr 1
  have h_right := Sym2.other_spec (helper_gain_mem G (↑(the_bij G W loose gain h_lt ε epos elt hc h_supp e he))
    (small_helpI G (in_sdiff_left (Subtype.prop (the_bij G W loose gain h_lt ε epos elt hc h_supp e he)))))
  dsimp [the_bij] at h_right
  have pi : Sym2.Mem.other (helper_gain_mem G s(gain, Sym2.Mem.other (the_bij.proof_1 G W loose gain e))
    (small_helpI G
      (in_sdiff_left
        (Subtype.prop
          ⟨s(gain, Sym2.Mem.other (the_bij.proof_1 G W loose gain e)), the_bij.proof_2 G W loose gain h_lt hc h_supp e⟩))))
    = Sym2.Mem.other (helper_gain_mem G (↑(the_bij G W loose gain h_lt ε epos elt hc h_supp e he))
      (small_helpI G (in_sdiff_left (Subtype.prop (the_bij G W loose gain h_lt ε epos elt hc h_supp e he))))) := by congr
  rw [← pi]; clear pi
  have pi : Sym2.Mem.other (helper_gain_mem G (↑e) (small_helpI G (in_sdiff_left (Subtype.prop e))) )
    = Sym2.Mem.other (the_bij.proof_1 G W loose gain e) := by congr
  nth_rewrite 1 [pi]
  clear pi
  rw [Sym2.mk_eq_mk_iff] at h_right
  cases' h_right with q q
  · rw [Prod.ext_iff] at q
    dsimp at q
    exact q.2.symm
  · rw [Prod.ext_iff] at q
    dsimp at q
    have problem := Sym2.other_spec (the_bij.proof_1 G W loose gain e)
    rw [← q.1] at problem
    have ohoh := e.prop
    rw [mem_sdiff] at ohoh
    exfalso
    apply ohoh.2
    rw [mem_singleton]
    exact problem.symm

/-- Uses `the_bij` to show that the total sum of the weights, on the "other" vertices in the supported incidence
set, is preserved when switching fom `loose` to `gain`-/
lemma Enhance_sum_loose_gain_equal (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (h_supp : W.w loose > 0 ∧ W.w gain > 0) :
  ∑ e∈((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))) =
  ∑ e∈((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (helper_gain_mem G e.val (G.small_helpI (in_sdiff_left e.prop)))) :=
  by
  have h_bij : ∀ e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach,
    (the_bij G W loose gain h_lt ε epos elt hc h_supp) e (mem_attach _ e) ∈ ((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach :=
    fun e he => the_bij_maps G W loose gain h_lt ε epos elt hc h_supp e he
  apply Finset.sum_bij (the_bij G W loose gain h_lt ε epos elt hc h_supp)
    (the_bij_maps G W loose gain h_lt ε epos elt hc h_supp)
    (the_bij_inj G W loose gain h_lt ε epos elt hc h_supp)
    (the_bij_surj G W loose gain h_lt ε epos elt hc h_supp)
    (the_bij_same G W loose gain h_lt ε epos elt hc h_supp)

/-- States that for every edge in the supported edges without `inci_loose_gain_full`,
the edge value remains unchanged after Enhance`-/
lemma Enhance_vp_complement_unchanged (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ e ∈ (G.supEdgeFinset W \ (inci_loose_gain_full G W loose gain (neq_of_W_lt G h_lt))),
    vp (Enhance G W loose gain h_lt ε epos elt).w e = vp W.w e := by
  intro e
  apply @Sym2.inductionOn α (fun e => e ∈ G.supEdgeFinset W \ inci_loose_gain_full G W loose gain _ → vp (Enhance G W loose gain h_lt ε epos elt).w e = vp W.w e)
  intro x y hxy
  dsimp [vp, Enhance]
  simp_rw [mem_sdiff, inci_loose_gain_full, incidence_loose_gain, mem_supEdgeFinset, mem_edgeFinset, mem_edgeSet] at hxy
  split_ifs with hx hy hz hw hu hv hh ho
  · exfalso
    apply @G.ne_of_adj _ x y hxy.1.1
    rw [hx,hy]
  · exfalso
    apply hxy.2
    rw [mem_disjUnion]; right; rw [hx,hz]; apply mem_singleton_self
  · exfalso
    apply hxy.2
    rw [mem_disjUnion]; left; rw [mem_disjUnion]; right; rw [mem_sdiff, mem_supIncidenceFinset]
    refine' ⟨⟨_,hxy.1.2⟩,_⟩
    · rw [hx]
      subst hx
      rw [mem_incidenceFinset, mem_incidenceSet]; exact hxy.1.1
    · rw [hx]
      intro h
      rw [mem_singleton] at h
      apply hz
      rw [Sym2.eq_iff] at h
      cases' h with h1 h2
      · exact h1.2
      · rcases h2 with ⟨hlg, hyl⟩
        rw [hyl, hlg]
  · exfalso
    apply hxy.2
    rw [mem_disjUnion]; right; rw[hw, hu, @Sym2.eq_swap, @mem_singleton]
  · exfalso
    apply @G.ne_of_adj _ x y hxy.1.1
    rw [hw, hv]
  · exfalso
    apply hxy.2
    rw [mem_disjUnion]; left; rw [mem_disjUnion]; left; rw [mem_sdiff, mem_supIncidenceFinset]
    refine' ⟨⟨_, hxy.1.2⟩, _⟩
    · rw [hw]
      subst hw
      rw [mem_incidenceFinset]
      rw [mem_incidenceSet]
      exact hxy.1.1
    · rw [hw]
      intro h
      rw [mem_singleton] at h
      apply hv
      rw [Sym2.eq_iff] at h
      cases' h with h1 h2
      · exact h1.2
      · rcases h2 with ⟨h3, h4⟩
        rw [h3, h4]
        exact False.elim (hu h4)
  · exfalso
    apply hxy.2; rw [mem_disjUnion]; left; rw [mem_disjUnion]; right; rw [mem_sdiff, mem_supIncidenceFinset]
    refine' ⟨⟨_, hxy.1.2⟩, _⟩
    · rw [hh]
      subst hh; rw [mem_incidenceFinset, @mk'_mem_incidenceSet_right_iff]; exact hxy.1.1
    · rw [hh]
      intro h
      rw [mem_singleton] at h
      apply hx
      rw [Sym2.eq_iff] at h
      cases' h with h1 h2
      · exact h1.1
      · rcases h2 with ⟨h1, h2⟩
        rw [h2, h1]
        exact False.elim (hw h1)
  · exfalso
    apply hxy.2
    rw [mem_disjUnion]; left;rw [mem_disjUnion]; left
    rw [mem_sdiff, mem_supIncidenceFinset]
    refine' ⟨⟨_, hxy.1.2⟩, _⟩
    · rw [ho]
      subst ho; rw [mem_incidenceFinset, @mk'_mem_incidenceSet_right_iff]; exact hxy.1.1
    · rw [ho]
      intro h
      rw [mem_singleton] at h
      apply hw
      rw [Sym2.eq_iff] at h
      cases' h with h1 h2
      · exfalso
        rcases h1 with ⟨hl, _⟩
        apply hx; exact hl
      · rcases h2 with ⟨h1, h2⟩
        rw [h2, h1]
        exact h2
  · rfl

/-- Shows that, for the edges in the  graph's support not in the set
`inci_loose_gain_full`, the total sum of edge values remains unchanged under `Enhance`. -/
lemma Enhance_sum_complement_unchanged (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∑ e∈(G.supEdgeFinset W \ (inci_loose_gain_full G W loose gain (neq_of_W_lt G h_lt))), vp (Enhance G W loose gain h_lt ε epos elt).w e =
  ∑ e∈(G.supEdgeFinset W \ (inci_loose_gain_full G W loose gain (neq_of_W_lt G h_lt))), vp W.w e := by
  apply Finset.sum_congr rfl
  intro e
  apply @Sym2.inductionOn _ (fun e => e ∈ G.supEdgeFinset W \ inci_loose_gain_full G W loose gain (neq_of_W_lt G h_lt) → vp (Enhance G W loose gain h_lt ε epos elt).w e = vp W.w e)
  intro x y he
  dsimp [Enhance]
  rw [mem_sdiff, inci_loose_gain_full] at he
  have hg : s(x,y) ∉ (G.supIncidenceFinset W gain) := by
    intro con
    have tec : s(x, y) ∉ ({s(loose, gain)} : Finset (Sym2 α)) :=
      by intro no ; apply he.2 ; rw [mem_disjUnion] ; right ; exact no
    have : s(x,y) ∈ (incidence_loose_gain G W loose gain (neq_of_W_lt G h_lt)) :=
      by dsimp [incidence_loose_gain] ; rw [mem_disjUnion] ; left ; rw [mem_sdiff] ; exact ⟨con,tec⟩
    apply he.2 ; rw [mem_disjUnion] ; left ; exact this
  have hl : s(x,y) ∉ (G.supIncidenceFinset W loose) := by
    intro con
    have tec : s(x, y) ∉ ({s(loose, gain)} : Finset (Sym2 α)) :=
      by intro no ; apply he.2 ; rw [mem_disjUnion] ; right ; exact no
    have : s(x,y) ∈ incidence_loose_gain G W loose gain (neq_of_W_lt G h_lt) := by
      dsimp [incidence_loose_gain]; rw [mem_disjUnion]; right; rw [mem_sdiff]; exact ⟨con, tec⟩
    apply he.2; rw [mem_disjUnion]; left; exact this
  have x_ne_loose : x ≠ loose := by
    intro h
    apply hl
    rw [h]
    apply Finset.mem_filter.mpr
    constructor
    · rw[h] at he
      dsimp [supEdgeFinset, supIncidenceFinset] at he
      have : s(loose, y) ∈ G.edgeFinset := (Finset.mem_filter.mp he.1).1
      rw [SimpleGraph.incidenceFinset]
      rw [Set.mem_toFinset]
      constructor
      · exact mem_edgeFinset.mp this
      · exact Sym2.mem_mk_left loose y
    · rw [← h]; exact (Finset.mem_filter.mp he.left).right
  have x_ne_gain : x ≠ gain := by
    intro h
    apply hg
    rw [h]
    apply Finset.mem_filter.mpr
    constructor
    · rw [h] at he
      dsimp [SimpleGraph.supEdgeFinset, SimpleGraph.supIncidenceFinset] at he
      have : s(gain, y) ∈ G.edgeFinset := (Finset.mem_filter.mp he.1).1
      rw [SimpleGraph.incidenceFinset]
      rw [Set.mem_toFinset]
      constructor
      · exact mem_edgeFinset.mp this
      · exact Sym2.mem_mk_left gain y
    · rw [← h]
      exact (Finset.mem_filter.mp he.left).right
  have y_ne_loose : y ≠ loose := by
    intro h
    apply hl
    rw [h] at he
    apply Finset.mem_filter.mpr
    constructor
    · dsimp [SimpleGraph.supEdgeFinset, SimpleGraph.supIncidenceFinset] at he
      have : s(x, loose) ∈ G.edgeFinset := (Finset.mem_filter.mp he.1).1
      rw [SimpleGraph.incidenceFinset]
      rw [Set.mem_toFinset]
      constructor
      · rw[h]; exact mem_edgeFinset.mp this
      · rw[h]; exact Sym2.mem_mk_right x loose
    · rw [h]; exact (Finset.mem_filter.mp he.left).right
  have y_ne_gain : y ≠ gain := by
    intro h
    apply hg
    apply Finset.mem_filter.mpr
    constructor
    · rw [h] at he
      dsimp [SimpleGraph.supEdgeFinset, SimpleGraph.supIncidenceFinset] at he
      have : s(x, gain) ∈ G.edgeFinset := (Finset.mem_filter.mp he.1).1
      rw [SimpleGraph.incidenceFinset]
      rw [Set.mem_toFinset]
      constructor
      · rw[h]; exact mem_edgeFinset.mp this
      · rw [h]; exact Sym2.mem_mk_right x gain
    · exact (Finset.mem_filter.mp he.1).2
  simp only [x_ne_loose, x_ne_gain, y_ne_loose, y_ne_gain]; rfl

/-- Proves that after `Enhance`, the value of the edge connecting `loose` and `gain`
is strictly increased in comparisson to that under the original weight function. -/
lemma Enhance_edge_gainloose_increase (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) (h_neq : gain ≠ loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) (h_supp : W.w loose > 0 ∧ W.w gain > 0) :
  vp (Enhance G W loose gain h_lt ε epos elt).w s(loose,gain) > vp W.w s(loose,gain)  := by
  simp [vp, Quot.liftOn]
  simp [Enhance]
  rw [if_neg h_neq]
  ring_nf
  rw [mul_tsub]
  rw [lt_tsub_comm] at elt
  apply @lt_of_eq_of_lt _ _ (W.w gain * W.w loose - W.w gain * ε + W.w gain * ε)
  · rw [mul_comm (W.w loose) (W.w gain)]
    have hle : W.w gain * ε ≤ W.w gain * W.w loose := by
      apply mul_le_mul_of_nonneg_left
      · have A : W.w gain + ε < W.w loose := by exact lt_tsub_iff_right.mp elt
        have B : ε ≤ W.w gain + ε := by
          exact le_add_self
        exact le_trans B (le_of_lt A)
      · exact NNReal.coe_nonneg _
    exact Eq.symm (tsub_add_cancel_of_le hle)
  · apply add_lt_add_left
    apply mul_lt_mul_of_pos_right
    · exact elt
    · exact epos

/-- States that the subset of supported edges in the Graph, remains the same subset under `Enhance`.
 -/
lemma Enhance_support_edges_same (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) (h_supp : W.w loose > 0 ∧ W.w gain > 0) :
  G.supEdgeFinset W = G.supEdgeFinset (Enhance G W loose gain h_lt ε epos elt) :=
  by
  ext x
  dsimp [supEdgeFinset]
  rw [mem_filter, mem_filter]
  have part : Sym2.inSupport G W x ↔ Sym2.inSupport G (Enhance G W loose gain h_lt ε epos elt) x :=
    by
    apply @Sym2.inductionOn α (fun x => Sym2.inSupport G W x ↔ Sym2.inSupport G (Enhance G W loose gain h_lt ε epos elt) x) x
    intro a b
    rw [Sym2.inSupport_explicit, Sym2.inSupport_explicit, ← Enhance_support_unchanged, ← Enhance_support_unchanged]
    exact h_supp.2 ; exact h_supp.2
  simp_all only [ne_eq, gt_iff_lt, Set.mem_toFinset]

/-- Combining previous lemmas, shows that the total edge weight increases or remains the same under `Enhance`.

Notes:
- `sum_over_support` : Assures that the total whole edge value of the Graph is the same as the total edge value of the
edges in the support
- `Enhance_support_edges_same` : assures the supported subset of edges is the same under `Enhance`
- `supported_edge_partition` : Partitions the total edge contribution of the clique (and whole Graph) into:
  + `inci_loose_gain_full` (edged incident to loose, edges incident to gain and {gain,loose})
  + `inci_loose_gain_full`'s complement

Now we show the change for each:
- with `Enhance_sum_complement_unchanged` we show that edges in the support but not in `inci_loose_gain_full` remain with
unchanged weights

- with `Enhance_gain_sum`, `Enhance_loose_sum` the lemma quantifies the gain from edges incident to gain and the loss from edges
incident to loose, then with  `Enhance_sum_loose_gain_equal`, since the support is a clique and there is a bijection between edged inci.
to loose to edges incid. to gain, we show that the change is 0.
- with `Enhance_edge_gainloose_increase` we show that the only change comes from the edge `gain-loose`
Therefore concluding that `Enhance` forms an strictly greater weight distribution
-/
lemma Enhance_total_weight_nondec (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (h_adj : G.Adj gain loose) (h_supp : W.w loose > 0 ∧ W.w gain > 0)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  W.fw ≤ (Enhance G W loose gain h_lt ε epos elt).fw := by
  simp_rw [FunToMax.fw]
  rw [sum_over_support G W, supported_edge_partition G W loose gain h_adj h_supp, sum_disjUnion]
  have todo : (Enhance G W loose gain h_lt ε epos elt).w loose > 0 ∧ (Enhance G W loose gain h_lt ε epos elt).w gain > 0 := by
    rw [← Enhance_support_unchanged, ← Enhance_support_unchanged] ; exact h_supp ; exact h_supp.2 ; exact h_supp.2
  rw [sum_over_support G (Enhance G W loose gain h_lt ε epos elt),← Enhance_support_edges_same G W loose gain h_lt ε epos elt h_supp]
  nth_rewrite 2 [supported_edge_partition G W loose gain h_adj h_supp]
  rw [sum_disjUnion]
  apply add_le_add
  · dsimp [inci_loose_gain_full]
    rw [sum_disjUnion,sum_disjUnion]
    apply add_le_add
    · dsimp [incidence_loose_gain]
      rw [sum_disjUnion,sum_disjUnion]
      rw [Enhance_gain_sum G W loose gain h_lt ε epos elt]
      rw [Enhance_loose_sum G W loose gain h_lt ε epos elt]
      rw [Enhance_sum_loose_gain_equal G W loose gain h_lt ε epos elt hc h_supp]
      rw [add_assoc]
      rw [add_tsub_cancel_of_le] -- seems to have done le_refl automaticly
      rw [← Enhance_sum_loose_gain_equal G W loose gain h_lt ε epos elt hc h_supp]
      rw [mul_sum]
      nth_rewrite 2 [← sum_attach]
      apply sum_le_sum
      apply epsilon_weight_bound G W loose gain h_lt ε epos elt
    · rw [sum_singleton, sum_singleton]
      apply le_of_lt -- so the bound is actually strict
      apply Enhance_edge_gainloose_increase
      · apply neq_of_W_lt G h_lt
      · exact h_supp
  · rw [← Enhance_sum_complement_unchanged G W loose gain h_lt ε epos elt]

-- end Section_2

-- section Section_3
/-!
Section 3 : Equalizing weights on the clique

Given any weight function `W` whose support is a clique here we:

 1. define
    - `W.max_weight` and `W.min_weight` as the extremal vertex weights,
    - `W.argmax` and `W.argmin` as vertices attaining them;

 2. prove inequalities relating these to the average weight `1 / |support|`:
    - `avg ≤ max`, `min ≤ avg`,
    - strictly showing `min < max ↔ avg < max` and `min < avg`

 3. set `the_ε := max_weight − (1/|support|) > 0` (when `min < max`), and define
    another improved weight function `Enhanced` that moves `ε` from `argmax` to `argmin`

 4. show `Enhanced` preserves total weight, support, and clique structure AND
    strictly increases the number of vertices with weight exactly `1/|support|`

 5. Shows `UniformBetter` has constant support
--/

/-- Assures the support of a weight function is non empty-/
lemma FunToMax.supp_nonempty (W : FunToMax G) : ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).Nonempty := by
  by_contra con
  simp [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at con
  have todo : ∑ v∈(Finset.univ : Finset α), W.w v = 0 := by
    simp_rw [con] ; apply sum_const_zero
  apply @one_ne_zero NNReal
  rw [← todo, W.h_w]
  -- should have used `supportSizeNotZero`

/-- Defines the maximun weight value among vertices -/
noncomputable
def FunToMax.max_weight (W : FunToMax G) :=
  Finset.max' (Finset.image W.w ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (by rw [image_nonempty] ; exact FunToMax.supp_nonempty G W)

/-- Specifies that there exists a vertex in the support attaining the maximum weight-/
lemma FunToMax.argmax_pre (W : FunToMax G) : ∃ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v = W.max_weight G := by
  rw [← mem_image] ; apply max'_mem

/-- Chooses a vertex attaining the maximun weight (later used as the `loose` vertex)-/
noncomputable
def FunToMax.argmax (W : FunToMax G) := Classical.choose (W.argmax_pre G)

/-- Proves that the chosen argmax vertex lies in the support (has positive weight)-/
lemma FunToMax.argmax_mem (W : FunToMax G) : (W.argmax G) ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)) :=
  (Classical.choose_spec (W.argmax_pre G)).1

/-- Confirms that the weigth of the chosen argmax vertex equals the maximun weight.-/
lemma FunToMax.argmax_weight (W : FunToMax G) : W.w (W.argmax G) = W.max_weight G := by
  exact (Classical.choose_spec (W.argmax_pre G)).2

/-- Defines the min. weight among vertices with positive weight -/
noncomputable
def FunToMax.min_weight (W : FunToMax G) :=
  Finset.min' (Finset.image W.w ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (by rw [image_nonempty] ; exact FunToMax.supp_nonempty G W)

/-- Specifies that there exists a vertex in the support that attains the minimun weight. -/
lemma FunToMax.argmin_pre (W : FunToMax G) : ∃ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v = W.min_weight G := by
  rw [← mem_image] ; apply min'_mem

/-- Chooses a vertex attaining the min weight (later used as the `gain` vertex)-/
noncomputable
def FunToMax.argmin (W : FunToMax G) :=
  Classical.choose (W.argmin_pre G)

/-- Proves that the chosen argmin vertex lies in the support. -/
lemma FunToMax.argmin_mem (W : FunToMax G) : (W.argmin G) ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)) :=
  (Classical.choose_spec (W.argmin_pre G)).1

/-- Confirms that the weight of the chosen argmin vertex equals the min. weight. -/
lemma FunToMax.argmin_weight (W : FunToMax G) : W.w (W.argmin G) = W.min_weight G := by
  exact (Classical.choose_spec (W.argmin_pre G)).2

/-- Shows that every vertex's weight is at most the maximun weight-/
lemma FunToMax.max_weight_max (W : FunToMax G) : ∀ v, W.w v ≤ W.max_weight G := by
  intro v
  by_cases q : v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0))
  · apply le_max' ; apply mem_image_of_mem ; apply q
  · simp only [gt_iff_lt, mem_filter, mem_univ, true_and, not_lt, nonpos_iff_eq_zero] at q
    rw [q]
    apply (W.max_weight G).prop

/-- Shows that every vertex's weight is at least the minimun weight-/
lemma FunToMax.min_weight_min (W : FunToMax G) : ∀ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.min_weight G ≤ W.w v := by
  intro v hv ; apply min'_le ; apply mem_image_of_mem ; apply hv

/--Shows that the weight of the argmin vertex is at most that of the argmax vertex-/
lemma FunToMax.argmin_le_argmax (W : FunToMax G) : W.w (W.argmin G) ≤  W.w (W.argmax G) := by
  rw [W.argmin_weight] ; apply W.min_weight_min ; apply W.argmax_mem

/-- Assures that minimum weight is at most the maximum weight -/
lemma FunToMax.min_weight_le_max_weight (W : FunToMax G) : W.min_weight G ≤  W.max_weight G := by
  rw [← W.argmin_weight, ← W.argmax_weight] ; apply W.argmin_le_argmax

-- /-- Shows the inequality bewtwen the maximun weight times the support size with the sum of weights on the support-/
-- lemma FunToMax.max_weight_ineq (W : FunToMax G) :
--     (W.max_weight G : ℝ) * ((Finset.univ.filter (fun i => W.w i > 0)).card : ℝ)
--     ≥ ∑ v in (Finset.univ.filter (fun i => W.w i > 0)), (W.w v : ℝ) := by
--   let S := Finset.univ.filter (fun i => W.w i > 0)
--   have bound : ∀ v ∈ S, (W.w v : ℝ) ≤ (W.max_weight G : ℝ) :=
--     fun v _ => NNReal.coe_le_coe.mpr (W.max_weight_max G v)
--   calc
--     (W.max_weight G : ℝ) * (S.card : ℝ)
--         = (S.card : ℝ) * (W.max_weight G : ℝ) := by rw [mul_comm]
--     _ = ∑ v in S, (W.max_weight G : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
--     _ ≥ ∑ v in S, (W.w v : ℝ) := Finset.sum_le_sum bound

/-- Shows that the sum of weights over all vertices equals the sum of weights over the support. -/
lemma FunToMax.sum_eq_sum_supp (W : FunToMax G) :
  ∑ v ∈ (Finset.univ : Finset α), W.w v
  = ∑ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v := by
  have H : (Finset.univ : Finset α) =
    Finset.univ.filter (fun i => W.w i > 0) ∪ Finset.univ.filter (fun i => ¬ (W.w i > 0)) := by
    ext v
    simp [Finset.mem_filter]
    simp[or_comm]
    by_cases h : W.w v > 0
    · exact Or.inr h
    · exact Or.inl (NNReal.eq_zero_of_ne_pos h)
  have h_disj : (Finset.univ.filter (fun i => W.w i > 0)) ∩ (Finset.univ.filter (fun i => ¬ W.w i > 0)) = ∅ := by
    ext v
    simp [mem_inter, mem_filter]
    intro h
    exact pos_iff_ne_zero.mp h
  have h_zero : ∀ v ∈ Finset.univ.filter (fun i => ¬ W.w i > 0), W.w v = 0 := by
    intros v hv
    simp [Finset.mem_filter] at hv
    exact hv
  have A : (Finset.univ.filter (fun i => 0 < W.w i) ∪ Finset.univ.filter (fun i => W.w i = 0)) = Finset.univ := by
    ext x
    simp [Finset.mem_union, Finset.mem_filter, Finset.mem_univ]
    match Classical.em (W.w x = 0) with
    | Or.inl h => right; exact h
    | Or.inr h => left; rw [pos_iff_ne_zero]; exact h
  rw [H]
  rw [← disjoint_iff_inter_eq_empty] at h_disj
  rw [sum_union h_disj]
  rw [sum_congr rfl h_zero]
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, sum_const_zero, add_zero]
  rw[A]

/-- Proves that the sum of weights on the support is exactly 1-/
lemma FunToMax.sum_supp_eq_one (W : FunToMax G) :
  ∑ v∈((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v = 1 := by
  convert W.h_w using 1
  rw [sum_filter]
  apply sum_congr rfl
  intro x _
  split_ifs with Q
  · rfl
  · have := (W.w x).prop
    rw [NNReal.eq_iff]
    apply eq_of_le_of_not_lt this
    contrapose! Q
    simp only [gt_iff_lt]
    rw [← NNReal.coe_lt_coe ]
    exact Q

/-- Gives an upper bound on the sum of weights on the support using the maximal weight times the support size  -/
lemma FunToMax.sum_supp_le_max  (W : FunToMax G) :
  ∑ v∈((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v
    ≤ (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) * W.max_weight G := by
  let S := ((Finset.univ : Finset α).filter (fun i => W.w i > 0))
  have bound : ∀ v ∈ S, W.w v ≤ W.max_weight G := by
    intro v hv
    exact W.max_weight_max G v
  calc
    ∑ v in S, W.w v
      ≤ ∑ v in S, W.max_weight G := Finset.sum_le_sum bound
    _ = (S.card : NNReal) * W.max_weight G := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Gives a lower bound on the sum of weights on the support using the minimun weight times the support size . -/
lemma FunToMax.min_le_sum_supp  (W : FunToMax G) :
  ∑ v∈((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v
    ≥ (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) * W.min_weight G := by
  let S := (Finset.univ : Finset α).filter (fun i => W.w i > 0)
  have bound : ∀ v ∈ S, W.min_weight G ≤ W.w v := by
    intro v hv
    exact W.min_weight_min G v hv
  calc
    ∑ v in S, W.w v
      ≥ ∑ v in S, W.min_weight G :=
        Finset.sum_le_sum (fun v hv => bound v hv)
    _ = (S.card : NNReal) * W.min_weight G := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- States that the maximum weight is at least the average support weight (1/|support|) -/
lemma FunToMax.avg_le_max (W : FunToMax G) :
    W.max_weight G ≥ 1 / (↑((Finset.univ.filter (fun i => W.w i > 0)).card)) := by
  set S := Finset.univ.filter (fun i => W.w i > 0)
  have h_sum : ∑ v in S, W.w v = 1 := W.sum_supp_eq_one
  have bound : ∀ v ∈ S, W.w v ≤ W.max_weight G := fun v _ => W.max_weight_max G v
  have h_max : 1 ≤ (S.card : ℝ) * W.max_weight G := by
    calc
      1 = ((∑ v in S, W.w v : NNReal) : ℝ) := by rw [h_sum]; norm_cast
      _ = ∑ v in S, (W.w v : ℝ) := by rw [NNReal.coe_sum]
      _ ≤ ∑ v in S, (W.max_weight G : ℝ) := by exact Finset.sum_le_sum (fun v hv => NNReal.coe_le_coe.mpr (bound v hv))
      _ = (S.card : ℝ) * W.max_weight G := by rw [Finset.sum_const, nsmul_eq_mul]
  exact NNReal.div_le_of_le_mul' h_max

/-- States that the minimun weight is at most the average support weight (1/|support|)-/
lemma FunToMax.min_le_avg  (W : FunToMax G) :
  W.min_weight G ≤ 1 / (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) := by
  let S := (Finset.univ : Finset α).filter (fun i => W.w i > 0)
  obtain ⟨x, hx⟩ := FunToMax.supp_nonempty G W
  have hS_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x, hx⟩)
  have h_sum : ∑ v in S, W.w v = 1 := W.sum_supp_eq_one
  have bound : ∀ v ∈ S, (W.min_weight G : ℝ) ≤ (W.w v : ℝ) :=
    fun v hv => NNReal.coe_le_coe.mpr (W.min_weight_min G v hv)
  have h_min : (S.card : ℝ) * (W.min_weight G : ℝ) ≤ 1 := by
    calc
      (S.card : ℝ) * (W.min_weight G : ℝ)
          = ∑ v in S, (W.min_weight G : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v in S, (W.w v : ℝ) := Finset.sum_le_sum bound
      _ = (∑ v in S, W.w v : NNReal) := by norm_cast
      _ = 1 := by rw [h_sum]; rfl
  have h_div : (W.min_weight G : ℝ) ≤ 1 / (S.card : ℝ) := by
    rw [le_div_iff₀' hS_pos]
    exact h_min
  exact h_div

/-- Shows that if the minimun weight is strictily less that the maximum weight, then the sum of weights
over the support is strictly less than the support size times the maximun weight-/
lemma FunToMax.sum_supp_lt_max  (W : FunToMax G) (h : W.min_weight G < W.max_weight G) :
  ∑ v∈((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v
    < (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) * W.max_weight G := by
  nth_rewrite 1 [← Finset.insert_erase (W.argmin_mem G)]
  rw [sum_insert]
  swap
  · apply not_mem_erase
  · rw [card_eq_sum_ones,  Nat.cast_sum, sum_mul]
    nth_rewrite 2 [← Finset.insert_erase (W.argmin_mem G)]
    rw [sum_insert]
    swap
    · apply not_mem_erase
    · rw [Nat.cast_one, one_mul]
      apply add_lt_add_of_lt_of_le
      · rw [← W.argmin_weight] at h
        exact h
      · apply sum_le_sum
        intro i idef
        apply W.max_weight_max

/-- Shows that if the minimun weight is strictily less that the maximum weight, then the sum over the support
is strictly greater than the support size times the minimum weight-/
lemma FunToMax.min_lt_sum_supp (W : FunToMax G) (h : W.min_weight G < W.max_weight G) :
  ∑ v in ((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v
    > (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card : NNReal) * W.min_weight G := by
  nth_rewrite 1 [← Finset.insert_erase (W.argmax_mem G)]
  rw [sum_insert]
  swap
  · apply not_mem_erase
  · rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]
    nth_rewrite 2 [← Finset.insert_erase (W.argmax_mem G)]
    rw [sum_insert]
    swap
    · apply not_mem_erase
    · rw [Nat.cast_one, one_mul]
      apply add_lt_add_of_lt_of_le
      · rw [← W.argmax_weight] at h
        exact h
      · apply sum_le_sum
        intro i idef
        apply W.min_weight_min
        exact mem_of_mem_erase idef

/-- States that the weight of the argmax vertex is at least the weight of any vertex in the support. -/
lemma FunToMax.argmax_weight_ge (W : FunToMax G) (v : α)
   (hv : v ∈ Finset.univ.filter (λ i => W.w i > 0)) :
    W.w (W.argmax G) ≥ W.w v := by
  rw [argmax_weight]
  exact max_weight_max G W v

/-- Shows that if the minimun weight is strictily less that the maximum weight, then the maximum weight
is strictly greater than (1/|support|) -/
lemma FunToMax.avg_lt_max (W : FunToMax G) (h : W.min_weight G < W.max_weight G) :
  W.max_weight G > 1 / (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) := by
  have := W.sum_supp_lt_max G h
  have tec : ∑ v ∈ univ, W.w v = ∑ v ∈ filter (fun i ↦ W.w i > 0) univ, W.w v := by
    exact sum_eq_sum_supp G W
  rw [← tec , W.h_w] at this
  simp only [gt_iff_lt, one_div]
  rw [inv_lt_iff_one_lt_mul₀]
  · rw [mul_comm] ; exact this
  · rw [Nat.cast_pos]
    rw [card_pos]
    use W.argmax G
    simp only [mem_filter, mem_univ, true_and]
    rw [W.argmax_weight]
    apply lt_of_le_of_lt _ h
    apply (min_weight G W).prop

/-- Shows that if the minimun weight is strictily less than the maximum weight, then the minimum weight
is strictly less than (1/|support|) -/
lemma FunToMax.min_lt_avg (W : FunToMax G) (h : W.min_weight G < W.max_weight G) :
    W.min_weight G < 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card := by
  let S := Finset.univ.filter (λ i => W.w i > 0)
  let x := W.argmax G
  have xS : x ∈ S := W.argmax_mem G
  have x_gt : W.min_weight G < W.w x := by
    rw [argmax_weight]
    exact h
  have sum_eq : ∑ v in S, W.w v = 1 := W.sum_supp_eq_one
  have card_pos : 0 < S.card := by
    apply Finset.card_pos.mpr
    use x
  have m_pos : (↑(S.card) : NNReal) > 0 := by exact_mod_cast card_pos
  have tec : ∑ v ∈ univ, W.w v = ∑ v ∈ filter (fun i ↦ W.w i > 0) univ, W.w v := by
    exact sum_eq_sum_supp G W
  have := W.min_lt_sum_supp
  rw [← tec , W.h_w] at this
  have final : W.min_weight G < 1 / ↑(S.card) := by exact (lt_div_iff₀' m_pos).mpr (this h)
  exact final

/--Shows that if the min. and max. weight are equal, then every vertex in the support
 hast weight 1/|support|. -/
lemma FunToMax.min_eq_max  (W : FunToMax G) (h : W.min_weight G = W.max_weight G):
  ∀ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)),
    W.w v = 1 / (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) := by
  let S := (Finset.univ.filter (λ i => W.w i > 0))
  have sumS : ∑ v in S, W.w v = 1 := W.sum_supp_eq_one
  have each_eq_min : ∀ v ∈ S, W.w v = W.min_weight G := by
    intros v hv
    have A := W.min_weight_min G v hv
    have B := W.max_weight_max G v
    rw [← h] at B
    exact le_antisymm B A
  have eq_card : (S.card : NNReal) * W.min_weight G = 1 := by
    have all_min : ∑ v in S, W.w v = ∑ v in S, W.min_weight G :=
      Finset.sum_congr rfl (λ v hv => each_eq_min v hv)
    rw [all_min] at sumS
    rw [Finset.sum_const, nsmul_eq_mul] at sumS
    exact sumS
  have card_nonzero : (S.card : NNReal) ≠ 0 := by
    apply Nat.cast_ne_zero.2
    exact support_size_nonempty G W
  intros v hv
  rw [each_eq_min v hv]
  have : W.min_weight G = 1 / (S.card : NNReal) := by
    rw [← eq_card]
    exact Eq.symm (mul_div_cancel_left₀ (min_weight G W) card_nonzero)
  rw [this]

-- Section 3.5 The last weight transfer

/--Defines ε (the_ε) as the difference between maximum weight and the average weight 1/|support| -/
noncomputable
def the_ε (W : FunToMax G) :=
  (W.max_weight G) - (1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)

/-- Shows that ε is positive if the min. and max. weight are distinct -/
lemma the_ε_pos (W : FunToMax G) (h : W.min_weight G < W.max_weight G) : 0 < the_ε G W := by
  have ineq := @FunToMax.avg_lt_max _ _ _ _ _ W h
  exact tsub_pos_of_lt ineq

/-- Shows that ε is less than the difference between the weights between argmax argmin vertices -/
lemma the_ε_lt (W : FunToMax G) (h : W.min_weight G < W.max_weight G) :
  the_ε G W < W.w (W.argmax G) - W.w (W.argmin G) := by
  unfold the_ε
  rw [FunToMax.argmax_weight]
  rw [tsub_lt_tsub_iff_left_of_le]
  · rw [FunToMax.argmin_weight]
    apply FunToMax.min_lt_avg
    exact h
  · apply FunToMax.avg_le_max

/-- Helper lemma: confirms if the weight at the argmin is less than that in argmax vertex, then the minimum weight
is strictly less than the maximum weight-/
lemma arg_help {W : FunToMax G} (h_con : W.w (W.argmin G) <  W.w (W.argmax G)) : W.min_weight G < W.max_weight G :=
  by rw [← W.argmin_weight, ← W.argmax_weight] ; exact h_con

/-- Defines `Enhanced` weight function : transfering weight from the argmax vertex `loose` to the argmin
vertex `gain`, using the previous in Section 2 defined function `Enhance` by the amount defined `the_ε`. -/
noncomputable
def Enhanced (W : FunToMax G) (h_con : W.w (W.argmin G) <  W.w (W.argmax G)) :=
  (Enhance G W (W.argmax G) (W.argmin G) h_con (the_ε G W) (the_ε_pos G W (arg_help G h_con)) (the_ε_lt G W (arg_help G h_con)))

/-- Shows that under `Enhanced` every vertex that originally had weight 1/|support|, remains with the same weight -/
lemma Enhanced_unaffceted (W : FunToMax G) (h_con : W.w (W.argmin G) <  W.w (W.argmax G)) :
  ∀ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)),
    (Enhanced G W h_con).w v = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card := by
  intro v hv
  rw[mem_filter] at hv
  dsimp[Enhanced, Enhance]
  set M := FunToMax.argmax G W
  set m := FunToMax.argmin G W
  split_ifs with hL hM
  · set c : NNReal := 1 / ↑(#(filter (fun i => W.w i > 0) univ)) with  hc
    rw [← hL, hv.2] at h_con
    rw [hc] at h_con
    have wM_eq_c : W.w M = c := by rw [← hL, hv.2]
    rw[wM_eq_c]
    have eqMax : W.max_weight = c := by
      rw [← FunToMax.argmax_weight G W]
      exact wM_eq_c
    have zero_eps : the_ε G W = 0 := by
      dsimp [the_ε]
      rw [eqMax, hc]
      exact tsub_self c
    rw[zero_eps, tsub_zero]
  · exfalso
    apply (ne_of_lt _) hv.2
    rw [hM]
    dsimp [m]
    rw [FunToMax.argmin_weight]
    apply FunToMax.min_lt_avg
    rw [← FunToMax.argmin_weight, ← FunToMax.argmax_weight]
    exact h_con
  · exact hv.2

/-- Proves that under the Enhanced weight function, the weight of the argmax vertex becomes 1/|support| -/
lemma Enhanced_effect_argmax (W : FunToMax G) (h_con : W.w (W.argmin G) <  W.w (W.argmax G)) :
  (Enhanced G W h_con).w (W.argmax G) = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card := by
  dsimp [Enhanced,Enhance]
  rw [if_pos rfl]
  dsimp [the_ε]
  rw [FunToMax.argmax_weight]
  rw [tsub_tsub_assoc]
  · rw [tsub_self,zero_add]
  · apply le_refl
  · apply FunToMax.avg_le_max

/-- Shows that the number of vertices with weight equal to 1/|support| increases after  `Enhanced`-/
lemma Enhanced_inc_uniform_count (W : FunToMax G) (h_con : W.w (W.argmin G) <  W.w (W.argmax G))  :
  let OneOverKSize (X : FunToMax G) := ((Finset.univ : Finset α).filter (fun i => X.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card ;
  OneOverKSize (Enhanced G W h_con) > OneOverKSize W := by
  intro OneOverKSize
  let denom := ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card
  let S := Finset.univ.filter (fun i => W.w i = 1 / denom)
  let T := Finset.univ.filter (fun i => (Enhanced G W h_con).w i = 1 / denom)
  have h_sub : S ⊆ T := by
    intro i hi
    have hi_val : W.w i = 1 / denom := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Enhanced_effect_argmax G W h_con]
    rw [Enhanced_effect_argmax G W h_con]
    rw [Enhanced_unaffceted G W h_con i]
    rw [mem_filter]
    refine' ⟨ by apply mem_univ, _ ⟩
    apply hi_val
  have h_ssub : S ⊂ T := by
    rw [Finset.ssubset_iff_of_subset h_sub]
    use W.argmax G
    constructor
    · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Enhanced_effect_argmax G W h_con
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      apply ne_of_gt
      rw [FunToMax.argmax_weight]
      apply FunToMax.avg_lt_max G W
      rw [← FunToMax.argmin_weight, ← FunToMax.argmax_weight]
      exact h_con
  exact card_lt_card h_ssub

/-- Helper lemma: Relates the support of the `UniformBetter` weight function to that of the original weight function `W`. THAT
is having W, whose support forms a clique, UniformBetter support also forms a clique -/
lemma UniformBetter_support_equiv (W : FunToMax G) (hW : G.IsClique ↑(filter (fun i ↦ W.w i > 0) univ)) (i : α) :
  W.w i > 0 ↔ (UniformBetter G W hW).w i > 0:= by
    rw [← not_iff_not]
    constructor
    · intro h
      intro con
      replace h := NNReal.eq_zero_of_ne_pos  h
      rw [UniformBetter_support_zero G W hW] at h
      rw [h] at con
      exact lt_irrefl _ con
    · intro h
      intro con
      replace h := NNReal.eq_zero_of_ne_pos  h
      rw [← UniformBetter_support_zero G W hW] at h
      rw [h] at con
      exact lt_irrefl _ con

/-- Helper lemma: Shows that if two vertices in the support of W are distinct then they are adjacent
 (since they are in a clique). Proves that the support forms a clique -/
lemma clique_support_adjacent (W : FunToMax G)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0)))
  (x y : α) (hx : W.w x > 0) (hy : W.w y > 0) (lol : x ≠ y) :
    G.Adj x y := by
  dsimp [SimpleGraph.IsClique] at hc
  apply hc
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ x, hx⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ y, hy⟩
  · exact lol

/--
Shows that under the `UniformBetter`, every vertex in the support has an equal weight
of 1/|support|.
-/
lemma UniformBetter_constant_support (W : FunToMax G)
  (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  ∀ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)),
    (UniformBetter G W hW).w v = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card := by
  intro v hv
  have q := le_iff_eq_or_lt.mp ((UniformBetter G W hW).min_weight_le_max_weight G)
  cases' q with q h_con
  · have := (UniformBetter G W hW).min_eq_max G q v
    have support_subset := UniformBetter_support_zero G W hW
    have h_subset := UniformBetter_support_zero G W hW
    have h_eq : {i | (UniformBetter G W hW).w i > 0} = {i | W.w i > 0} := by
      ext i
      simp only [Set.mem_setOf_eq, gt_iff_lt, not_lt]
      rw [←not_iff_not]
      simp only [not_lt, le_zero_iff]
      exact (h_subset i).symm
    have card_eq : #(filter (fun i => (UniformBetter G W hW).w i > 0) univ) = #(filter (fun i => W.w i > 0) univ) := by congr
    rw [←card_eq]
    rw [mem_filter] at hv
    have hv' : v ∈ filter (fun i => (UniformBetter G W hW).w i > 0) univ := by
      rw [mem_filter]
      exact ⟨mem_univ v, (Set.ext_iff.mp h_eq v).mpr hv.2⟩
    exact this hv'
  · exfalso
    have reminder := UniformBetter_support_size G W hW
    simp_rw [UniformBetter_support_equiv G W hW] at reminder
    have problem := Enhanced_inc_uniform_count G (UniformBetter G W hW)
      (by rw [@FunToMax.argmin_weight]; rw [@FunToMax.argmax_weight]; exact h_con)
    dsimp at problem
    rw [reminder] at problem
    have ohoh := @Nat.findGreatest_is_greatest (#(filter (fun i ↦ (Enhanced G (UniformBetter G W hW) _).w i = 1 / ↑(#(filter (fun i ↦ (UniformBetter G W hW).w i > 0) univ)))
      univ)) _ _ _ problem
    apply ohoh
    clear ohoh
    · simp_rw [UniformBetter_support_equiv G W hW]
      apply card_le_card
      intro x xdef
      rw [mem_filter] at xdef ⊢
      refine' ⟨xdef.1, _⟩
      dsimp [Enhanced] at xdef
      have := Enhance_support_unchanged G (UniformBetter G W hW)
        (FunToMax.argmax G (UniformBetter G W hW))
        (FunToMax.argmin G (UniformBetter G W hW))
        (by rw [@FunToMax.argmin_weight]; rw [@FunToMax.argmax_weight]; exact h_con)
        (by
          have h_gain_pos : 0 < (UniformBetter G W hW).w (FunToMax.argmin G (UniformBetter G W hW)) := by
            have hmem : (FunToMax.argmin G (UniformBetter G W hW)) ∈ ((Finset.univ : Finset α).filter
                      (fun i => (UniformBetter G W hW).w i > 0)) := FunToMax.argmin_mem (G := G) (W := UniformBetter G W hW)
            exact (Finset.mem_filter.1 hmem).2
          exact h_gain_pos            )
        (the_ε G (UniformBetter G W hW))
        (by exact the_ε_pos G (UniformBetter G W hW) h_con)
        (by exact the_ε_lt G (UniformBetter G W hW) h_con)
      rw [this, xdef.2]
      exact one_div_pos.mpr (Nat.cast_pos.mpr (card_pos.mpr ⟨v, by
        simp only [mem_filter, mem_univ, true_and]
        have hv_pos : W.w v > 0 := by rcases Finset.mem_filter.1 hv with ⟨-, hv_pos⟩; exact hv_pos
        have : (UniformBetter G W hW).w v > 0 := (UniformBetter_support_equiv (G:=G) (W:=W) (hW:=hW) v).mp hv_pos
        exact this⟩))
    · clear ohoh -- clear bug
      dsimp [exists_uniform_clique]
      use (Enhanced G (UniformBetter G W hW) (by rw [@FunToMax.argmin_weight, @FunToMax.argmax_weight]; exact h_con))
      let eW : FunToMax G := UniformBetter G W hW
      let loose : α := FunToMax.argmax G eW
      let gain  : α := FunToMax.argmin G eW
      have gain_pos : 0 < eW.w gain := by
        have : gain ∈ ((Finset.univ : Finset α).filter (fun j => eW.w j > 0)) :=
        FunToMax.argmin_mem (G:=G) (W:=eW)
        exact (Finset.mem_filter.1 this).2
      let ε   : NNReal := the_ε G eW
      have h_lt : eW.w gain < eW.w loose := by
        dsimp [gain, loose] at *; simpa [FunToMax.argmin_weight, FunToMax.argmax_weight] using h_con
      have epos : 0 < ε := by exact the_ε_pos G eW h_con
      have elt  : ε < eW.w loose - eW.w gain := by exact the_ε_lt G eW h_con
      have hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => eW.w i > 0)) := (UniformBetter_clique (G:=G) (W:=W) (hW:=hW))
      split_ands
      · intro i
        have h_equiv := (Enhance_nsupport_unchanged (G:=G) (W:=eW) (loose:=loose) (gain:=gain) h_lt gain_pos ε epos elt) i
        constructor
        · intro i0
          have heW0 : eW.w i = 0 := by exact (UniformBetter_support_zero G W hW i).mp i0
          have : (Enhanced G eW h_lt).w i = 0 := by
            dsimp [Enhanced, loose, gain] at *
            have h' : (Enhance G eW loose gain h_lt ε epos elt).w i = 0 := (h_equiv).mp heW0
            exact h'
          exact this
        · intro i0'
          have heW0 : eW.w i = 0 := (h_equiv).mpr i0'
          exact (UniformBetter_support_zero G W hW i).mpr heW0
      · exact Enhance_clique (G:=G) (W:=eW)
          (loose:=loose) (gain:=gain)
          (h_lt:=h_lt) (ah:=gain_pos)
          (ε:=ε) (epos:=epos) (elt:=elt) (hc:=hc)
      · let S  := (Finset.univ : Finset α).filter (fun i : α => W.w  i  > 0)
        let S' := (Finset.univ : Finset α).filter (fun i : α => eW.w i  > 0)
        have hS : S = S' := by
          apply Finset.ext ; intro i
          simp [S, S', UniformBetter_support_equiv (G:=G) (W:=W) (hW:=hW) i]
          exact gt_iff_lt
        have h_card : S.card = S'.card := by simp [hS]
        rw [h_card]
      · have h1 : W.fw ≤ eW.fw := UniformBetter_fw_ge (G:=G) (W:=W) hW
        have h_loose_pos : 0 < eW.w loose := by
          have hmem := (FunToMax.argmax_mem (G:=G) (W:=eW))
          exact (Finset.mem_filter.1 hmem).2
        have h_gain_pos : 0 < eW.w gain := gain_pos
        have h_supp : eW.w loose > 0 ∧ eW.w gain > 0 := ⟨h_loose_pos, h_gain_pos⟩
        have h_neq : gain ≠ loose := by exact neq_of_W_lt G h_lt
        have h_adj : G.Adj gain loose := clique_support_adjacent (G:=G) (W:=eW) hc gain loose h_gain_pos h_loose_pos h_neq
        have h2 : eW.fw ≤ (Enhanced G eW h_lt).fw := by
          have hE := Enhance_total_weight_nondec (G:=G) (W:=eW) (loose:=loose) (gain:=gain) h_lt h_adj h_supp ε epos elt hc
          exact hE
        exact le_trans h1 h2

/-- Shows that after `UniformBetter` every edge connecting vertices in the support has edge value equal to
the square of the uniform weight. -/
lemma UniformBetter_edges_value (W : FunToMax G)
  (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  ∀ e ∈ G.supEdgeFinset W, vp (UniformBetter G W hW).w e =
    (1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)^2 := by
  intro e
  apply @Sym2.inductionOn α (fun e => e ∈ G.supEdgeFinset W → vp (UniformBetter G W hW).w e = (1 / ↑(#(filter (fun i ↦ W.w i > 0) univ))) ^ 2)
  intro x y hxy
  dsimp [vp]
  rw [UniformBetter_constant_support G W hW, UniformBetter_constant_support G W hW]
  · rw [pow_two]
  · rw [SimpleGraph.supEdgeFinset] at hxy
    rw [Finset.mem_filter] at hxy
    rcases hxy with ⟨_, vp_pos⟩
    rw [Sym2.inSupport] at vp_pos
    simp only [gt_iff_lt, mem_filter, mem_univ, true_and]
    simp[Quot.lift] at vp_pos
    exact vp_pos.2
  · rw [SimpleGraph.supEdgeFinset] at hxy
    rw [Finset.mem_filter] at hxy
    rcases hxy with ⟨_, vp_pos⟩
    rw [Sym2.inSupport] at vp_pos
    simp only [gt_iff_lt, mem_filter, mem_univ, true_and]
    simp[Quot.lift] at vp_pos
    exact vp_pos.1

/-- Computes the size of the clique induced by the support of W by counting the edges in the support-/
lemma clique_size (W : FunToMax G)
  (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  let k := ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card
  (G.supEdgeFinset W).card = k * (k - 1) / 2 := by
  dsimp
  rw [← Nat.choose_two_right]
  apply Eq.trans _ (Sym2.card_image_offDiag _)
  congr
  ext e
  dsimp [supEdgeFinset]
  apply @Sym2.inductionOn _ (fun e => e ∈ filter (Sym2.inSupport G W) G.edgeFinset ↔ e ∈ image Sym2.mk (filter (fun i ↦ W.w i > 0) univ).offDiag)
  intro x y
  simp only [mem_filter, mem_edgeFinset, mem_image, Finset.mem_offDiag, Sym2.inSupport]
  constructor
  · rintro ⟨h_adj, hx, hy⟩
    rw [SimpleGraph.mem_edgeSet] at h_adj
    use (x, y)
    simp [hx, hy, h_adj, mem_univ]
    exact G.ne_of_adj h_adj
  · rintro ⟨⟨a, b⟩, ⟨⟨a1, ha⟩, ⟨a2, hb⟩, hab⟩, hsym⟩
    have h_adj : G.Adj a b := hW (Finset.mem_filter.mpr ⟨a1, ha⟩) (Finset.mem_filter.mpr ⟨a2, hb⟩) hab
    rcases Sym2.eq_iff.mp hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exact ⟨h_adj, ha, hb⟩
    rw [← hsym]
    exact ⟨h_adj, hb, ha⟩

/-- Computation. -/
lemma computation (k : Nat) (hk : 0 < k) :
  ((k : ℝ) * (k - 1) / 2)  * ((1/k)^2) = (1/2)*(1 - (1/k)) := by
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hk
  have hk2_ne : (↑k ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hk_ne
  field_simp [hk2_ne]
  ring

/-- Bound-/
lemma bound (k q: Nat) (hk : 0 < k) (h : k ≤ q):
  (1/2 : ℝ)*(1 - (1/k)) ≤ (1/2)*(1 - (1/q)) := by
  rw [mul_le_mul_left (by linarith)]
  apply sub_le_sub_left
  apply div_le_div₀
  · linarith
  · linarith
  · rw [Nat.cast_pos]
    exact hk
  · rw [Nat.cast_le]
    exact h

lemma bound_real (k p : Nat) (hk : 0 < k) (hkp : k ≤ p) :
    (1 : ℝ) / 2 * (1 - 1 / ↑k) ≤ 1 / 2 * (1 - 1 / ↑p) :=
  by exact_mod_cast bound k p hk hkp

#check Better_non_decr
#check Better_forms_clique
#check UniformBetter_support_zero
#check UniformBetter_support_equiv
#check UniformBetter_clique

theorem castStuff : @Nat.cast ℝ Real.instNatCast = fun x => (@Nat.cast NNReal AddMonoidWithOne.toNatCast x).val := by
  apply funext
  intro x
  induction' x with x ih
  ·  exact rfl
  · simp only [Nat.cast_add, Nat.cast_one, NNReal.val_eq_coe, NNReal.coe_add, NNReal.coe_natCast,
    NNReal.coe_one]

lemma finale_bound (h0 : p ≥ 2) (h1 : G.CliqueFree p) (W : FunToMax G) : W.fw ≤ ((p-1) * ((p-1) - 1) / 2 ) * (1/(p-1))^2 := by
  apply le_trans (Better_non_decr G W)
  apply le_trans (UniformBetter_fw_ge G _ (Better_forms_clique G W))
  -- f(w) in a uniform distributino is the sum of all vp of edges
  have fst : (UniformBetter G _ (Better_forms_clique G W)).fw = ∑ e ∈ G.supEdgeFinset (Better G W), vp (UniformBetter G _ (Better_forms_clique G W)).w e := by
    rw [FunToMax.fw]
    rw [sum_over_support]
    congr 1
    dsimp [supEdgeFinset]
    congr
    ext x
    apply @Sym2.inductionOn α (fun x => Sym2.inSupport G (UniformBetter G (Better G W) (Better_forms_clique G W)) x ↔ Sym2.inSupport G (Better G W) x)
    intro a b
    rw [Sym2.inSupport_explicit, Sym2.inSupport_explicit]
    rw [← UniformBetter_support_equiv,← UniformBetter_support_equiv]
-- Was this before, I believe it was the other direction since Better could theoretically set one weight
-- to 0 so as its commented here below it wouldndt always be possible
  -- have snd : G.supEdgeFinset W ⊆ G.supEdgeFinset (Better G W) := by
  -- edges still suported after Better
  have snd : G.supEdgeFinset (Better G W) ⊆ G.supEdgeFinset W := by
    intro e
    apply @Sym2.inductionOn α
      (fun e => e ∈ G.supEdgeFinset (Better G W) → e ∈ G.supEdgeFinset W) e
    intro a b h
    dsimp [supEdgeFinset] at h
    simp only [Finset.mem_filter, Sym2.inSupport_explicit] at h
    rcases h with ⟨h_edge, ha, hb⟩
    exact Finset.mem_filter.mpr ⟨h_edge, by
        dsimp [Sym2.inSupport] at *
        have ha_ne : (Better G W).w a ≠ 0 := pos_iff_ne_zero.mp ha
        have wa_ne : W.w a ≠ 0             := mt (Better_support_included G W a) ha_ne
        have hb_ne : (Better G W).w b ≠ 0 := pos_iff_ne_zero.mp hb
        have wb_ne : W.w b ≠ 0             := mt (Better_support_included G W b) hb_ne
        exact ⟨pos_iff_ne_zero.mpr wa_ne, pos_iff_ne_zero.mpr wb_ne⟩⟩
  -- every supported edge has value 1/k^2
  have thd := UniformBetter_edges_value G _ (Better_forms_clique G W)
  -- shows support really is a clique
  have four := UniformBetter_clique G _ (Better_forms_clique G W)
  simp_rw [← UniformBetter_support_equiv G _ (Better_forms_clique G W)] at four
  --recalls number of edges in the clique (clique_size)
  have five := clique_size G _ four
  rw [fst]
  replace thd := fun e ed => le_of_eq (thd e ed)
  apply le_trans (sum_le_card_nsmul _ _ _ thd)
  rw [five]
  rw [nsmul_eq_mul]
  have tec : #(filter (fun i ↦ (Better G W).w i > 0) univ) < p := by
    by_contra! con
    have ohoh := CliqueFree.mono con h1
    replace ohoh := ohoh ↑(filter (fun i ↦ (Better G W).w i > 0) univ)
    apply ohoh
    constructor
    · exact four
    · dsimp [supEdgeFinset]
  -- computations from here on ; try to use `computation` and `bound` maybe
  -- simp [Nat.cast_mul, Nat.cast_sub, Nat.cast_one, Nat.cast_div] at *
  set k := #(filter (fun i => 0 < (Better G W).w i) univ) with hkdef
  have hk_pos : 0 < k := by
    have hne := support_size_nonempty (G := G) (W := Better G W)
    have : ((Finset.univ : Finset α).filter (fun i => 0 < (Better G W).w i)).card = k := by
      simp [hkdef]
    have : k ≠ 0 := by
      intro hk0; exact hne hk0
    exact Nat.pos_of_ne_zero this
  have h_le : k ≤ p - 1 := by exact Nat.le_sub_one_of_lt tec
  have h_bound := bound_real k (p - 1) hk_pos h_le
  have hp1_pos : 0 < p - 1 := by
    have hp : 0 < p := (Nat.zero_lt_two.trans_le h0)
    exact Nat.zero_lt_sub_of_lt h0
  have k_ne_zero : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hk_pos
  have div_ok : 2 ∣ k * (k - 1) := by exact Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp (Nat.even_mul_pred_self k))
  have h_div : ↑(k * (k - 1) / 2) = (k : ℝ) * (k - 1) / 2 := by
    have two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
    simp [Nat.cast_mul, Nat.cast_div div_ok]
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hk_pos)] -- anoying cast stuff
    rw [@Nat.cast_one]
  have h_lhs : ↑(k * (k - 1) / 2) * (1 / (↑k ^ 2)) = (1 / 2 : ℝ) * (1 - 1 / ↑k) := by
    calc
      ↑(k * (k - 1) / 2) * (1 / (k ^ 2) : ℝ)
          = ((k : ℝ) * (k - 1) / 2) * (1 / (k ^ 2) : ℝ) := by rw [h_div]
      _ = ((k : ℝ) * (k - 1) / 2) * ((1 / k) ^ 2)         := by simp [one_div, inv_pow]
      _ = (1 / 2 : ℝ) * (1 - 1 / k)                       := computation k hk_pos
  have h_rhs :
      ((↑p - 1) * (↑p - 1 - 1) / 2) * (1 / (↑p - 1)) ^ 2 =
      (1 / 2 : ℝ) * (1 - 1 / (↑p - 1)) := by
    simpa [Nat.cast_sub (Nat.le_of_lt (lt_of_lt_of_le one_lt_two h0))]
      using
        (computation (p - 1) hp1_pos)
  --
  simp [div_eq_mul_inv, inv_pow, Nat.cast_mul, Nat.cast_sub, Nat.cast_div] at h_lhs
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_natCast, inv_pow, one_div]
  simp only [castStuff] at h_lhs
  simp only [castStuff]
  rw[h_lhs]
  simp only [NNReal.val_eq_coe]
  --
  have hp1_real1 : (0 : ℝ) < ↑(p - 1) := by
    exact_mod_cast hp1_pos
  have hp1_real2 : (0 : ℝ) < (↑p : ℝ) - 1 := by
    have hp : (1 : ℕ) ≤ p := by exact Nat.one_le_of_lt h0
    simpa [Nat.cast_sub hp, Nat.cast_one] using hp1_real1
  have hp1 : (1 : ℕ) ≤ p       := by exact Nat.one_le_of_lt tec
  have hp2 : (1 : ℕ) ≤ p - 1   := by exact (Nat.le_sub_one_iff_lt hp1).mpr h0
  have h_rhs' :
      (↑p - 1 - 1 : ℝ) = ↑p - 2 := by
    simp [sub_sub, one_add_one_eq_two]
  have rhs_eq :
      ((p : ℝ) - 1) * ((p : ℝ) - 2) / 2 * (((p : ℝ) - 1) ^ 2)⁻¹
        = (1 / 2 : ℝ) * (1 - 1 / ((p : ℝ) - 1)) := by
    have h₁ : ((p : ℝ) - 1) ≠ 0 := by
      have : (1 : ℝ) < p := by
        exact Nat.one_lt_cast.mpr h0
      linarith
    field_simp [h₁]
    ring_nf

  rw [← NNReal.coe_mul]

  -- simp only [castStuff]
  -- have sub_eq : (p : ℝ) - 1 - 1 = (p : ℝ) - 2 := by ring
  -- have h_cast :
  --   ↑((↑p : ℝ) - 1 - 1) = ↑((↑p : ℝ) - 2) := by
  --   simp [sub_eq]
  -- conv_rhs =>
  --   simp [sub_eq]





  sorry
#check Nat.cast_pred


  -- h_rhs : (↑↑p - 1) * (↑↑p - 1 - 1) * 2⁻¹ * ((↑↑p - 1) * (↑↑p - 1))⁻¹
  -- goal: ↑(↑p - 1) * ↑(↑p - 1 - 1) * (↑2)⁻¹ * (↑(↑p - 1) ^ 2)⁻¹

  -- 2⁻¹ * (1 - (↑↑k)⁻¹) ≤
  -- after h_rhs: = 2⁻¹ * (1 - (↑↑p - 1)⁻¹)


#check castStuff
#check Enhance_total_weight_nondec
#check Enhanced
#check UniformBetter_support_zero


#check sum_le_sum_of_subset
#check sum_le_card_nsmul

/-- Defines the universal vertex weight function that asisngs all vertices the same weight 1 /|V| -/
noncomputable
def UnivFun [Inhabited α] : FunToMax G where
  w := fun _ => 1 / #univ
  h_w := (by
    rw [sum_const]
    simp only [one_div, nsmul_eq_mul]
    rw [mul_inv_cancel₀]
    simp only [card_univ, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true])

/-- Computes the total edge weight of the universal weight function. Shows that the total edge weight is equal to
the number of edges times the square of the uniform vertex weight.-/
lemma UnivFun_weight [Inhabited α] : (UnivFun G).fw = #E * (1/#(univ : Finset α))^2 := by
  dsimp [UnivFun, FunToMax.fw]
  have h : ∀ e ∈ G.edgeFinset, vp (fun x : α => 1 / ↑n) e = (1 / #(univ : Finset α))^2 := by
    intro e he; revert he; rw [vp]
    refine Quot.inductionOn e ?_; intro ⟨a, b⟩ _
    dsimp; rw [@sq]
  rw [Finset.sum_eq_card_nsmul]
  · rw [nsmul_eq_mul]
  · intro e he; exact h e he

-- # Turan

/-- The final theorem. Let p ≥ 2, and G be a p-Clique free Graph then we find the desired upper bound
on the number of edges.-/
theorem turans [Inhabited α]  (h0 : p ≥ 2) (h1 : G.CliqueFree p):
  (#E : ℝ) ≤ (1/2)* (1 -  1 / (p - 1)) * (#(univ : Finset α))^2 := by
  have := finale_bound G h0 h1 (UnivFun G)
  rw [UnivFun_weight] at this
  have c := computation (p-1)
  rw [Nat.cast_sub, Nat.cast_one] at c
  rw [← c]
  nth_rewrite 1 [one_div] at this
  rw [inv_pow] at this
  swap
  · exact Nat.zero_lt_sub_of_lt h0
  · rw [mul_inv_le_iff₀] at this
    swap
    · exact pow_pos (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨default⟩)) 2
    · rw [← NNReal.coe_le_coe] at this
      simp only [NNReal.coe_natCast, NNReal.val_eq_coe,
        inv_pow, card_univ, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat,
        NNReal.coe_inv, NNReal.coe_pow] at this
      rw [NNReal.coe_sub] at this
      · rw [NNReal.coe_sub] at this
        · rw [NNReal.coe_one] at this
          rw [NNReal.coe_sub] at this
          · rw [castStuff]
            dsimp
            rw [castStuff] at this
            dsimp at this
            apply this
          · rw [← Nat.cast_one]
            rw [Nat.cast_le]
            linarith
        · rw [← Nat.cast_one]
          rw [le_tsub_iff_right]
          · rw [← Nat.cast_add]
            rw [Nat.cast_le]
            apply h0
          · rw [← Nat.cast_one]
            rw [Nat.cast_le]
            linarith
      · rw [← Nat.cast_one]
        rw [Nat.cast_le]
        linarith
  · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (by norm_num) h0)
