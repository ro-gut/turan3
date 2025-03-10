import Mathlib.Topology.Basic

import Mathlib

variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

-- Vertice Set (V), Edge Set (E), Graphs order (n)
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "n" => Fintype.card α

set_option linter.unusedSectionVars false

set_option autoImplicit true -- I need this∈v.4.18


open Finset SimpleGraph

-- "Value" of an edge = product of its vertices weight
def vp (w : α → NNReal) (e : Sym2 α) :=
  Quot.liftOn e (λ pair : α × α => w pair.1 * w pair.2)
    (by intros x y h; cases h;
        · apply refl
        · apply mul_comm)

-- f(w)∈the informal proof
structure FunToMax (G : SimpleGraph α) [Fintype α] where
  w   : α → NNReal
  h_w : ∑ v∈(Finset.univ : Finset α), w v = 1

namespace FunToMax

def fw {G : SimpleGraph α} [DecidableRel G.Adj] (W : FunToMax G) : NNReal :=
  ∑ e∈G.edgeFinset, vp W.w e

end FunToMax

-- help: Assures that for any weight function W there exists an m and another weight function "better" with the following properties
theorem help (W : FunToMax G) : ∃ m : ℕ, (fun m =>
  ∃ better : FunToMax G,
    (∀ i, W.w i = 0 → better.w i = 0) ∧ -- support is included∈that of W
    (((Finset.univ : Finset α).filter (fun i => better.w i > 0)).card = m) ∧ -- support has size m
    (W.fw ≤ better.fw) -- has better weights
    ) m := by
    let m := ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card
    use m
    let better := W
    use better
    have hP : ∀ (i : α), W.w i = 0 → better.w i = 0 := by
      intro i h_w_zero
      have better_eq : better.w = W.w := rfl
      rw [better_eq]
      exact h_w_zero
    have hQ : (Finset.filter (fun i => better.w i > 0) Finset.univ).card = m := by
      exact rfl
    have hR : W.fw ≤ better.fw := by
      have better_fw_eq : better.fw = W.fw := rfl
      rw [better_fw_eq]
    exact ⟨hP, ⟨hQ, hR⟩⟩

open Classical

noncomputable
-- With help G W, K represents the smallest size (m) of the weight support
-- Computes the smallest possible m
def K (W : FunToMax G) := Nat.find (help G W)

-- Pinpoints size m = K(G, W), ensures that the weight function better achieves the optimal size K
lemma help2 (W : FunToMax G):
  ∃ better : FunToMax G,
    (∀ i, W.w i = 0 → better.w i = 0) ∧ -- support is included∈that of W
    (((Finset.univ : Finset α).filter (fun i => better.w i > 0)).card = (K G W)) ∧ -- support has size m
    (W.fw ≤ better.fw) -- has better weights
    := Nat.find_spec (help G W)

-- Define optimal weight function with size m = K(G,W)
noncomputable
def Better (W : FunToMax G) : FunToMax G := Classical.choose (help2 G W)

-- Ensures Better's support is included∈W's support
lemma BetterSupportIncluded (W : FunToMax G)  (i : α) (hi : W.w i = 0) : (Better G W).w i = 0 :=
  (Classical.choose_spec (help2 G W)).1 i hi

-- Confirms the size of Better's support (K(G,W)) being the smallest size guaranteed by help2
lemma BetterSupportSize (W : FunToMax G) : ((Finset.univ : Finset α).filter (fun i => (Better G W).w i > 0)).card = (K G W) :=
  (Classical.choose_spec (help2 G W)).2.1

-- Ensures that the function of Better is at least as large as that of W
lemma BetterHigher (W : FunToMax G) : W.fw ≤ (Better G W).fw :=
  (Classical.choose_spec (help2 G W)).2.2

-- Define a new weight function redistributing weight from one vertex (loose) to another (gain)
-- Note : I added h_neq as an assumption
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
    --⊢ (∑ x ∈ filter (fun x => ¬x = loose) univ, if x = gain then W.w gain + W.w loose else W.w x) = 1
    -- sum of           all x =! loose           ,        condition          = 1
    rw[Finset.sum_ite]
    have : filter (fun x => x = gain) (filter (fun x => ¬x = loose) univ) = {gain} := by
      rw[Finset.filter_filter]
      ext a
      constructor
      · intro h
        rw[Finset.mem_filter] at h
        simp only [Finset.mem_singleton]
        exact h.2.2
      · intro h
        simp only [Finset.mem_singleton] at h
        rw[Finset.mem_filter]
        constructor
        · exact Finset.mem_univ a
        · constructor
          · intro contra
            rw[h] at contra
            exact h_neq contra
          · exact h
    -- Rewrite using previous result
    rw[this]
    rw[Finset.sum_singleton]
    rw[Finset.filter_filter]
    -- S is set of vertices excluding gain and loose
    let S := filter (fun x => x ≠ gain ∧ x ≠ loose) univ
    -- Rewrite total sum of weights∈terms of gain, loose and S
    have h_sum : ∑ x ∈ univ, W.w x = (W.w gain + W.w loose) + ∑ x ∈ S, W.w x := by
      rw[←Finset.sum_add_sum_compl (filter (fun x => x = gain ∨ x = loose) univ)]
      rw[Finset.filter_or]
      rw[Finset.sum_union]
      ·
        have gain_filter : filter (fun x => x = gain) univ = {gain} := by
          ext x
          simp[Finset.mem_filter, Finset.mem_univ]
        have loose_filter : filter (fun x => x = loose) univ = {loose} := by
          ext x
          simp[Finset.mem_filter, Finset.mem_univ]
        rw[gain_filter]
        rw[loose_filter]
        rw[Finset.sum_singleton]
        rw[Finset.sum_singleton]
        -- Proof that complement of {gain} AND {loose} is S
        have compl_eq : ({gain} ∪ {loose})ᶜ = S := by
          ext x
          simp [Finset.mem_compl, Finset.mem_union, Finset.mem_singleton, S]
        rw[compl_eq]
      -- Proof {gain} and {loose} are disjoint
      · rw[Finset.disjoint_left]
        intros x hx h'x
        rw[Finset.mem_filter] at hx h'x
        have contra : gain = loose := by
          rw[←hx.2, h'x.2]
        exact h_neq contra
    have filter_eq_S : filter (fun a => ¬a = loose ∧ ¬a = gain) univ = S := by
      ext x
      simp[Finset.mem_filter]
      constructor
      · intro h
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ x, ⟨h.2, h.1⟩⟩
      · intro h
        rw [Finset.mem_filter] at h
        exact ⟨h.2.2, h.2.1⟩
    rw[filter_eq_S]
    rw[←h_sum]
    rw[remember]

-- if an edge e is connceted to vertex gain --> gain ∈ e
lemma mini_help (e : Sym2 α) (he : e ∈ G.incidenceFinset gain) :
  gain ∈ e := by
  rw [mem_incidenceFinset] at he
  let e' : G.edgeSet := ⟨e, G.incidenceSet_subset _ he⟩
  have wow : ↑e' ∈ G.incidenceSet gain := he
  rw [edge_mem_incidenceSet_iff] at wow
  exact wow

-- Product of weights for an edge e "connected to gain" as wegith of gain * weight of the other vertices connected to gain
lemma Improve_does_its_thing_part_help_0 (W : FunToMax G) (gain : α)
  (e : Sym2 α) (he : e ∈ G.incidenceFinset gain) :
  vp W.w e = (W.w gain) * (W.w (Sym2.Mem.other (mini_help G e he))) := by
  revert he
  apply @Sym2.inductionOn α (fun e => ∀ he : e ∈ G.incidenceFinset gain, vp W.w e = (W.w gain) * (W.w (Sym2.Mem.other (mini_help G e he))))
  intro x y he
  dsimp [vp]
  have help := (Sym2.other_spec (mini_help _ _ he))
  --rw [← help]  -- don't know  why this fails ...
  -- I'm not expecting you to come up with ↓ ; If you get stuck, tell me
  apply @Eq.ndrec _ (s(gain, Sym2.Mem.other (mini_help G s(x, y) he))) (fun X =>
    Quot.liftOn X (fun pair => W.w pair.1 * W.w pair.2) (vp.proof_1 W.w) = W.w gain * W.w (Sym2.Mem.other (mini_help G s(x, y) he))
    ) _ s(x,y) help
  rw [Quot.liftOn_mk]

-- sum of vp W.w e = W.w gain * sum
lemma Improve_does_its_thing_part_help_1 (W : FunToMax G) (gain : α) :
    ∑ e∈G.incidenceFinset gain, vp W.w e =
    (W.w gain) * ∑ e∈(G.incidenceFinset gain).attach, W.w (Sym2.Mem.other (mini_help G e.val e.prop)) := by
  rw [mul_sum]
  rw [← sum_attach]
  apply sum_congr
  · rfl
  · intro x _
    apply Improve_does_its_thing_part_help_0 _ _ gain _ x.prop

lemma Improve_does_its_thing_part_0 {loose gain : α}
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  Disjoint (G.incidenceFinset gain) (G.incidenceFinset loose) := by
    simp_rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem, mem_inter]
    rintro x ⟨xg,xl⟩
    rw [incidenceFinset_eq_filter, mem_filter, mem_edgeFinset] at *
    apply h_adj
    rw [adj_iff_exists_edge]
    exact ⟨h_neq,⟨x,xg.1,xg.2,xl.2 ⟩⟩

lemma edge_mem_iff {v w : α} : G.Adj v w ↔ ∃ e ∈ G.edgeSet, e = Sym2.mk (v, w) := by
  constructor
  · intro h
    use Sym2.mk (v, w)
    simp [h]
  · rintro ⟨e, he, rfl⟩
    simp at he
    exact he

lemma incidenceFinset_subset (v : α) : G.incidenceFinset v ⊆ G.edgeFinset := by
  intro e he
  simp [incidenceFinset] at he
  rw [mem_edgeFinset]
  exact he.1

lemma Improve_does_its_thing_part_1 (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  let changed :=
    disjUnion
      (G.incidenceFinset gain)
      (G.incidenceFinset loose)
      (Improve_does_its_thing_part_0 G h_neq h_adj)
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

lemma Improve_does_its_thing_part_2 (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  let changed :=
    disjUnion
      (G.incidenceFinset gain)
      (G.incidenceFinset loose)
      (Improve_does_its_thing_part_0 G h_neq h_adj)
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
        := by rw [Finset.sum_union (Improve_does_its_thing_part_0 G h_neq h_adj)]
    _ = ∑ e∈G.incidenceFinset gain, vp W.w e
        + ∑ e∈G.incidenceFinset loose, vp W.w e
        + ∑ e∈(G.edgeFinset \ changed), vp W.w e
        := by rw [add_assoc]

@[simp]
lemma Improve_w_eq (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  (Improve G W loose gain h_neq).w = (fun i => if i = loose then 0 else if i = gain then W.w gain + W.w loose else W.w i) :=
by rfl

lemma Improve_does_its_thing_part_3 (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
    ∑ e∈G.incidenceFinset gain, vp (Improve G W loose gain h_neq).w e =
    ∑ e∈G.incidenceFinset gain, vp W.w e
    + (W.w loose)
      * ∑ e∈(G.incidenceFinset gain).attach, W.w (Sym2.Mem.other (mini_help G e.val e.prop)) := by
    rw [mul_sum, ← sum_attach]
    nth_rewrite 2 [← sum_attach]
    rw [← sum_add_distrib]
    apply sum_congr
    · rfl
    · intro x xdef
      have tec := Subtype.prop x
      revert tec
      have tec2 : (↑x ∈ G.incidenceFinset gain → vp (Improve G W loose gain h_neq).w ↑x = vp W.w ↑x + W.w loose * W.w (Sym2.Mem.other (mini_help G (↑x) (Subtype.prop x))))
        = ((P : ↑x ∈ G.incidenceFinset gain) → vp (Improve G W loose gain h_neq).w ↑x = vp W.w ↑x + W.w loose * W.w (Sym2.Mem.other (mini_help G (↑x) (P)))) :=
          by exact rfl
      rw [tec2]
      clear tec2
      apply @Sym2.inductionOn _ (fun X => ∀ (P : X ∈ G.incidenceFinset gain),
  vp (Improve G W loose gain h_neq).w X = vp W.w X + W.w loose * W.w (Sym2.Mem.other (mini_help G X P )))
      intro y z Pyz
      dsimp [vp,Quot.liftOn, Improve]
      have help := Sym2.mk_eq_mk_iff.mp (Sym2.other_spec (mini_help _ _ Pyz))
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
            -- use convert when patterns don't really exactly match, but morally match
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

@[simp]
lemma vp_sym2_mk (w : α → NNReal) (a b : α) :
    vp w (Sym2.mk (a, b)) = w a * w b := by
  dsimp [vp]

lemma Improve_loose_weight_zero (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  (Improve G W loose gain h_neq).w loose = 0 := by
  dsimp [Improve]
  simp only [if_pos rfl]
  split_ifs
  · rfl
  · rfl

lemma Improve_does_its_thing_part_4 (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) :
    ∑ e∈G.incidenceFinset loose, vp (Improve G W loose gain h_neq).w e = 0 := by
  let newW := (Improve G W loose gain h_neq).w
  have hl : newW loose = 0 := Improve_loose_weight_zero G W loose gain h_neq
  apply Finset.sum_eq_zero
  intro e he
  have h_mem : loose ∈ e := by
    exact mini_help G e he
  rcases Sym2.mem_iff_exists.mp h_mem with ⟨x, h_or⟩
  rcases h_or with rfl | rfl
  rw [vp_sym2_mk newW loose x, hl]
  simp

lemma Improve_does_its_thing_part_5 (W : FunToMax G) (loose : α) :
  ∑ e∈G.incidenceFinset loose, vp W.w e =
  (W.w loose)
    * ∑ e∈(G.incidenceFinset loose).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop))) := by
  apply Improve_does_its_thing_part_help_1

lemma Improve_does_its_thing_part_7 (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  let changed :=
    disjUnion
      (G.incidenceFinset gain)
      (G.incidenceFinset loose)
      (Improve_does_its_thing_part_0 G h_neq h_adj)
  ∑ e∈(G.edgeFinset \ changed), vp (Improve G W loose gain h_neq).w e
  = ∑ e∈(G.edgeFinset \ changed), vp W.w e :=
by
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

lemma Improve_does_its_thing (W : FunToMax G) (loose gain : α)
  (h : ∑ e∈(G.incidenceFinset gain).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop))) ≥
    ∑ e∈(G.incidenceFinset loose).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop))))
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  (Improve G W loose gain h_neq).fw ≥ W.fw := by
  simp_rw [FunToMax.fw]
  rw [Improve_does_its_thing_part_2 G (Improve G W loose gain h_neq) loose gain h_neq h_adj]
  rw [Improve_does_its_thing_part_2 G W loose gain h_neq h_adj]
  rw [Improve_does_its_thing_part_7 G W loose gain h_neq h_adj]
  apply add_le_add_right
  rw [Improve_does_its_thing_part_3 G W loose gain h_neq h_adj, Improve_does_its_thing_part_4 G W loose gain h_neq]
  rw [add_zero]
  apply add_le_add_left
  rw [Improve_does_its_thing_part_5]
  apply mul_le_mul_of_nonneg_left h (by exact zero_le (W.w loose))

lemma ImproveReducesSupport (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_supp : 0 < W.w gain) : -- will be `xdef`∈`BetterFormsClique`
  ∀ i, W.w i = 0 → (Improve G W loose gain h_neq).w i = 0 := by
  intro i h_zero
  simp only [Improve, FunToMax.w]
  split_ifs with _ H
  · rfl
  · rw [H] at h_zero
    rw [h_zero] at h_supp
    exfalso
    apply lt_irrefl 0 h_supp
  · exact h_zero

lemma ImproveReducesSupportSize (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_supp1 : 0 < W.w gain) -- will be `xdef`∈`BetterFormsClique`
  (h_supp2: 0 < W.w loose) : -- will be `ydef`∈`BetterFormsClique`
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
        exact ImproveReducesSupport G W loose gain h_neq h_supp1 x xmem

lemma BetterFormsClique (W : FunToMax G) : G.IsClique ((Finset.univ : Finset α).filter (fun i => (Better G W).w i > 0)) := by
  by_contra con
  dsimp [IsClique, Set.Pairwise] at con
  push_neg at con
  obtain ⟨x,xdef,y,ydef,xny,xyAdj⟩ := con
  wlog wlog : ∑ e∈(G.incidenceFinset x).attach, ((Better G W).w (Sym2.Mem.other (mini_help G e.val e.prop)))
                ≥ ∑ e∈(G.incidenceFinset y).attach, ((Better G W).w (Sym2.Mem.other (mini_help G e.val e.prop)))  with SymCase
  · push_neg at wlog
    specialize SymCase G W y ydef x xdef (ne_comm.mp xny) (by rw [G.adj_comm] ; exact xyAdj)
    have H : ∑ e∈(G.incidenceFinset y).attach, (Better G W).w (Sym2.Mem.other (mini_help G e.val e.prop))
      ≥ ∑ e∈(G.incidenceFinset x).attach, (Better G W).w (Sym2.Mem.other (mini_help G e.val e.prop)) := le_of_lt wlog
    exact SymCase H
    -- use `le_of_lt`
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
          apply ImproveReducesSupport
          · have h_x_pos : (Better G W).w x > 0 := (Finset.mem_filter.mp xdef).2
            exact h_x_pos -- xdef
          · apply BetterSupportIncluded _ _ _ wi
        · constructor
          · rfl
          · apply le_trans (BetterHigher _ W)
            exact Improve_does_its_thing G (Better G W) y x wlog xny xyAdj
    have ohoh := @Nat.find_le (#(filter (fun i => (Improve G (Better G W) y x xny).w i > 0) univ)) _ _ (help G W) con
    have nono := ImproveReducesSupportSize G (Better G W) y x xny h_pos_x h_pos_y
    rw [BetterSupportSize G W] at nono
    apply not_lt_of_le ohoh nono

-- Part 2 of the proof starts here: we show that the weights are all equal, on the clique

-- We'll use a similar workarround as before, because using the existent notions of compacity
-- to justify the existence of a max are a pain∈the ass. For a given W who's support forms a k-clique,
-- we'll consider the largest number for which there is a FunToMax with same support who's
-- number of nodes at weight 1/k is that number.
-- Such numbers exist (possibly 0 if `(Better G W)` has no weights equal to 1/k)
-- We will then show that this number must be the size of the support:
-- if it weren't, we'll have to argue that the minimum weight w_min and the maximum
-- weight w_max satisfy w_min < 1/k < w_max (else, take sum and contradict W.h_w).
-- With them we'll use the improving argument from the book, with ε = w_max - 1/k
-- (it satisfies > 0 and < w_max-w_min), so that∈the new wieghts, there will be
-- one more node with weight 1/k, namely the one that had weight w_max.
-- This will contradict maximality of number of nodes with weight 1/k

#check Nat.findGreatest

lemma supportSizeNotZero (W : FunToMax G) : ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card ≠ 0 := by
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

@[reducible]
def help3 (W : FunToMax G) :=
  (fun m =>
    ∃ better : FunToMax G,
      (∀ i, W.w i = 0 ↔ better.w i = 0) ∧ -- support same
      (G.IsClique ((Finset.univ : Finset α).filter (fun i => better.w i > 0))) ∧ -- support also forms clique
      (((Finset.univ : Finset α).filter (fun i => better.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card = m) ∧ -- number of weights being 1/k is m
      (W.fw ≤ better.fw) -- has better weights
      )



open Classical

noncomputable
-- Largest number m, such that there is a FunToMax that has support∈that of W,
-- has a support that forms a k-clique, has better total weight,
-- and has m weights that evaluate to 1/k
def S (W : FunToMax G) :=
  Nat.findGreatest (help3 G W) ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card

lemma help4 (W : FunToMax G)
  (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  (fun m =>
    ∃ better : FunToMax G,
      (∀ i, W.w i = 0 ↔ better.w i = 0) ∧ -- support same
      (G.IsClique ((Finset.univ : Finset α).filter (fun i => better.w i > 0))) ∧ -- support also forms clique
      (((Finset.univ : Finset α).filter (fun i => better.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card = m) ∧ -- number of weights being 1/k is m
      (W.fw ≤ better.fw) -- has better weights
      ) (S G W)
    :=
    @Nat.findGreatest_spec ((Finset.univ : Finset α).filter (fun i => W.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card (help3 G W) _
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
            @supportSizeNotZero α G (inferInstance : Fintype α)
            (inferInstance : DecidableEq α) (inferInstance : DecidableRel G.Adj) W
          have j_pos : j > 0 := Nat.pos_of_ne_zero j_nonzero
          rw [div_eq_mul_inv]
          rw [one_mul]
          have h1 : ((j : NNReal)⁻¹) = 1 / (j : NNReal) := by rw [inv_eq_one_div]
          rw [h1]
          have h_j_pos : (j : NNReal) > 0 := by exact_mod_cast j_pos
          have h1_real : (1 : ℝ) / ((j : NNReal) : ℝ) > 0 := div_pos zero_lt_one (by exact_mod_cast j_pos)
          exact_mod_cast h1_real
        )
      (by
        dsimp [help3]
        use W
        constructor
        · intro i
          exact Iff.rfl
        constructor
        · exact hW
        constructor
        · rfl
        · exact le_refl W.fw
        )

noncomputable
def EvenBetter (W : FunToMax G) (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) : FunToMax G := Classical.choose (help4 G W hW)

lemma EvenBetterSupportIncluded (W : FunToMax G) (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (i : α) : W.w i = 0 ↔ (EvenBetter G W hW).w i = 0 :=
  (Classical.choose_spec (help4 G W hW)).1 i

lemma EvenBetterSupportSize (W : FunToMax G) (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) : ((Finset.univ : Finset α).filter (fun i => (EvenBetter G W hW).w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card = (S G W) :=
  (Classical.choose_spec (help4 G W hW)).2.2.1

lemma EvenBetterHigher (W : FunToMax G) (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) : W.fw ≤ (EvenBetter G W hW).fw :=
  (Classical.choose_spec (help4 G W hW)).2.2.2

lemma EvenBetterClique (W : FunToMax G) (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) : G.IsClique ((Finset.univ : Finset α).filter (fun i => (EvenBetter G W hW).w i > 0)) :=
  (Classical.choose_spec (help4 G W hW)).2.1

noncomputable
def Enhance (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) : FunToMax G where
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
        -- hx : x ∈ univ ∧ (x ≠ loose ∧ x ≠ gain)
        by_cases hxl : x = loose
        · exfalso
          rw[hxl] at hx
          have mem_union : loose ∈ {loose} ∪ {gain} := Finset.mem_union_left {gain} (Finset.mem_singleton_self loose)
          exact hx.2 mem_union
        by_cases hxg : x = gain
        ·
          exfalso
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
      _ = (∑ x∈{loose} ∪ {gain}, W.w x) + (univ \ ({loose} ∪ {gain})).sum W.w :=
        by
          rw [Finset.sum_union disj2, Finset.sum_singleton, Finset.sum_singleton]
      _ = ∑ x∈({loose} ∪ {gain}) ∪ (univ \ ({loose} ∪ {gain})), W.w x :=
        by rw [← split_univ, Finset.sum_union (Finset.disjoint_sdiff)]
      _ = ∑ x∈univ, W.w x :=
        by rw [← eq_S, split_univ]
      _ = 1 :=
        by exact W.h_w

lemma neq_of_W_lt {W : FunToMax G} {loose gain : α} (h_neq : W.w gain < W.w loose) : gain ≠ loose :=
  by
  intro con
  rw [con] at h_neq
  apply lt_irrefl _ h_neq

example (h : ¬ (a = 0)) : a ≠ 0 :=
by
  change ¬ (a = 0)
  exact h

-- added assumption ah to help in the case h_loose : ¬i = loose, h_gain : i = gain
lemma EnhanceSupport (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) (ah : 0 < W.w gain)
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

#check tsub_eq_zero_iff_le

lemma NNReal.eq_zero_of_ne_pos {x : NNReal} (h : ¬ x > 0) : x = 0 := by
  rw [← NNReal.coe_inj, eq_comm]
  simp_rw [← NNReal.coe_pos] at h
  have := x.prop
  apply eq_of_le_of_not_lt this h

lemma EnhanceSupport' (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) (ah : 0 < W.w gain)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ i, W.w i > 0 ↔ (Enhance G W loose gain h_lt ε epos elt).w i > 0 := by
    intro i
    rw [← not_iff_not]
    constructor
    · intro h
      intro con
      replace h := NNReal.eq_zero_of_ne_pos  h
      rw [EnhanceSupport G W loose gain h_lt ah ε epos elt] at h
      rw [h] at con
      exact lt_irrefl _ con
    · intro h
      intro con
      replace h := NNReal.eq_zero_of_ne_pos  h
      rw [← EnhanceSupport G W loose gain h_lt ah ε epos elt] at h
      rw [h] at con
      exact lt_irrefl _ con

lemma EnhanceCliquePractical (W : FunToMax G)
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

#check SimpleGraph.ne_of_adj

lemma EnhanceClique (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) (ah : 0 < W.w gain)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0)))   :
  G.IsClique ((Finset.univ : Finset α).filter (fun i => (Enhance G W loose gain h_lt ε epos elt).w i > 0)) := by
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
    rw [← EnhanceSupport' G W loose gain h_lt ah ε epos elt] at xPosNew yPosNew
    apply hc
    · simp only [gt_iff_lt, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] -- via simp?
      exact xPosNew
    · simp only [gt_iff_lt, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] -- via simp?
      exact yPosNew
    · exact xny


#check Quot.lift

def Sym2.inSupport (W : FunToMax G) (e : Sym2 α) : Prop :=
  @Quot.lift _ (Sym2.Rel α) Prop (fun x => W.w x.1 > 0 ∧ W.w x.2 > 0)
    (by
     intro a b rel
     dsimp
     --apply propext
     rw [Sym2.rel_iff'] at rel
     cases' rel with rel rel
     · rw [rel]
     · rw [rel]
       dsimp
       nth_rewrite 1 [and_comm]
       rfl
     ) e

lemma Sym2.inSupport_explicit (W : FunToMax G) {x y : α} : s(x,y).inSupport G W ↔ (W.w x > 0 ∧ W.w y > 0) := by
  dsimp [inSupport]
  rfl


lemma Sym2.inSupport_mem (W : FunToMax G) {x : α} {e : Sym2 α} (hm : x ∈ e) (hs : e.inSupport G W) : W.w x > 0 := by
  revert hs hm
  apply @Sym2.ind _ (fun e => x ∈ e → inSupport G W e → W.w x > 0)
  intro y z hm hs
  rw [Sym2.mem_iff] at hm
  rw [Sym2.inSupport_explicit] at hs
  cases' hm with hm hm
  · rw [hm] ; exact hs.1
  · rw [hm] ; exact hs.2

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

lemma Sym2.inSupport_rec (W : FunToMax G) {e : Sym2 α} (h : ∀ x ∈ e, W.w x > 0) : e.inSupport G W := by
  revert h
  apply @Sym2.ind _ (fun e => (∀ x ∈ e, W.w x > 0) → e.inSupport G W) _ e
  intro x y h
  rw [Sym2.inSupport_explicit]
  exact ⟨h x (Sym2.mem_mk_left _ _), h y (Sym2.mem_mk_right _ _)⟩

noncomputable
def SimpleGraph.supIncidenceFinset (W : FunToMax G) (v : α) :=
  (G.incidenceFinset v).filter (Sym2.inSupport G W)

noncomputable
def SimpleGraph.supEdgeFinset (W : FunToMax G) :=
  G.edgeFinset.filter (Sym2.inSupport G W)

lemma SimpleGraph.mem_supIncidenceFinset {W : FunToMax G} {v : α} {e : Sym2 α} :
  e ∈ G.supIncidenceFinset W v ↔ e ∈ (G.incidenceFinset v) ∧ e.inSupport G W := by
  dsimp [supIncidenceFinset] ; rw [mem_filter]

lemma SimpleGraph.mem_supEdgeFinset {W : FunToMax G} {e : Sym2 α} :
  e ∈ G.supEdgeFinset W ↔ e ∈ (G.edgeFinset) ∧ e.inSupport G W := by
  dsimp [supEdgeFinset] ; rw [mem_filter]

lemma SimpleGraph.small_helpI {W : FunToMax G} {v : α} {e : Sym2 α} (h : e ∈ G.supIncidenceFinset W v) :
  e ∈ (G.incidenceFinset v) := by
  rw [mem_supIncidenceFinset] at h ; exact h.1

lemma SimpleGraph.small_helpE {W : FunToMax G} {e : Sym2 α} (h : e ∈ G.supEdgeFinset W) : e ∈ (G.edgeFinset) := by
  rw [mem_supEdgeFinset] at h ; exact h.1

lemma supIncidenceFinset_subset (W : FunToMax G) (v : α) :
  (G.supIncidenceFinset W v) ⊆ G.incidenceFinset v :=
Finset.filter_subset (fun e => Sym2.inSupport G W e) (G.incidenceFinset v)

lemma EnhanceIsBetter_part_1 (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  Disjoint ((G.supIncidenceFinset W gain) \ {s(loose,gain)}) ((G.supIncidenceFinset W loose) \ {s(loose,gain)}) := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
  intro x hx
  -- dsimp at hx
  let h_int := Finset.mem_inter.mp hx
  let h_gain := Finset.mem_sdiff.mp h_int.left
  let h_loose := Finset.mem_sdiff.mp h_int.right
  have h_loose_inc : x ∈ G.incidenceFinset loose :=
  ((SimpleGraph.mem_supIncidenceFinset (W := W) (v := loose) (e := x)).mp h_loose.left).1
  have h_gain_inc : x ∈ G.incidenceFinset gain :=
  ((SimpleGraph.mem_supIncidenceFinset (W := W) (v := gain) (e := x)).mp h_gain.left).1
  have h_both : loose ∈ x ∧ gain ∈ x := ⟨mini_help G x h_loose_inc, mini_help G x h_gain_inc⟩
  apply h_gain.2
  rw [mem_singleton]
  apply Sym2.eq_of_ne_mem h_neq h_both.2 h_both.1
  · apply Sym2.mem_mk_right
  · apply Sym2.mem_mk_left


noncomputable
def InciLooseGain (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) : Finset (Sym2 α) :=
  disjUnion
    ((G.supIncidenceFinset W gain) \ {s(loose,gain)})
    ((G.supIncidenceFinset W loose) \ {s(loose,gain)})
    (EnhanceIsBetter_part_1 G W loose gain h_neq)

lemma EnhanceIsBetter_part_2 (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  Disjoint (InciLooseGain G W loose gain h_neq) {s(loose,gain)} := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
  intro x
  rw [Finset.mem_inter]
  rintro ⟨x_in_inci, x_in_singleton⟩
  rw [Finset.mem_singleton] at x_in_singleton
  subst x_in_singleton
  rw [InciLooseGain, Finset.mem_disjUnion] at x_in_inci
  cases x_in_inci
  case inl leftMem =>
    rw [Finset.mem_sdiff] at leftMem
    exact leftMem.2 (Finset.mem_singleton_self _)
  case inr rightMem =>
    rw [Finset.mem_sdiff] at rightMem
    exact rightMem.2 (Finset.mem_singleton_self _)

noncomputable
def InciLooseGainFull (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) : Finset (Sym2 α) :=
  disjUnion
    (InciLooseGain G W loose gain h_neq) {s(loose,gain)}
    (EnhanceIsBetter_part_2 G W loose gain h_neq)

lemma EnhanceIsBetter_part_3 (W : FunToMax G) (loose gain : α) (h_adj : G.Adj gain loose) :
  G.supEdgeFinset W = -- you're gonna hat me for this ; sorry
    disjUnion (InciLooseGainFull G W loose gain (G.ne_of_adj h_adj)) (G.supEdgeFinset W \ (InciLooseGainFull G W loose gain (G.ne_of_adj h_adj)))
      (disjoint_sdiff) := by
  rw [Finset.disjUnion_eq_union]
  ext e
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_coe]
  apply Iff.intro
  · intro he
    by_cases hin : e ∈ InciLooseGainFull G W loose gain (G.ne_of_adj h_adj)
    · exact Or.inl hin
    · right
      constructor
      · exact he
      · exact hin
  · intro he
    cases he with
    | inl h_in =>
      unfold supEdgeFinset
      unfold InciLooseGainFull InciLooseGain supIncidenceFinset at h_in
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
        ·
          rw [Sym2.inSupport_explicit]
          rw [← SimpleGraph.adj_comm] at h_adj
          rcases (@edge_mem_iff α G _ _).mp h_adj with ⟨e, he, heq⟩
          rw [heq] at he
          constructor
          ·
            sorry
          ·
            sorry
    | inr h =>
      exact h.1

lemma EnhanceIsBetter_part_4 (W : FunToMax G) (loose gain : α) (h_adj : G.Adj gain loose) :
  ∑ e∈G.supEdgeFinset W, vp W.w e =
    ((∑ e∈((G.supIncidenceFinset W gain) \ {s(loose,gain)}) , vp W.w e +
      ∑ e∈((G.supIncidenceFinset W loose) \ {s(loose,gain)}) , vp W.w e) +
     ∑ e∈{s(loose,gain)}, vp W.w e) +
    ∑ e∈(G.supEdgeFinset W \ (InciLooseGainFull G W loose gain (G.ne_of_adj h_adj))), vp W.w e := by
  rw [EnhanceIsBetter_part_3 G W loose gain h_adj]
  rw [Finset.sum_disjUnion disjoint_sdiff]
  rw [InciLooseGainFull, Finset.disjUnion_eq_union]
  rw [Finset.sum_union (EnhanceIsBetter_part_2 G W loose gain (G.ne_of_adj h_adj))]
  rw [InciLooseGain, Finset.disjUnion_eq_union]
  rw [Finset.sum_union (EnhanceIsBetter_part_1 G W loose gain (G.ne_of_adj h_adj))]
  rw [Finset.disjUnion_eq_union]
  rw [Finset.union_sdiff_of_subset]
  intro e eMem
  rw [Finset.mem_union, Finset.mem_union, or_assoc] at eMem
  -- rcases eMem with (memGain | memLoose | memSingleton)
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
        -- rcases Sym2.mem_iff.mp slg with (rfl | rfl)
        apply pos_iff_ne_zero.mpr
        intro w0
        have hx_or : x = loose ∨ x = gain := Sym2.mem_iff.mp slg
      ------------------
        let mem_in_filter := s(loose, gain) ∈ G.edgeFinset.filter (Sym2.inSupport G W)
        have hInSup : s(loose, gain).inSupport G W := by
          rw [Sym2.inSupport_explicit]
          by_cases h : W.w loose = 0
          · sorry
          · sorry
        cases hx_or with
        | inl hxl =>
          rw [hxl] at w0
          rw [Sym2.inSupport_explicit] at hInSup
          exact (pos_iff_ne_zero.mp hInSup.left) w0
        | inr hxg =>
          rw [hxg] at w0
          rw [Sym2.inSupport_explicit] at hInSup
          exact (pos_iff_ne_zero.mp hInSup.right) w0

lemma Sym2.inSupport_vp (W : FunToMax G) {e : Sym2 α} (h : ¬ e.inSupport G W ) : vp W.w e = 0 := by
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

lemma EnhanceIsBetter_part_4_and_a_half (W : FunToMax G) (loose gain : α) (h_adj : G.Adj gain loose) :
  ∑ e∈G.edgeFinset, vp W.w e = ∑ e∈G.supEdgeFinset W, vp W.w e := by
  rw [eq_comm]
  apply sum_subset
  · unfold supEdgeFinset
    apply filter_subset
  · intro x xInEdges xNotSup
    rw [mem_supEdgeFinset] at xNotSup
    apply Sym2.inSupport_vp
    intro supp
    apply xNotSup
    exact ⟨xInEdges, supp⟩

lemma tiny_help {s t : Finset α} {a : α} (h : a ∈ s \ t) : a ∈ s := by
  rw [Finset.mem_sdiff] at h; exact h.1

lemma EnhanceIsBetter_part_5 (W : FunToMax G) (gain : α) (dummy : Sym2 α)
  (e : Sym2 α) (he : e ∈ ((G.supIncidenceFinset W gain) \ {dummy})) :
  vp W.w e = (W.w gain) * (W.w (Sym2.Mem.other (mini_help G e (G.small_helpI (tiny_help he))))) := by
  rw [Finset.mem_sdiff] at he
  convert (Improve_does_its_thing_part_help_0 G W gain e (G.small_helpI he.1))

-- sum of vp W.w e = W.w gain * sum
lemma EnhanceIsBetter_part_6 (W : FunToMax G) (gain : α) (dummy : Sym2 α) :
    ∑ e∈((G.supIncidenceFinset W gain) \ {dummy}), vp W.w e =
    (W.w gain) * ∑ e∈((G.supIncidenceFinset W gain) \ {dummy}).attach, W.w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))) := by
  rw [mul_sum]
  rw [← sum_attach]
  apply sum_congr
  · rfl
  · intro x _
    apply EnhanceIsBetter_part_5 _ _ gain dummy _ x.prop

-- any e∈incidence set of vertex gain withouth elg = loosegain is unchanged after applying Enhance
lemma EnhanceIsBetter_part_7_help (W : FunToMax G) (loose: α) (gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ e ∈ ((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach,
    (Enhance G W loose gain h_lt ε epos elt).w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))) =
    W.w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))) := by
  intro e he
  let x := Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))
  dsimp [Enhance] at *
  have h_loose_nonneg : 0 ≤ W.w loose := (W.w loose).prop
  have h_gain_le : W.w gain ≤ W.w loose := le_of_lt h_lt
  have h_tec : ε ≤ W.w loose := by
            replace elt := add_le_of_le_tsub_left_of_le (le_of_lt h_lt) (le_of_lt elt)
            apply le_trans (le_add_of_nonneg_left (W.w gain).prop) elt
  split_ifs with h_xloose h_xgain
  · exfalso
    have := Sym2.other_spec (mini_help G e.val (G.small_helpI (tiny_help e.prop)))
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
    -- use `s(x, y) ∈ G.supIncidenceFinset W gain` and evetually `mem_edgeSet`, as usual
  · rfl

lemma EnhanceIsBetter_part_7 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∑ e∈((G.supIncidenceFinset W gain) \ {s(loose,gain)}), vp (Enhance G W loose gain h_lt ε epos elt).w e =
  ∑ e∈((G.supIncidenceFinset W gain) \ {s(loose,gain)}), vp W.w e +
  ε * ∑ e∈((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))) := by
  rw [mul_sum, ← sum_attach]
  let S := G.supIncidenceFinset W gain \ {s(loose, gain)}
  rw [← Finset.sum_attach S (λ e => vp W.w e)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  -- rw[EnhanceIsBetter_part_7_help]
  simp[vp]
  simp[Quot.liftOn]

  sorry


lemma EnhanceIsBetter_part_8_help (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach,
    (Enhance G W loose gain h_lt ε epos elt).w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))) =
    W.w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))) := by
  intro e he
  let edge : Sym2 α := e.val
  let v : α := Sym2.Mem.other (mini_help G edge (G.small_helpI (tiny_help e.prop)))
  have h_edge : edge ∈ G.supIncidenceFinset W loose :=
    (Finset.mem_sdiff.mp e.prop).1
  have h_edge_ne : edge ∉ {s(loose, gain)} :=
    (Finset.mem_sdiff.mp e.prop).2
  have h_loose : loose ∈ edge :=
    mini_help G edge (G.small_helpI (tiny_help e.prop))
  dsimp[Enhance]
  split_ifs with h_vloose h_vgain
  have this_should_be_a_lemma : ε < W.w loose := by
    apply lt_of_lt_of_le elt ; exact tsub_le_self
    -- Similar contradictionas∈EnhanceSupport !
  ·
    rw [h_vloose]
    have hpos : 0 < (ε : ℝ) := by exact_mod_cast epos


    sorry
  ·

    sorry
  · rfl

lemma EnhanceIsBetter_part_8 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∑ e∈((G.supIncidenceFinset W loose) \ {s(loose,gain)}), vp (Enhance G W loose gain h_lt ε epos elt).w e =
  ∑ e∈((G.supIncidenceFinset W loose) \ {s(loose,gain)}), vp W.w e -
  ε * ∑ e∈((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))) := by
  rw [mul_sum]
  have h_tec : ε ≤ W.w loose := by
            replace elt := add_le_of_le_tsub_left_of_le (le_of_lt h_lt) (le_of_lt elt)
            apply le_trans (le_add_of_nonneg_left (W.w gain).prop) elt

  sorry
/-
For ↑ use ↓
Will require `∀ e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}), vp W.w e ≥ ε*W.w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop))))`
Recall that `vp W.w e = (W.w loose) * (W.w (other ...))`, so this follows from `ε ≤ W.w loose` which should follow from assumption `elt`
-/
#check sum_tsub_distrib

--#exit

#check sum_attach

-- will be used∈at EnhanceIsBetter_part_9
-- it is a bijection between the edges incident to loose and those incident to gain:
-- since we're∈a clique, to each edge incident to loose, consider the other vertex, and return its edge with gain
noncomputable
def the_bij (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  (e : { x // x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} }) → (e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach) → { x // x ∈ G.supIncidenceFinset W gain \ {s(loose, gain)} } :=
  fun e h =>
    ⟨(s(gain,(Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))))),
     (by
        have e_mem : e.val ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} := e.property
        rw [Finset.mem_sdiff] at e_mem
        obtain ⟨he_sup, he_not⟩ := e_mem
        rw [SimpleGraph.mem_supIncidenceFinset] at he_sup
        obtain ⟨he_inc, he_supp⟩ := he_sup
        let other_v := Sym2.Mem.other (mini_help G e.val he_inc)
        have other_mem : other_v ∈ e.val := Sym2.other_mem (mini_help G e.val he_inc)
        have adj_new : G.Adj gain other_v := sorry
        have gain_mem : gain ∈ s(gain, other_v) := Sym2.mem_mk_left gain other_v
        have new_edge_in_incidence : s(gain, other_v) ∈ G.incidenceFinset gain := by
          rw [SimpleGraph.mem_incidenceFinset]
          exact ⟨adj_new, gain_mem⟩

        sorry
     )⟩

lemma the_bij_maps (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
    ∀ (e : { x // x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} })
      (he : e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach),
        (the_bij G W loose gain h_lt ε epos elt) e he ∈ ((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach := by
  intro e he
  apply mem_attach

lemma the_bij_inj (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
    ∀ (a₁ : { x // x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} })
      (ha₁ : a₁ ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach)
      (a₂ : { x // x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} })
      (ha₂ : a₂ ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach),
      (the_bij G W loose gain h_lt ε epos elt) a₁ ha₁ = (the_bij G W loose gain h_lt ε epos elt) a₂ ha₂ →
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
  -- disjoin cases ; `other` can't be `loose` due to `Sym2.other_ne` ; it can't be gain, else via `this` and `that` we contradict he₁ and he₂
  cases h1 with
  | inl h_eq =>
    left
    sorry
  | inr swapped =>
    sorry

#check Sym2.other_spec

lemma the_bij_surj (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
    ∀ b ∈ ((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach,
      ∃ a, ∃ (ha : a ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach),
        (the_bij G W loose gain h_lt ε epos elt) a ha = b := by
  intro b hb
  rcases b with ⟨e, he⟩
  let x := Sym2.Mem.other (mini_help G e (G.small_helpI (tiny_help he)))
  sorry

lemma the_bij_same (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ (e : { x // x ∈ G.supIncidenceFinset W loose \ {s(loose, gain)} })
      (he : e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach) ,
      (W.w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))))
      = (fun e => W.w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))))
        ((the_bij G W loose gain h_lt ε epos elt) e he) := by
  intro e he
  dsimp
  congr 1
  simp [the_bij]


  sorry


lemma EnhanceIsBetter_part_9 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∑ e∈((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))) =
  ∑ e∈((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (mini_help G e.val (G.small_helpI (tiny_help e.prop)))) :=
  by
  have h_bij : ∀ e ∈ ((G.supIncidenceFinset W loose) \ {s(loose,gain)}).attach,
    (the_bij G W loose gain h_lt ε epos elt) e (mem_attach _ e) ∈ ((G.supIncidenceFinset W gain) \ {s(loose,gain)}).attach :=
    fun e he => the_bij_maps G W loose gain h_lt ε epos elt e he
  apply Finset.sum_bij (the_bij G W loose gain h_lt ε epos elt)
    (the_bij_maps G W loose gain h_lt ε epos elt)
    (the_bij_inj G W loose gain h_lt ε epos elt)
    (the_bij_surj G W loose gain h_lt ε epos elt)
    (the_bij_same G W loose gain h_lt ε epos elt)

-- use ↓∈↑
-- #check sum_bij

--#exit

#check disjUnion_eq_union

lemma EnhanceIsBetter_part_10 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ e ∈ (G.supEdgeFinset W \ (InciLooseGainFull G W loose gain (neq_of_W_lt G h_lt))),
    vp (Enhance G W loose gain h_lt ε epos elt).w e = vp W.w e := by
  intro e he
  by_cases h_loose : loose ∈ e
  ·
    let ⟨h_sup, h_not_in_full⟩ := Finset.mem_sdiff.mp he
    have h_in_full : e ∈ InciLooseGainFull G W loose gain (neq_of_W_lt G h_lt) := by
      by_cases h_eq : e = s(loose, gain)
      ·
        have mem_sing : s(loose, gain) ∈ {s(loose, gain)} := Finset.mem_singleton_self (s(loose, gain))
      --   have mem_single : s(loose, gain) ∈ Finset.singleton (s(loose, gain)) :=
      -- Finset.mem_singleton_self (s(loose, gain))
        rw[h_eq]
        dsimp[InciLooseGainFull]
        rw[disjUnion_eq_union]

        sorry
      ·
        sorry
    exfalso
    exact h_not_in_full h_in_full
  ·
    by_cases h_gain: gain ∈ e
    ·
      sorry
    ·
      sorry

lemma EnhanceIsBetter_part_11 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∑ e∈(G.supEdgeFinset W \ (InciLooseGainFull G W loose gain (neq_of_W_lt G h_lt))), vp (Enhance G W loose gain h_lt ε epos elt).w e =
  ∑ e∈(G.supEdgeFinset W \ (InciLooseGainFull G W loose gain (neq_of_W_lt G h_lt))), vp W.w e := by
  apply Finset.sum_congr rfl
  intro e --he
  apply @Sym2.inductionOn _ (fun e => e ∈ G.supEdgeFinset W \ InciLooseGainFull G W loose gain (neq_of_W_lt G h_lt) → vp (Enhance G W loose gain h_lt ε epos elt).w e = vp W.w e)
  intro x y he
  dsimp [Enhance]


  /-
  With your initial approach, the following would have worked:

  apply @Sym2.inductionOn α
    (fun e => e ∈ G.supEdgeFinset W \ ((InciLooseGainFull G W loose gain) (neq_of_W_lt G h_lt))
       → Quot.liftOn e
            (fun pair =>
               (if pair.1 = loose then W.w loose - ε
                else if pair.1 = gain then W.w gain + ε else W.w pair.1) *
               (if pair.2 = loose then W.w loose - ε
                else if pair.2 = gain then W.w gain + ε else W.w pair.2))
           (vp.proof_1 fun i => if i = loose then W.w loose - ε else if i = gain then W.w gain + ε else W.w i )
          =
          Quot.liftOn e (fun pair => W.w pair.1 * W.w pair.2) (vp.proof_1 W.w))

  The reason your version didn't work is because you use a different proof instead of `vp.proof_1 ...`
  I don't know why the pattern matching algorithm fails here, because Lean should ignore that the proofs
  are different ...
  So when using induction principles, make sure to use the same proofs too : you can find them by hovering/clicking
  on the `⋯`∈the infoview.
  -/

  sorry



/-
So I did the overcomplicating.
In the informal proof, we don't actually need to do the computation.
We just need to show that the weight on the edge has increased, wich∈"Proofs from THE BOOK"
is implicit (skipped) after the weight is computed
Instead we'll just show ↓
Btw: h_neq should follow from h_lt (if loose and gain were equal, we'd contradict h_lt)
-/


lemma EnhanceIsBetter_part_12 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) (h_neq : gain ≠ loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  vp (Enhance G W loose gain h_lt ε epos elt).w s(loose,gain) > vp W.w s(loose,gain)  := by
  simp [vp, Quot.liftOn]
  simp [Enhance]
  rw [if_neg h_neq]
  ring_nf
  rw [mul_tsub]
  rw [lt_tsub_comm] at elt
  apply @lt_of_eq_of_lt _ _ (W.w gain * W.w loose - W.w gain * ε + W.w gain * ε)
  ·
    have := @tsub_add_cancel_iff_le _ _ _ _ _ _ (W.w gain * ε ) (W.w gain * W.w loose)
    rw [mul_comm, eq_comm]
    apply this.mpr
    sorry
  · apply add_lt_add_left
    apply mul_lt_mul_of_pos_right
    · exact elt
    · exact epos

lemma EnhanceIsBetter (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) (h_adj : G.Adj gain loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  W.fw ≤ (Enhance G W loose gain h_lt ε epos elt).fw := by
  simp_rw [FunToMax.fw]
  rw [EnhanceIsBetter_part_4_and_a_half G W loose gain h_adj, EnhanceIsBetter_part_3 G W loose gain h_adj]
  simp [Enhance]
  let A := InciLooseGainFull G W loose gain (neq_of_W_lt G h_lt)
  let S := G.supEdgeFinset W \ (InciLooseGainFull G W loose gain (neq_of_W_lt G h_lt))
  have h_S : ∀ e ∈ S, vp W.w e = vp (Enhance G W loose gain h_lt ε epos elt).w e :=
    fun e heS => (EnhanceIsBetter_part_10 G W loose gain h_lt ε epos elt e heS).symm
  have sum_S : ∑ e∈S, vp (Enhance G W loose gain h_lt ε epos elt).w e =
               ∑ e∈S, vp W.w e :=
    Finset.sum_congr rfl (fun e heS => Eq.symm (h_S e heS))
  let T := (G.supIncidenceFinset W gain \ {s(loose, gain)}).attach
  have h_T : ∑ e∈T, vp (Enhance G W loose gain h_lt ε epos elt).w e ≥
               ∑ e∈T, vp W.w e :=
    sorry

  sorry

#check Finset.image
#check Finset.max'_mem
#check Finset.min'
#check Finset.Nonempty
#check Finset.min'_le


lemma FunToMax.supp_nonempty (W : FunToMax G) : ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).Nonempty := by
  by_contra con
  simp [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at con
  have todo : ∑ v∈(Finset.univ : Finset α), W.w v = 0 := by
    simp_rw [con] ; apply sum_const_zero
  apply @one_ne_zero NNReal
  rw [← todo, W.h_w]
  -- should have used `supportSizeNotZero`

noncomputable
def FunToMax.max_weight (W : FunToMax G) :=
  Finset.max' (Finset.image W.w ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (by rw [image_nonempty] ; exact FunToMax.supp_nonempty G W)

lemma FunToMax.argmax_pre (W : FunToMax G) : ∃ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v = W.max_weight G := by
  rw [← mem_image] ; apply max'_mem

-- will become loose
noncomputable
def FunToMax.argmax (W : FunToMax G) :=
  Classical.choose (W.argmax_pre G)

lemma FunToMax.argmax_mem (W : FunToMax G) : (W.argmax G) ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)) :=
  (Classical.choose_spec (W.argmax_pre G)).1

lemma FunToMax.argmax_weight (W : FunToMax G) : W.w (W.argmax G) = W.max_weight G := by
  exact (Classical.choose_spec (W.argmax_pre G)).2

noncomputable
def FunToMax.min_weight (W : FunToMax G) :=
  Finset.min' (Finset.image W.w ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) (by rw [image_nonempty] ; exact FunToMax.supp_nonempty G W)

lemma FunToMax.argmin_pre (W : FunToMax G) : ∃ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v = W.min_weight G := by
  rw [← mem_image] ; apply min'_mem

-- will become gain
noncomputable
def FunToMax.argmin (W : FunToMax G) :=
  Classical.choose (W.argmin_pre G)

lemma FunToMax.argmin_mem (W : FunToMax G) : (W.argmin G) ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)) :=
  (Classical.choose_spec (W.argmin_pre G)).1

lemma FunToMax.argmin_weight (W : FunToMax G) : W.w (W.argmin G) = W.min_weight G := by
  exact (Classical.choose_spec (W.argmin_pre G)).2

lemma FunToMax.max_weight_max (W : FunToMax G) : ∀ v, W.w v ≤ W.max_weight G := by
  intro v
  by_cases q : v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0))
  · apply le_max' ; apply mem_image_of_mem ; apply q
  · simp only [gt_iff_lt, mem_filter, mem_univ, true_and, not_lt, nonpos_iff_eq_zero] at q
    rw [q]
    apply (W.max_weight G).prop

lemma FunToMax.min_weight_min (W : FunToMax G) : ∀ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.min_weight G ≤ W.w v := by
  intro v hv ; apply min'_le ; apply mem_image_of_mem ; apply hv

lemma FunToMax.argmin_le_argmax (W : FunToMax G) : W.w (W.argmin G) ≤  W.w (W.argmax G) := by
  rw [W.argmin_weight] ; apply W.min_weight_min ; apply W.argmax_mem

lemma FunToMax.min_weight_le_max_weight (W : FunToMax G) : W.min_weight G ≤  W.max_weight G := by
  rw [← W.argmin_weight, ← W.argmax_weight] ; apply W.argmin_le_argmax

lemma FunToMax.max_weight_ineq (W : FunToMax G) :
  (W.max_weight G) * ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card
  ≥ ∑ v∈((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v := by

  sorry

#check card_eq_sum_ones

lemma FunToMax.sum_eq_sum_supp (W : FunToMax G) :
  ∑ v∈(Finset.univ : Finset α), W.w v
  = ∑ v∈((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v := by
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

lemma FunToMax.sum_supp_eq_one (W : FunToMax G) :
  ∑ v∈((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v = 1 := by
  have eq : ∑ v in (Finset.univ : Finset α).filter (fun i => 0 < W.w i), W.w v =
             ∑ v in (Finset.univ : Finset α).filter (fun i => W.w i > 0), W.w v :=
    by simp [gt_iff_lt]
  convert W.h_w using 1
  sorry

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

lemma FunToMax.avg_le_max  (W : FunToMax G) :
  W.max_weight G ≥ 1 / (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) := by
  sorry

lemma FunToMax.min_le_avg  (W : FunToMax G) :
  W.min_weight G ≤ 1 / (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) := by
  let S := (Finset.univ : Finset α).filter (fun i => W.w i > 0)
  obtain ⟨x, hx⟩ := FunToMax.supp_nonempty G W
  let hS_nonempty : Nonempty { x : α // x ∈ S } := ⟨⟨x, hx⟩⟩
  have hS_pos : 0 < (S.card : NNReal) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x, hx⟩)
  have h_sum : ∑ v in ((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v = 1 := sorry
  sorry

lemma FunToMax.sum_supp_lt_max  (W : FunToMax G) (h : W.min_weight G < W.max_weight G) :
  ∑ v∈((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v
    < (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) * W.max_weight G := by
  nth_rewrite 1 [← Finset.insert_erase (W.argmin_mem G)]
  rw [sum_insert]
  swap
  · apply not_mem_erase
  ·
    have h_bound : ∀ x ∈ (filter (fun i => W.w i > 0) univ).erase (W.argmin G),
      W.w x ≤ W.max_weight G := λ x hx => W.max_weight_max G x
    have h_sum_bound : ∑ x in (filter (fun i => W.w i > 0) univ).erase (W.argmin G), W.w x
      ≤ ((filter (fun i => W.w i > 0) univ).erase (W.argmin G)).card * W.max_weight G := sorry
    sorry

#check Finset.card_erase_lt_of_mem
#check Nat.lt_iff_add_one_le


lemma FunToMax.min_lt_sum_supp  (W : FunToMax G) (h : W.min_weight G < W.max_weight G) :
  ∑ v∈((Finset.univ : Finset α).filter (fun i => W.w i > 0)), W.w v
    > (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) * W.max_weight G := by
  sorry

lemma FunToMax.avg_lt_max  (W : FunToMax G) (h : W.min_weight G < W.max_weight G) :
  W.max_weight G > 1 / (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) := by
  sorry

lemma FunToMax.min_lt_avg  (W : FunToMax G) (h : W.min_weight G < W.max_weight G):
  W.min_weight G ≤ 1 / (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) := by
  sorry

lemma FunToMax.min_eq_max  (W : FunToMax G) (h : W.min_weight G = W.max_weight G):
  ∀ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)),
    W.w v = 1 / (((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card) := by
  sorry


noncomputable
def the_ε (W : FunToMax G) :=
  (W.max_weight G) - (1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)

lemma the_ε_pos (W : FunToMax G) (h : W.min_weight G < W.max_weight G) : 0 < the_ε G W := by
  unfold the_ε
  let S := Finset.univ.filter (fun i => W.w i > 0)
  let as := Finset.card S
  sorry

lemma the_ε_lt (W : FunToMax G) (h : W.min_weight G < W.max_weight G) : the_ε G W < W.w (W.argmax G) - W.w (W.argmin G) := by
  sorry

lemma arg_help {W : FunToMax G} (h_con : W.w (W.argmin G) <  W.w (W.argmax G)) : W.min_weight G < W.max_weight G :=
  by rw [← W.argmin_weight, ← W.argmax_weight] ; exact h_con

noncomputable
def Enhanced (W : FunToMax G) (h_con : W.w (W.argmin G) <  W.w (W.argmax G)) :=
  (Enhance G W (W.argmax G) (W.argmin G) h_con (the_ε G W) (the_ε_pos G W (arg_help G h_con)) (the_ε_lt G W (arg_help G h_con)))

lemma Enhanced_unaffceted (W : FunToMax G) (h_con : W.w (W.argmin G) <  W.w (W.argmax G)) :
  ∀ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)),
    (Enhanced G W h_con).w v = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card := by
  sorry

lemma Enhanced_effect (W : FunToMax G) (h_con : W.w (W.argmin G) <  W.w (W.argmax G)) :
  (Enhanced G W h_con).w (W.argmax G) = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card := by
  sorry

lemma EnhanceIncreasesOneOverKVertices (W : FunToMax G) (h_con : W.w (W.argmin G) <  W.w (W.argmax G))  :
  let OneOverKSize (X : FunToMax G) := ((Finset.univ : Finset α).filter (fun i => X.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card ;
  OneOverKSize (Enhanced G W h_con) > OneOverKSize W := by

  sorry -- use ↓

#check ssubset_iff_of_subset
#check card_lt_card


lemma EvenBetter_has_constant_support (W : FunToMax G)
  (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  ∀ v ∈ ((Finset.univ : Finset α).filter (fun i => W.w i > 0)),
    (EvenBetter G W hW).w v = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card := by
  intro v hv
  have q := le_iff_eq_or_lt.mp ((EvenBetter G W hW).min_weight_le_max_weight G)
  cases' q with q h_con
  · have := (EvenBetter G W hW).min_eq_max G q v
    sorry -- use `EvenBetterSupportIncluded`
  · exfalso
    have reminder := EvenBetterSupportSize G W hW
    have problem := EnhanceIncreasesOneOverKVertices G (EvenBetter G W hW) sorry
    dsimp at problem
    sorry
    /-
    - apply `Nat.findGreatest_is_greatest`, with field `k` being `#(filter (fun i ↦ (Enhanced G (EvenBetter G W hW) ⋯).w i = 1 / ↑(#(filter (fun i ↦ (EvenBetter G W hW).w i > 0) univ))) univ)`
      and `hk` being `problem`, rewritten using `reminder`
    - it'll remain to show that the above `k` field argument satisfies the `help3` predicate
    - this will follow from `EnhanceSupport`, `EnhanceClique`  and `EnhanceIsBetter`
    -/

lemma EvenBetter_has_constant_support_consequence (W : FunToMax G)
  (hW : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  ∀ e ∈ G.supEdgeFinset W, vp W.w e =
    (1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)^2 := by
  sorry


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
  sorry

/-
We'll cast things to the reals to make computations managable
-/

lemma test (m : Nat) : (m / 2 : ℝ) =(m : ℝ ) / 2 := by exact rfl


lemma computation (k : Nat) :
  ((k : ℝ) * (k - 1) / 2)  * ((1/k)^2) = (1/2)*(1 - (1/k)) := by

  ring_nf!
  rw [pow_two, pow_two, ← mul_assoc] -- mul_inv_cancel
  sorry

#exit

-- Turan

theorem turan (h0 : p ≥ 2) (h1 : G.CliqueFree p)
  (w : α → NNReal) (h_w : ∑ v∈V, w v = 1) :
  #E ≤ (1 -  1 / (p - 1)) * n^2 / 2 := by
  sorry
