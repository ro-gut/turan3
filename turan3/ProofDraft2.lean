import Mathlib

variable {α : Type*} [Fintype α](G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

-- Vertice Set (V), Edge Set (E), Graphs order (n)
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "n" => Fintype.card α

set_option linter.unusedSectionVars false

open Finset SimpleGraph

-- "Value" of an edge = product of its vertices weight
def vp (w : α → NNReal) (e : Sym2 α) :=
  Quot.liftOn e (λ pair : α × α => w pair.1 * w pair.2)
    (by intros x y h; cases h;
        · apply refl
        · apply mul_comm)

-- f(w) in the informal proof
structure FunToMax (G : SimpleGraph α) [Fintype α] where
  w   : α → NNReal
  h_w : ∑ v in (Finset.univ : Finset α), w v = 1

namespace FunToMax

def fw {G : SimpleGraph α} [DecidableRel G.Adj] (W : FunToMax G) : NNReal :=
  ∑ e in G.edgeFinset, vp W.w e

end FunToMax

-- help: Assures that for any weight function W there exists an m and another weight function "better" with the following properties
theorem help (W : FunToMax G) : ∃ m : ℕ, (fun m =>
  ∃ better : FunToMax G,
    (∀ i, W.w i = 0 → better.w i = 0) ∧ -- support is included in that of W
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
    (∀ i, W.w i = 0 → better.w i = 0) ∧ -- support is included in that of W
    (((Finset.univ : Finset α).filter (fun i => better.w i > 0)).card = (K G W)) ∧ -- support has size m
    (W.fw ≤ better.fw) -- has better weights
    := Nat.find_spec (help G W)

-- Define optimal weight function with size m = K(G,W)
noncomputable
def Better (W : FunToMax G) : FunToMax G := Classical.choose (help2 G W)

-- Ensures Better's support is included in W's support
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
    -- Rewrite total sum of weights in terms of gain, loose and S
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


#check vp
#check Sym2.inductionOn
#check Sym2.mem_iff_exists
#check Sym2.mk_eq_mk_iff

-- sum of vp W.w e = W.w gain * sum
lemma Improve_does_its_thing_part_help_1 (W : FunToMax G) (gain : α) :
    ∑ e in G.incidenceFinset gain, vp W.w e =
    (W.w gain) * ∑ e in (G.incidenceFinset gain).attach, W.w (Sym2.Mem.other (mini_help G e.val e.prop)) := by
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
  ∑ e in G.edgeFinset, vp W.w e =
    ∑ e in G.incidenceFinset gain, vp W.w e +
    ∑ e in G.incidenceFinset loose, vp W.w e +
    ∑ e in (G.edgeFinset \ changed), vp W.w e := by
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
    ∑ e in G.edgeFinset, vp W.w e
      = ∑ e in changed ∪ (G.edgeFinset \ changed), vp W.w e
        := by rw [Finset.union_sdiff_of_subset h_changed_sub]
    _ = ∑ e in changed, vp W.w e + ∑ e in (G.edgeFinset \ changed), vp W.w e
        := Finset.sum_union h_disj_sdiff
    _ = ∑ e in (G.incidenceFinset gain ∪ G.incidenceFinset loose), vp W.w e
        + ∑ e in (G.edgeFinset \ changed), vp W.w e
        := by rw [h_disj_union]
    _ = (∑ e in G.incidenceFinset gain, vp W.w e
        + ∑ e in G.incidenceFinset loose, vp W.w e)
        + ∑ e in (G.edgeFinset \ changed), vp W.w e
        := by rw [Finset.sum_union (Improve_does_its_thing_part_0 G h_neq h_adj)]
    _ = ∑ e in G.incidenceFinset gain, vp W.w e
        + ∑ e in G.incidenceFinset loose, vp W.w e
        + ∑ e in (G.edgeFinset \ changed), vp W.w e
        := by rw [add_assoc]

@[simp]
lemma Improve_w_eq (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  (Improve G W loose gain h_neq).w = (fun i => if i = loose then 0 else if i = gain then W.w gain + W.w loose else W.w i) :=
by rfl

lemma Improve_does_its_thing_part_3 (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
    ∑ e in G.incidenceFinset gain, vp (Improve G W loose gain h_neq).w e =
    ∑ e in G.incidenceFinset gain, vp W.w e
    + (W.w loose)
      * ∑ e in (G.incidenceFinset gain).attach, W.w (Sym2.Mem.other (mini_help G e.val e.prop)) := by
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
    ∑ e in G.incidenceFinset loose, vp (Improve G W loose gain h_neq).w e = 0 := by
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
  ∑ e in G.incidenceFinset loose, vp W.w e =
  (W.w loose)
    * ∑ e in (G.incidenceFinset loose).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop))) := by
  apply Improve_does_its_thing_part_help_1

#check Sym2.Rel α


lemma Improve_does_its_thing_part_7 (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  let changed :=
    disjUnion
      (G.incidenceFinset gain)
      (G.incidenceFinset loose)
      (Improve_does_its_thing_part_0 G h_neq h_adj)
  ∑ e in (G.edgeFinset \ changed), vp (Improve G W loose gain h_neq).w e
  = ∑ e in (G.edgeFinset \ changed), vp W.w e :=
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
  by_cases h_y_loose : y = loose
  ·
    have h_y_in : y ∈ s(x,y) := by
      simp[h_y_loose]
    have h_edge : s(x,y) ∈ G.edgeFinset := by
      rw[Finset.mem_sdiff] at he_diff
      exact he_diff.1
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
        · 
          -- exact Finset.mem_coe.mp h_edge
          sorry
        · rfl
      · exact Or.inr rfl
    exfalso
    rw [Finset.mem_sdiff] at he_diff
    have h_not_in_changed : s(x,y) ∉ changed := he_diff.2
    have h_changed_eq : changed = G.incidenceFinset gain ∪ G.incidenceFinset loose := by
      apply Finset.ext
      intro e
      simp [Finset.mem_disjUnion, Finset.mem_union]
      sorry

    sorry

  · sorry
  sorry
#check edge_mem_iff

  -- proceed similarly to `Improve_does_its_thing_part_3`
  -- show that x and y can't be loose or gain, or else the other one would be in the inicidence set, hence in `changed`, contradicting `he_diff`

lemma Improve_does_its_thing (W : FunToMax G) (loose gain : α)
  (h : ∑ e in (G.incidenceFinset gain).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop))) ≥
    ∑ e in (G.incidenceFinset loose).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop))))
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
  (h_neq : gain ≠ loose) (h_supp : 0 < W.w gain) : -- will be `xdef` in `BetterFormsClique`
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
  (h_neq : gain ≠ loose) (h_supp1 : 0 < W.w gain) -- will be `xdef` in `BetterFormsClique`
  (h_supp2: 0 < W.w loose) : -- will be `ydef` in `BetterFormsClique`
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
  wlog wlog : ∑ e in (G.incidenceFinset x).attach, ((Better G W).w (Sym2.Mem.other (mini_help G e.val e.prop)))
                ≥ ∑ e in (G.incidenceFinset y).attach, ((Better G W).w (Sym2.Mem.other (mini_help G e.val e.prop)))  with SymCase
  · push_neg at wlog
    specialize SymCase G W y ydef x xdef (ne_comm.mp xny) (by rw [G.adj_comm] ; exact xyAdj)
    have H : ∑ e in (G.incidenceFinset y).attach, (Better G W).w (Sym2.Mem.other (mini_help G e.val e.prop))
      ≥ ∑ e in (G.incidenceFinset x).attach, (Better G W).w (Sym2.Mem.other (mini_help G e.val e.prop)) := le_of_lt wlog
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
-- to justify the existence of a max are a pain in the ass. For a given W who's support forms a k-clique,
-- we'll consider the largest number for which there is a FunToMax with same support who's
-- number of nodes at weight 1/k is that number.
-- Such numbers exist (possibly 0 if `(Better G W)` has no weights equal to 1/k)
-- We will then show that this number must be the size of the support:
-- if it weren't, we'll have to argue that the minimum weight w_min and the maximum
-- weight w_max satisfy w_min < 1/k < w_max (else, take sum and contradict W.h_w).
-- With them we'll use the improving argument from the book, with ε = w_max - 1/k
-- (it satisfies > 0 and < w_max-w_min), so that in the new wieghts, there will be
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
  have sum0 : ∑ i in (Finset.univ : Finset α), W.w i = 0 :=
    Finset.sum_eq_zero (fun i hi => all_zero i)
  rw [W.h_w] at sum0
  have hcontra : (1 : NNReal) ≠ 0 := by simp
  exact hcontra sum0

  -- else we'd contradict W.h_w

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
-- Largest number m, such that there is a FunToMax that has support in that of W,
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
        · 
          rw [hi.2]
          let j := (#(filter (fun i => W.w i > 0) univ))
          have j_nonzero : j ≠ 0 :=
            @supportSizeNotZero α (inferInstance : Fintype α) G (inferInstance : Fintype α)
            (inferInstance : DecidableEq α) (inferInstance : DecidableRel G.Adj) W
          have j_pos : j > 0 := Nat.pos_of_ne_zero j_nonzero
          rw [div_eq_mul_inv]
          rw [one_mul]         
          have hj : (j : NNReal) > 0 := Nat.cast_pos.mpr j_pos
          have hjnz : (j : NNReal) ≠ 0 := ne_of_gt (by exact_mod_cast hj)
          have hjR : (j : ℝ) > 0 := Nat.cast_pos.mpr j_pos        
          sorry
        )
      (by
        dsimp [help3]
        use W
        sorry
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
      · 
        intro hx
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
          ring_nf 
          sorry
      _ = (∑ x in {loose} ∪ {gain}, W.w x) + (univ \ ({loose} ∪ {gain})).sum W.w :=
        by sorry
      _ = ∑ x in ({loose} ∪ {gain}) ∪ (univ \ ({loose} ∪ {gain})), W.w x :=
        by sorry
      _ = ∑ x in univ, W.w x :=
        by sorry
      _ = 1 :=
        by { exact W.h_w }

lemma neq_of_W_lt {W : FunToMax G} {loose gain : α} (h_neq : W.w gain < W.w loose) : gain ≠ loose :=
  by
  intro con
  rw [con] at h_neq
  apply lt_irrefl _ h_neq

lemma EnhanceSupport (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ i, W.w i = 0 ↔ (Enhance G W loose gain h_lt ε epos elt).w i = 0 := by
    intro i
    dsimp[Enhance]
    split_ifs with h_loose h_gain
    · rw[h_loose]
      constructor
      · intro w0
        rw[w0]
        sorry
      · 
        sorry
    ·
      sorry
    · rfl  


lemma NNReal.eq_zero_of_ne_pos {x : NNReal} (h : ¬ x > 0) : x = 0 := by
  rw [← NNReal.coe_inj, eq_comm]
  simp_rw [← NNReal.coe_pos] at h
  have := x.prop
  apply eq_of_le_of_not_lt this h

lemma EnhanceSupport' (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∀ i, W.w i > 0 ↔ (Enhance G W loose gain h_lt ε epos elt).w i > 0 := by
    intro i
    rw [← not_iff_not]
    constructor
    · intro h
      intro con
      replace h := NNReal.eq_zero_of_ne_pos  h
      rw [EnhanceSupport] at h
      rw [h] at con
      exact lt_irrefl _ con
    · intro h
      intro con
      replace h := NNReal.eq_zero_of_ne_pos  h
      rw [← EnhanceSupport] at h
      rw [h] at con
      exact lt_irrefl _ con


lemma EnhanceCliquePractical (W : FunToMax G) (loose gain : α) (h_lt : W.w gain > W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) 
  (x y : α) (hx : W.w x > 0) (hy : W.w y > 0) :
    G.Adj x y := by
  dsimp [SimpleGraph.IsClique] at hc
  apply hc
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ x, hx⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ y, hy⟩
  · 
    intro eqxy
    subst eqxy

    sorry


lemma EnhanceClique (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain)
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  G.IsClique ((Finset.univ : Finset α).filter (fun i => (Enhance G W loose gain h_lt ε epos elt).w i > 0)) := by
    dsimp [IsClique]
    intros x hx y hy xny
    let hx₀ := Finset.mem_coe.mp hx
    rcases Finset.mem_filter.mp hx₀ with ⟨_, xPosNew⟩
    let hy₀ := Finset.mem_coe.mp hy
    rcases Finset.mem_filter.mp hy₀ with ⟨_, yPosNew⟩
    by_cases hx_loose : x = loose
    · 
      by_cases hy_gain : y = gain
      · 
        rw [hx_loose, hy_gain] at *
        dsimp [Enhance] at xPosNew yPosNew
        sorry
      ·   
        -- rw [hx_loose] at *
        simp[Enhance] at yPosNew
        sorry
    ·
      sorry 


#exit


import Matlib
/-
Don't work on these yet.
There is a mistake : all sets of edges should be filtered to those having vertices
in the support, as we'll later on need the fact that the support forms a clique.

-/

lemma EnhanceIsBetter_part_1 (loose gain : α) (h_neq : gain ≠ loose) :
  Disjoint ((G.incidenceFinset gain) \ {s(loose,gain)}) ((G.incidenceFinset gain) \ {s(loose,gain)}) := by
    sorry

def InciLooseGain (loose gain : α) (h_neq : gain ≠ loose) : Finset (Sym2 α) := 
  disjUnion 
    ((G.incidenceFinset gain) \ {s(loose,gain)}) ((G.incidenceFinset gain) \ {s(loose,gain)})
    (EnhanceIsBetter_part_1 G loose gain h_neq)

lemma EnhanceIsBetter_part_2 (loose gain : α) (h_neq : gain ≠ loose) :
  Disjoint (InciLooseGain G loose gain h_neq) {s(loose,gain)} := by
    sorry

def InciLooseGainFull (loose gain : α) (h_neq : gain ≠ loose) : Finset (Sym2 α) := 
  disjUnion 
    (InciLooseGain G loose gain h_neq) {s(loose,gain)}
    (EnhanceIsBetter_part_2 G loose gain h_neq)


--#exit

lemma EnhanceIsBetter_part_3 (loose gain : α) (h_neq : gain ≠ loose) :
  G.edgeFinset = 
    disjUnion (InciLooseGainFull G loose gain h_neq) (G.edgeFinset \ (InciLooseGainFull G loose gain h_neq)) 
      (disjoint_sdiff) := by 
    sorry

lemma EnhanceIsBetter_part_4 (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  ∑ e in G.edgeFinset, vp W.w e =
    ((∑ e in ((G.incidenceFinset gain) \ {s(loose,gain)}) , vp W.w e +
      ∑ e in ((G.incidenceFinset loose) \ {s(loose,gain)}) , vp W.w e) +
     ∑ e in {s(loose,gain)}, vp W.w e)+
    ∑ e in (G.edgeFinset \ (InciLooseGainFull G loose gain h_neq)), vp W.w e := by
  sorry

lemma tiny_help {s t : Finset α} {a : α} (h : a ∈ s \ t) : a ∈ s := by
  rw [Finset.mem_sdiff] at h; exact h.1


lemma EnhanceIsBetter_part_5 (W : FunToMax G) (gain : α) (dummy : Sym2 α)
  (e : Sym2 α) (he : e ∈ ((G.incidenceFinset gain) \ {dummy})) :
  vp W.w e = (W.w gain) * (W.w (Sym2.Mem.other (mini_help G e (tiny_help he)))) := by
  rw [Finset.mem_sdiff] at he
  convert (Improve_does_its_thing_part_help_0 G W gain e he.1)


-- sum of vp W.w e = W.w gain * sum
lemma EnhanceIsBetter_part_6 (W : FunToMax G) (gain : α) (dummy : Sym2 α) :
    ∑ e in ((G.incidenceFinset gain) \ {dummy}), vp W.w e =
    (W.w gain) * ∑ e in ((G.incidenceFinset gain) \ {dummy}).attach, W.w (Sym2.Mem.other (mini_help G e.val (tiny_help e.prop))) := by
  rw [mul_sum]
  rw [← sum_attach]
  apply sum_congr
  · rfl
  · intro x _
    apply EnhanceIsBetter_part_5 _ _ gain dummy _ x.prop


lemma EnhanceIsBetter_part_7_help (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) :
  ∀ e ∈ ((G.incidenceFinset gain) \ {s(loose,gain)}).attach, 
    (Enhance G W loose gain h_lt ε epos elt).w (Sym2.Mem.other (mini_help G e.val (tiny_help e.prop))) =
    W.w (Sym2.Mem.other (mini_help G e.val (tiny_help  e.prop))) := by
  sorry


lemma EnhanceIsBetter_part_7 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) :
  ∑ e in ((G.incidenceFinset gain) \ {s(loose,gain)}), vp (Enhance G W loose gain h_lt ε epos elt).w e =
  ∑ e in ((G.incidenceFinset gain) \ {s(loose,gain)}), vp W.w e +
  ε * ∑ e in ((G.incidenceFinset gain) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (mini_help G e.val (tiny_help e.prop))) := by
  sorry

lemma EnhanceIsBetter_part_8_help (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) :
  ∀ e ∈ ((G.incidenceFinset loose) \ {s(loose,gain)}).attach, 
    (Enhance G W loose gain h_lt ε epos elt).w (Sym2.Mem.other (mini_help G e.val (tiny_help e.prop))) =
    W.w (Sym2.Mem.other (mini_help G e.val (tiny_help  e.prop))) := by
  sorry


lemma EnhanceIsBetter_part_8 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) :
  ∑ e in ((G.incidenceFinset loose) \ {s(loose,gain)}), vp (Enhance G W loose gain h_lt ε epos elt).w e =
  ∑ e in ((G.incidenceFinset loose) \ {s(loose,gain)}), vp W.w e -
  ε * ∑ e in ((G.incidenceFinset loose) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (mini_help G e.val (tiny_help e.prop))) := by
  sorry

#check sum_attach

noncomputable
def the_bij (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) :
  (e : { x // x ∈ G.incidenceFinset loose \ {s(loose, gain)} }) → (e ∈ ((G.incidenceFinset loose) \ {s(loose,gain)}).attach) → { x // x ∈ G.incidenceFinset gain \ {s(loose, gain)} } :=
  fun e h => 
    ⟨(s(gain,(Sym2.Mem.other (mini_help G e.val (tiny_help e.prop))))),
     (by
      sorry
      )⟩ 

lemma EnhanceIsBetter_part_9 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) :
  ∑ e in ((G.incidenceFinset loose) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (mini_help G e.val (tiny_help e.prop))) =
  ∑ e in ((G.incidenceFinset gain) \ {s(loose,gain)}).attach, W.w (Sym2.Mem.other (mini_help G e.val (tiny_help e.prop))) :=
  by
  sorry
  
#check sum_bij


#exit

lemma EnhanceIsBetter_part_9 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) :
  ∀ e ∈ (G.edgeFinset \ (InciLooseGainFull G loose gain (neq_of_W_lt G h_lt))),
    vp (Enhance G W loose gain h_lt ε epos elt).w e = vp W.w e := by
  sorry

lemma EnhanceIsBetter_part_10 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) :
  ∑ e in (G.edgeFinset \ (InciLooseGainFull G loose gain (neq_of_W_lt G h_lt))), vp (Enhance G W loose gain h_lt ε epos elt).w e =
  ∑ e in (G.edgeFinset \ (InciLooseGainFull G loose gain (neq_of_W_lt G h_lt))), vp W.w e := by
  sorry


lemma EnhanceIsBetter_part_11 (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) :
  vp (Enhance G W loose gain h_lt ε epos elt).w s(loose,gain) =
  vp W.w s(loose,gain) + ε*(W.w loose - W.w gain) - ε^2 := by
  sorry

lemma EnhanceIsBetter (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) 
  (hc : G.IsClique ((Finset.univ : Finset α).filter (fun i => W.w i > 0))) :
  W.fw ≤ (Enhance G W loose gain h_lt ε epos elt).fw := by
    sorry


#exit

-- actually, this is only true for specific choices of loose and gain
-- Before we tackle this, we'll have to develop some stuff around minimum and maximum weights
lemma EnhanceDecreasesOneOverKVertices (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose) 
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w gain - W.w loose) :
  let OneOverKSize (X : FunToMax G) := ((Finset.univ : Finset α).filter (fun i => X.w i = 1 / ((Finset.univ : Finset α).filter (fun i => W.w i > 0)).card)).card ;
  OneOverKSize (Enhance G W loose gain h_lt ε epos elt) < OneOverKSize W := by
    sorry



-- eventually
#check Nat.le_findGreatest
#check Nat.findGreatest_le




#exit

-- Turan

theorem turan (h0 : p ≥ 2) (h1 : G.CliqueFree p)
  (w : α → NNReal) (h_w : ∑ v in V, w v = 1) :
  #E ≤ (1 -  1 / (p - 1)) * n^2 / 2 := by
  sorry
