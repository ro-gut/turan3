



import Mathlib

variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

-- Vertice Set (V), Edge Set (E), Graphs order (n)
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "n" => Fintype.card α

open Finset SimpleGraph


def vp (w : α → NNReal) (e : Sym2 α) := 
  Quot.liftOn e (λ pair : α × α => w pair.1 * w pair.2)
    (by intros x y h; cases h;
        · apply refl
        · apply mul_comm)

structure FunToMax where
  w : α → NNReal
  h_w : ∑ v in V, w v = 1
  fw := ∑ e in G.edgeFinset, vp w e
    



-- help: Assures there exists an m s.t there is a weight function "better" with the following properties
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
-- Notes : I added h_neq as an assumption
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





lemma mini_help (e : Sym2 α) (he : e ∈ G.incidenceFinset gain) :
  gain ∈ e := by
  rw [mem_incidenceFinset] at he
  let e' : G.edgeSet := ⟨e, G.incidenceSet_subset _ he⟩
  have wow : ↑e' ∈ G.incidenceSet gain := he
  rw [edge_mem_incidenceSet_iff] at wow
  exact wow


lemma Improve_does_its_thing_part_help_0 (W : FunToMax G) (v : α) 
  (e : Sym2 α) (he : e ∈ G.incidenceFinset gain) :
  vp W.w e = (W.w gain) * (W.w (Sym2.Mem.other (mini_help G e he))) := by
  revert he
  apply @Sym2.inductionOn α (fun e => ∀ he : e ∈ G.incidenceFinset gain, vp W.w e = (W.w gain) * (W.w (Sym2.Mem.other (mini_help G e he))))
  intro x y he
  sorry


#check Sym2.inductionOn
#check Sym2.mem_iff_exists
#check Sym2.other_mem


lemma Improve_does_its_thing_part_help (W : FunToMax G) (v : α) :
    ∑ e in G.incidenceFinset gain, vp W.w e = 
    (W.w v) * ∑ e in (G.incidenceFinset gain).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop))) := by
    sorry

#check sum_bij
#check incidenceSetEquivNeighborSet
#check mem_incidenceFinset
#check mem_incidenceSet
#check mem_neighborFinset
#check mem_incidence_iff_neighbor



lemma Improve_does_its_thing_part_0 {loose gain : α}
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  Disjoint (G.incidenceFinset gain) (G.incidenceFinset loose) := by 
    simp_rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem, mem_inter]
    rintro x ⟨xg,xl⟩
    rw [incidenceFinset_eq_filter, mem_filter, mem_edgeFinset] at *
    apply h_adj
    rw [adj_iff_exists_edge]
    exact ⟨h_neq,⟨x,xg.1,xg.2,xl.2 ⟩⟩


lemma Improve_does_its_thing_part_1 (W : FunToMax G) (loose gain : α) 
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  let changed :=
    disjUnion
      (G.incidenceFinset gain)
      (G.incidenceFinset loose)
      (Improve_does_its_thing_part_0 G h_neq h_adj)
  G.edgeFinset = disjUnion changed (G.edgeFinset \ changed) (disjoint_sdiff) := by
    intro changed
    sorry
    -- the lack of API makes me sad
-- you may use
#check Finset.disjUnion_eq_union
#check Finset.sdiff_union_of_subset


lemma Improve_does_its_thing_part_2 (W : FunToMax G) (loose gain : α) 
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  let changed :=
    disjUnion
      (G.incidenceFinset gain)
      (G.incidenceFinset loose)
      (Improve_does_its_thing_part_0 G h_neq h_adj)
  ∑ e in G.edgeFinset, vp W.w e = 
    ∑ e in G.incidenceFinset gain, vp W.w e 
    + ∑ e in G.incidenceFinset loose, vp W.w e
    + ∑ e in (G.edgeFinset \ changed), vp W.w e := by
    sorry
-- use
#check sum_disjUnion


lemma Improve_does_its_thing_part_3 (W : FunToMax G) (loose gain : α) 
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
    ∑ e in G.incidenceFinset gain, vp (Improve G W loose gain h_neq).w e =
    ∑ e in G.incidenceFinset gain, vp W.w e 
    + ((Improve G W loose gain h_neq).w loose) * ∑ v in G.neighborFinset gain, W.w v := by
    sorry


lemma Improve_does_its_thing_part_4 (W : FunToMax G) (loose gain : α) 
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
    ∑ e in G.incidenceFinset loose, vp (Improve G W loose gain h_neq).w e = 0 := by
    sorry


lemma Improve_does_its_thing_part_5 (W : FunToMax G) (loose gain : α) 
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  ∑ e in G.incidenceFinset loose, vp W.w e =
  ((Improve G W loose gain h_neq).w loose) * ∑ v in G.neighborFinset loose, W.w v := by
  sorry

lemma Improve_does_its_thing_part_6 (W : FunToMax G) (loose gain : α) 
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) 
  (h : ∑ e in (G.incidenceFinset gain).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop)))
          ≥ ∑ e in (G.incidenceFinset loose).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop))))  :
    ∑ e in G.incidenceFinset gain, vp W.w e 
    + ((Improve G W loose gain h_neq).w loose) * ∑ e in (G.incidenceFinset gain).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop))) 
    ≥ ∑ e in G.incidenceFinset gain, vp W.w e + ∑ e in G.incidenceFinset loose, vp W.w e := by
  sorry
    

lemma Improve_does_its_thing_part_7 (W : FunToMax G) (loose gain : α) 
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  let changed :=
    disjUnion
      (G.incidenceFinset gain)
      (G.incidenceFinset loose)
      (Improve_does_its_thing_part_0 G h_neq h_adj)
  ∑ e in (G.edgeFinset \ changed), vp (Improve G W loose gain h_neq).w e
  = ∑ e in (G.edgeFinset \ changed), vp W.w e := by
  sorry


lemma Improve_does_its_thing (W : FunToMax G) (loose gain : α) 
  (h : ∑ e in G.incidenceFinset gain, vp W.w e ≥ ∑ e in G.incidenceFinset loose, vp W.w e) 
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose) :
  (Improve G W loose gain h_neq).fw ≥ W.fw := by
  sorry

 

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
        sorry
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
  wlog wlog : ∑ e in (G.incidenceFinset x).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop))) 
                ≥ ∑ e in (G.incidenceFinset y).attach, (W.w (Sym2.Mem.other (mini_help G e.val e.prop)))  with SymCase
  · push_neg at wlog
    specialize SymCase G W y ydef x xdef (ne_comm.mp xny) -- ...
    sorry
  · sorry







-- Turan

theorem turan (h0 : p ≥ 2) (h1 : G.CliqueFree p)
  (w : α → NNReal) (h_w : ∑ v in V, w v = 1) :
  #E ≤ (1 -  1 / (p - 1)) * n^2 / 2 := by
  sorry
