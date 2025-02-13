import Mathlib

variable {α : Type*} [Fintype α](G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

-- Vertice Set (V), Edge Set (E), Graphs order (n)
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "n" => Fintype.card α

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

#check sum_bij
#check incidenceSetEquivNeighborSet
#check mem_incidenceFinset
#check mem_incidenceSet
#check mem_neighborFinset
#check mem_incidence_iff_neighbor
#check mem_attach
  --

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

lemma Improve_does_its_thing_part_1 (W : FunToMax G) (loose gain : α)
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

-- use
#check sum_disjUnion


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

@[simp]
lemma Improve_w_eq (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  (Improve G W loose gain h_neq).w = (fun i => if i = loose then 0 else if i = gain then W.w gain + W.w loose else W.w i) :=
by rfl

lemma edgeFinset_subset_edgeSet (e : Sym2 α) (h : e ∈ G.edgeFinset) : e ∈ G.edgeSet :=
by rw [mem_edgeFinset] at h; exact h

lemma edge_mem_iff_explicit {α : Type*} [Fintype α] (G : SimpleGraph α) (v w : α) :
  G.Adj v w ↔ ∃ e ∈ G.edgeSet, e = Sym2.mk (v, w) :=
by
  constructor
  · intro h
    use Sym2.mk (v, w)
    simp [h]
  · rintro ⟨e, he, rfl⟩
    simp at he
    exact he

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
      apply @Sym2.inductionOn _ (fun X => ∀ (P : X ∈ G.incidenceFinset gain),
  vp (Improve G W loose gain h_neq).w X = vp W.w X + W.w loose * W.w (Sym2.Mem.other (mini_help G X P )))
      intro y z Pyz
      dsimp [vp,Quot.liftOn, Improve]
      have help := Sym2.mk_eq_mk_iff.mp (Sym2.other_spec (mini_help _ _ Pyz))
      cases help with
      | inl eqn =>
        injection eqn with hy hz
        subst hy
        rw[hz]
        simp[if_neg h_neq] at *
        ring_nf
        by_cases hzl : z = loose
        · subst hzl
          simp[if_pos rfl] at *
          ring_nf
          by_cases hz_nonzero : W.w z = 0
          · simp[hz_nonzero]
          ·
            have eq_factor : W.w z * (W.w gain + W.w z) = W.w gain * W.w z + W.w z ^ 2 :=
              by ring_nf
            rw [← eq_factor]
            by_cases hsum : W.w gain + W.w z = 0
            · rw [hsum, mul_zero]
            · have hprod : W.w z * (W.w gain + W.w z) ≠ 0 :=
                mul_ne_zero hz_nonzero hsum
              exfalso
              -- contradiction
              sorry
        ·
          simp [if_neg hzl] at *
          ring_nf
          sorry
      | inr eqn =>
        sorry

-- and use ↓ after disjoining on `help`
#check Prod.ext_iff

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

lemma nnreal_ne_def (a : NNReal) : a ≠ 0 ↔ ¬ a = 0 := by simp
#check nnreal_ne_def


lemma Improve_does_its_thing_part_6 (W : FunToMax G) (loose gain : α)
  (h_neq : gain ≠ loose) (h_adj : ¬ G.Adj gain loose)
  (h : ∑ e in (G.incidenceFinset gain).attach,
         W.w (Sym2.Mem.other (mini_help G e.val e.prop))
       ≥ ∑ e in (G.incidenceFinset loose).attach,
         W.w (Sym2.Mem.other (mini_help G e.val e.prop))) :
  ∑ e in G.incidenceFinset gain, vp W.w e
    + ((Improve G W loose gain h_neq).w loose)
      * ∑ e in (G.incidenceFinset gain).attach,
          W.w (Sym2.Mem.other (mini_help G e.val e.prop))
  ≥ ∑ e in G.incidenceFinset gain, vp W.w e
    + ∑ e in G.incidenceFinset loose, vp W.w e :=
by
  rw [Improve_does_its_thing_part_help_1 G W gain,
      Improve_does_its_thing_part_5 G W loose]
  rw [Improve_loose_weight_zero G W loose gain h_neq]
  simp only [zero_mul, add_zero]
  by_cases h_loose : W.w loose = 0
  · rw [h_loose, zero_mul, add_zero]
  · by_cases h_sum : ∑ e in (G.incidenceFinset loose).attach,
                       W.w (Sym2.Mem.other (mini_help G e.val e.prop)) = 0
    · rw [h_sum, mul_zero, add_zero]
    · exfalso
      have nonneg := (W.w loose).2
      cases eq_or_lt_of_le nonneg with
      | inl eq0 =>
        have : W.w loose = 0 :=
          Subtype.eq eq0.symm
        contradiction
      | inr great0 =>

        sorry

  -- rw [Improve_does_its_thing_part_help_1]
  -- rw [Improve_does_its_thing_part_5]
  -- rw [Improve_loose_weight_zero]
  -- simp only [zero_mul, add_zero]
  -- rw [add_sub_cancel_left]


#check Sym2.Rel α
#check G.incidenceFinset


--
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
  apply Finset.sum_congr rfl
  intro e he
  have h_e_not_gain_loose : e ∉ G.incidenceFinset gain ∧ e ∉ G.incidenceFinset loose := by
    constructor <;> simp_all [Finset.mem_sdiff, Finset.mem_disjUnion]
    <;> aesop
  rw [Finset.mem_sdiff] at he
  rcases he with ⟨h_edge, h_ne_changed⟩
  · dsimp [vp,Quot.liftOn, Improve]

    sorry

  -- simp [vp, Quot.liftOn]
  -- apply Finset.sum_congr rfl
  -- intro e he_diff
  -- have h_e_not_gain_loose : e ∉ G.incidenceFinset gain ∧ e ∉ G.incidenceFinset loose := by
  --   constructor <;> simp_all [Finset.mem_sdiff, Finset.mem_disjUnion]
  --   <;> aesop


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


#exit


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
