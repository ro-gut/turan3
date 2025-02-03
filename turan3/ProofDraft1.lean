import Mathlib

variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

-- Vertice Set (V), Edge Set (E), Graphs order (n)
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "n" => Fintype.card α

open Finset SimpleGraph

-- structure FunToMax where
--   w : α → NNReal
--   h_w : ∑ v in V, w v = 1
--   fw := ∑ e in G.edgeFinset,
--     Quot.liftOn e (λ pair : α × α => w pair.1 * w pair.2)
--     (by intros x y h; cases h;
--         · apply refl
--         · apply mul_comm)

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


lemma Improve_does_its_thing (W : FunToMax G) (loose gain : α) (h : W.w gain ≥ W.w loose) (h_neq : gain ≠ loose):
  (Improve G W loose gain h_neq).fw ≥ W.fw := by
  -- unfold fw and Improve
  simp only [FunToMax.fw, Improve]
  let W' := Improve G W loose gain h_neq
  -- Prove Quot.liftOn is well_defined
  have well_defined : ∀ (a b : α × α),
    Sym2.Rel α a b →
      (fun pair =>
        (if pair.1 = loose then 0 else if pair.1 = gain then W.w gain + W.w loose else W.w pair.1) *
        (if pair.2 = loose then 0 else if pair.2 = gain then W.w gain + W.w loose else W.w pair.2)) a =
      (fun pair =>
        (if pair.1 = loose then 0 else if pair.1 = gain then W.w gain + W.w loose else W.w pair.1) *
        (if pair.2 = loose then 0 else if pair.2 = gain then W.w gain + W.w loose else W.w pair.2)) b := by
    intros a b h_rel
    cases h_rel
    · case refl => rfl
    · case swap => simp [mul_comm]
  -- Partitio G.edgeFinset into 3 parts by cases
  let edges_with_loose := G.edgeFinset.filter (λ e => loose ∈ e)
  let edges_with_gain := G.edgeFinset.filter (λ e => gain ∈ e ∧ ¬(loose ∈ e))
  let edges_other := G.edgeFinset.filter (λ e => ¬(loose ∈ e) ∧ ¬(gain ∈ e))
  let w' := (Improve G W loose gain h_neq).w
  have h_partition : G.edgeFinset =
    edges_with_loose ∪ edges_with_gain ∪ edges_other := by
    apply Finset.ext
    intro e
    simp only [edges_with_loose, edges_with_gain, edges_other, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h_mem
      by_cases h_loose : loose ∈ e
      · left
        exact Or.inl ⟨h_mem, h_loose⟩
      by_cases h_gain : gain ∈ e
      · left; right
        exact ⟨h_mem, h_gain, h_loose⟩
      · right
        exact ⟨h_mem, h_loose, h_gain⟩
    · rintro ((⟨eg,_⟩ | ⟨eg,_⟩) | ⟨eg,_⟩)
      all_goals {apply eg}

  -- disjoint lemmas

  have disj₁ : Disjoint edges_with_loose edges_with_gain := by
    rw [Finset.disjoint_left]
    intros x hx hx'
    rw [Finset.mem_filter] at hx hx'
    exact hx'.2.2 hx.2



  have disj₂ : Disjoint (edges_with_loose ∪ edges_with_gain) edges_other := by
    rw [Finset.disjoint_left]
    intros x hx hx'
    rw [Finset.mem_union] at hx
    cases hx
    case inl hx_loose =>
      rw [Finset.mem_filter] at hx_loose hx'
      exact hx'.2.1 hx_loose.2
    case inr hx_gain =>
      rw [Finset.mem_filter] at hx_gain hx'
      exact hx'.2.2 hx_gain.2.1

-- summand function f to define bigSum
  let f : Sym2 α → NNReal :=
    fun e =>
      Quot.liftOn e
        (fun pair =>
          (if pair.1 = loose then 0
          else if pair.1 = gain then W.w gain + W.w loose
          else W.w pair.1) *
          (if pair.2 = loose then 0
          else if pair.2 = gain then W.w gain + W.w loose
          else W.w pair.2)
        )
        well_defined

  set bigSum :=
    ∑ x in edges_with_loose, f x +
    ∑ x in edges_with_gain,  f x +
    ∑ x in edges_other,      f x

  -- merge sums by steps

  have step1 :
    ∑ x in edges_with_loose, f x +
    ∑ x in edges_with_gain, f x =
    ∑ x in (edges_with_loose ∪ edges_with_gain), f x :=
    (Finset.sum_union disj₁ (f := f)).symm

  have step2 :
    ∑ x in (edges_with_loose ∪ edges_with_gain), f x +
    ∑ x in edges_other, f x =
    ∑ x in (edges_with_loose ∪ edges_with_gain ∪ edges_other), f x :=
    (Finset.sum_union disj₂ (f := f)).symm

  have eq_bigSum : bigSum = W'.fw := by
    calc
      bigSum
        = ∑ x in edges_with_loose, f x + ∑ x in edges_with_gain, f x + ∑ x in edges_other, f x
          := rfl
      _ = ∑ x in (edges_with_loose ∪ edges_with_gain), f x + ∑ x in edges_other, f x
          := by rw [step1]
      _ = ∑ x in (edges_with_loose ∪ edges_with_gain ∪ edges_other), f x
          := by rw [step2]
      _ = ∑ x in G.edgeFinset, f x
          := by rw [h_partition]
      _ = W'.fw
          := rfl

----------------------- Show its not neg
  sorry

-----------------------



lemma ImproveReducesSupport (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  ∀ i, W.w i = 0 → (Improve G W loose gain h_neq).w i = 0 := by
  intro i h_zero
  simp only [Improve, FunToMax.w]
  by_cases hi_loose : i = loose
  · rw [hi_loose]
    simp
  · by_cases hi_gain : i = gain
    · rw [hi_gain] at h_zero
      simp [h_zero]
      have h_sum := W.h_w
      have h_sum_split : ∑ v in Finset.univ, W.w v = W.w loose + ∑ v in Finset.univ.erase loose, W.w v := by
        have h_not_mem : loose ∉ Finset.univ.erase loose := Finset.not_mem_erase loose Finset.univ
        rw [←Finset.insert_erase (Finset.mem_univ loose)]
        rw [Finset.sum_insert h_not_mem]
        rw [Finset.insert_erase (Finset.mem_univ loose)]
      have h_other_sum : ∑ v in Finset.univ.erase loose, W.w v = 1 - W.w loose := by
        rw [h_sum_split] at h_sum
        apply_fun (λ x => x - W.w loose) at h_sum
        simp at h_sum
        exact h_sum
      have h_nonneg : W.w loose ≥ 0 := NNReal.coe_nonneg (W.w loose)
      have h_contradiction : W.w loose = 0 := by
        sorry
      sorry
    · simp [hi_loose, hi_gain, h_zero]


lemma BetterFormsClique (W : FunToMax G) : G.IsClique ((Finset.univ : Finset α).filter (fun i => (Better G W).w i > 0)) := by
  by_contra con
  dsimp [IsClique, Set.Pairwise] at con
  push_neg at con
  obtain ⟨x,xdef,y,ydef,xny,xyAdj⟩ := con
  wlog wlog : (Better G W).w x ≤ (Better G W).w y with SymCase
  · push_neg at wlog
    specialize SymCase G W y ydef x xdef (ne_comm.mp xny) -- ...
    sorry
  · sorry



-- Turan

theorem turan (h0 : p ≥ 2) (h1 : G.CliqueFree p)
  (w : α → NNReal) (h_w : ∑ v in V, w v = 1) :
  #E ≤ (1 -  1 / (p - 1)) * n^2 / 2 := by
  sorry


---------------------------------------------------

def vp (w : α → NNReal) (e : Sym2 α) :=
  Quot.liftOn e (λ pair : α × α => w pair.1 * w pair.2)
    (by intros x y h; cases h;
        · apply refl
        · apply mul_comm)

structure FunToMax where
  w : α → NNReal
  h_w : ∑ v in V, w v = 1
  fw := ∑ e in G.edgeFinset, vp w e

lemma mini_help (e : Sym2 α) (he : e ∈ G.incidenceFinset gain) :
  gain ∈ e := by
  rw [mem_incidenceFinset] at he
  let e' : G.edgeSet := ⟨e, G.incidenceSet_subset _ he⟩
  have wow : ↑e' ∈ G.incidenceSet gain := he
  rw [edge_mem_incidenceSet_iff] at wow
  exact wow

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
  let changed :=
  disjUnion
    (G.incidenceFinset gain)
    (G.incidenceFinset loose)
    (Improve_does_its_thing_part_0 G h_neq h_adj)
  have h_disj_union : changed = G.incidenceFinset gain ∪ G.incidenceFinset loose := by
    apply Finset.disjUnion_eq_union
  have h_disj_sdiff : Disjoint changed (G.edgeFinset \ changed) := Finset.disjoint_sdiff
-- Define decidable instance for Sym2.Mem gain e
  calc
    ∑ e in G.edgeFinset, vp W.w e = ∑ e in changed ∪ (G.edgeFinset \ changed), vp W.w e := by
      rw [Finset.union_sdiff_self_eq_union]
      -- ⊢ edgeFinset G = changed ∪ (edgeFinset G \ changed)
      rw [Finset.union_comm]
