import Mathlib

variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

-- Vertice Set (V), Edge Set (E), Graphs order (n)
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "n" => Fintype.card α

structure FunToMax where
  w : α → NNReal
  h_w : ∑ v in V, w v = 1
  fw := ∑ e in G.edgeFinset,
    Quot.liftOn e (λ pair : α × α => w pair.1 * w pair.2)
    (by intros x y h; cases h;
        · apply refl
        · apply mul_comm)

noncomputable
def SupposedMax {k : ℕ} (hk : k ≠ 0) {clique : Finset α} (hc : clique.card = k) : FunToMax G where
  w := fun x => if x ∈ clique then 1/k else 0
  h_w := by
    rw [Finset.sum_ite,Finset.sum_const_zero, add_zero, Finset.sum_const,Finset.filter_univ_mem,hc]
    rw [one_div, nsmul_eq_mul, mul_inv_cancel₀]
    simp only [ne_eq, Nat.cast_eq_zero] -- from simp?
    apply hk


noncomputable
def definitionalMax := sSup (Set.image FunToMax.fw (Set.univ : Set (FunToMax G)))

---------------------

theorem help (W : FunToMax G) : ∃ m : ℕ, (fun m =>
  ∃ better : FunToMax G,
    (∀ i, W.w i = 0 → better.w i = 0) ∧ -- support is included in that of W
    (((Finset.univ : Finset α).filter (fun i => better.w i > 0)).card = m) ∧ -- support has size m
    (W.fw ≤ better.fw) -- has better weights
    ) m := by
    let m := ((Finset.univ : Finset α).filter (fun i => W.w i = 0)).card
    use m
    let better := W
    use better
    have hP : ∀ (i : α), W.w i = 0 → better.w i = 0 := by
      intro i h_w_zero
      have better_eq : better.w = W.w := rfl
      rw [better_eq]
      exact h_w_zero
    have hQ : (Finset.filter (fun i => better.w i = 0) Finset.univ).card = m := by
      exact rfl
    have hR : W.fw ≤ better.fw := by
      have better_fw_eq : better.fw = W.fw := rfl
      rw [better_fw_eq]
    exact ⟨hP, ⟨hQ, hR⟩⟩

open Classical

noncomputable
def K (W : FunToMax G) := Nat.find (help G W)

lemma help2 (W : FunToMax G):
  ∃ better : FunToMax G,
    (∀ i, W.w i = 0 → better.w i = 0) ∧ -- support is included in that of W
    (((Finset.univ : Finset α).filter (fun i => better.w i = 0)).card = (K G W)) ∧ -- support has size m
    (W.fw ≤ better.fw) -- has better weights
    := Nat.find_spec (help G W)

--------- WIP -----------

lemma Improve_does_its_thing (W : FunToMax G) (loose gain : α) (h : W.w gain ≥ W.w loose) (h_neq : gain ≠ loose):
  (Improve G W loose gain h_neq).fw ≥ W.fw := by
    simp only [Improve, FunToMax.w]
  have left_hand : (Improve G W loose gain h_neq).fw =
    ∑ e in G.edgeFinset,
      Quot.liftOn e
        (λ pair : α × α =>
          (if pair.1 = loose then 0 else if pair.1 = gain then W.w gain + W.w loose else W.w pair.1) *
          (if pair.2 = loose then 0 else if pair.2 = gain then W.w gain + W.w loose else W.w pair.2))
        (by
          intros x y hxy;
          cases hxy with
          | refl x y => rfl
          | swap x y => simp only [mul_comm, if_pos, if_neg]) := by
              simp only [Improve, FunToMax.fw]

  have right_hand : W.fw = ∑ e in G.edgeFinset,
    Quot.liftOn e
      (λ pair : α × α => W.w pair.1 * W.w pair.2)
      (by
        intros x y hxy
        cases hxy with
        | refl x y => rfl
        | swap x y => simp only [mul_comm, if_pos, if_neg]) := by

    let fw_manual := ∑ e in G.edgeFinset,
      Quot.liftOn e
        (λ pair : α × α => W.w pair.1 * W.w pair.2)
        (by
          intros a b hab
          cases hab with
          | refl => rfl
          | swap => simp only [mul_comm])

    change W.fw = fw_manual
    rfl
    sorry


    -- Idea: split by cases 1. e_1 or e_2 = loose
      --              2. e_1 or e_2 = gain
      --              2. e_1 and e_2 =! gain or loose (remains unchanged by def)
    let edges_with_loose := G.edgeFinset.filter (λ e => loose ∈ e)
    let edges_with_gain := G.edgeFinset.filter (λ e => gain ∈ e ∧ ¬(loose ∈ e))
    let edges_other := G.edgeFinset.filter (λ e => ¬(loose ∈ e) ∧ ¬(gain ∈ e))
    let w' := (Improve G W loose gain h_neq).w

lemma ImproveReducesSupport (W : FunToMax G) (loose gain : α) (h_neq : gain ≠ loose) :
  ∀ i, W.w i = 0 → (Improve G W loose gain h_neq).w i = 0 := by
  intro i h_zero
  simp only [Improve, FunToMax.w]
  by_cases hi_loose : i = loose
  · rw [hi_loose]
    simp
  · by_cases hi_gain : i = gain
    · rw [hi_gain]
      simp
      intro h_not_eq
      constructor
      · rw [hi_gain] at h_zero
        exact h_zero
      ·
        have h_sum_split : ∑ v in Finset.univ, W.w v = W.w loose + ∑ v in Finset.univ.erase loose, W.w v := by
        W.w loose + W.w gain + ∑ v in (Finset.univ.erase loose).erase gain, W.w v := by
          have h_not_mem : loose ∉ Finset.univ.erase loose := Finset.not_mem_erase loose Finset.univ
          rw [←Finset.insert_erase (Finset.mem_univ loose)]
          rw [Finset.sum_insert h_not_mem]
          rw [Finset.insert_erase (Finset.mem_univ loose)]

        have h_sum := W.h_w
        rw [h_sum_split] at h_sum

        have h_other_sum : ∑ v in Finset.univ.erase loose, W.w v = 1 - W.w loose := by
          apply_fun (λ x => x - W.w loose) at h_sum
          simp at h_sum
          exact h_sum
        rw[h_other_sum] at h_sum

        sorry
    · simp [hi_loose, hi_gain, h_zero]


open Finset SimpleGraph

theorem turan (h0 : p ≥ 2) (h1 : G.CliqueFree p)
  (w : α → NNReal) (h_w : ∑ v in V, w v = 1) :
  #E ≤ (1 -  1 / (p - 1)) * n^2 / 2 := by
  sorry
