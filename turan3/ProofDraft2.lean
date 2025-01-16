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

---------------

w



open Classical

noncomputable
def K (W : FunToMax G) := Nat.find (help G W)

lemma help2 (W : FunToMax G):
  ∃ better : FunToMax G,
    (∀ i, W.w i = 0 → better.w i = 0) ∧ -- support is included in that of W
    (((Finset.univ : Finset α).filter (fun i => better.w i = 0)).card = (K G W)) ∧ -- support has size m
    (W.fw ≤ better.fw) -- has better weights
    := Nat.find_spec (help G W)

#check Nat.find_le
