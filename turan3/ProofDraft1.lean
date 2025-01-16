import Mathlib

variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

-- Vertice Set (V), Edge Set (E), Graphs order (n)
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "n" => Fintype.card α

open Finset SimpleGraph

structure FunToMax where
  w : α → NNReal
  h_w : ∑ v in V, w v = 1
  fw := ∑ e in G.edgeFinset,
    Quot.liftOn e (λ pair : α × α => w pair.1 * w pair.2)
    (by intros x y h; cases h;
        · apply refl
        · apply mul_comm)

-- Turán's Theorem
theorem turan (h0 : p ≥ 2) (h1 : G.CliqueFree p)
  (w : α → NNReal) (h_w : ∑ v in V, w v = 1) :
  #E ≤ (1 -  1 / (p - 1)) * n^2 / 2 := by
  sorry



#check E
#check Sym2.lift
#check Quot.liftOn
#check G.edgeFinset
#check @mul_comm NNReal
#check (λ x y : NNReal => mul_comm x y)
