import Mathlib

variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

-- Vertice Set (V), Edge Set (E), Graphs order (n)
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "n" => Fintype.card α

open Finset SimpleGraph

-- Turán's Theorem
theorem turan (h0 : p ≥ 2) (h1 : G.CliqueFree p)
  (w : α → NNReal) (h_w : ∑ v in V, w v = 1) :
  #E ≤ (1 -  1 / (p - 1)) * n^2 / 2 := by

  -- First try (defining f(w)):
  -- let f : E -> NNReal := ∑ e in G.edgeFinset, Sym2.lift (λ u v => w u * w v) e

  -- Second try (defining f(w))
  -- Define f(w): the sum over "edges" of the product of weights
  -- Iterate through all edges of G. Quot.liftOn "extracts" pair of vertices for each edge in G
  let f : NNReal :=
  ∑ e in G.edgeFinset,
    Quot.liftOn e (λ pair : α × α => w pair.1 * w pair.2)
    (by intros x y h; cases h;
        · apply refl
        · apply mul_comm)



#check E
#check Sym2.lift
#check Quot.liftOn
#check G.edgeFinset
#check @mul_comm NNReal
#check (λ x y : NNReal => mul_comm x y)
