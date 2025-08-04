# turan3
Formalisation of (the 3rd) Turan's Theorem Proof from The Book (6th Edition)

## Theorem: 
   Let G = (V, E) be a simple graph on n vertices with no p-clique (p ≥ 2). 
   
   Then: |E| ≤ (1 – (1 / (p–1))) · n²/2

## Sketch of the proof

**Setup:** 
- Let w : V → ℝ≥0 be an arbitrary weight distribution on the vertice Set with : ∑_{i∈V} w(i) = 1
- Define f(w) = ∑_{i,j}∈E₎ w(i)·w(j)
  Our goal is to maximize f(w)

**1. Concentrating positive weights on a clique**

- Let w be an arbitrary weight function.
- Define S_I = { w' : V → ℝ≥0 |supp(w') ⊆ supp(w) and f(w) ≤ f(w') }
                                        (where  supp(w)= { i | w(i) ≠ 0 })
- Let m = min { |supp(W)| : w' ∈ S_I }

- Choose any W_m ∈ S_I with |supp(W_m)| = m

Now we show supp(W_m) foms a clique.

- If i,j ∈ supp(W_m) are nonadjacent vertices, define: s_x = ∑_{v_k ∈ N(v_x)} W_m(v_x)
  as the sum of all weights from vertices adjacent to v_x
  
Assume wlog s_i ≥ s_j

Define a new weight function w_m' with:
1. w_m' (i) = w_m(i) + w_m(j)
2. w_m' (j) = 0
3. w_m' (l) = w_m (l)   For all other vertices

Then we get f(w_m') = f(w_m) + w_m(j)·(s_i − s_j) ≥ f(w_m).

This reduces the support size by one, so w_m' ∈ S_I, but |supp(W_m')| = m - 1, contradiction the minimality of the support size
Therefore we conclude |supp(W_m)| must be a clique


**2. "Equalizing" weights in the clique**

Let k = |supp(w_m)|
Define  S_E = { w : V → ℝ≥0 | supp(W) = supp(w_m) ∧
                                    f(w_m) ≤ f(w) ∧ 
                                    supp(w) forms a clique of size k }

Let 
- Na(w) = #{ i ∈ supp(W) | w(i) = 1/k }  - number of vertices with weight 1/k 
- M = max { Na(w) | w ∈ S_E }

We consider the largest M such that there is an w_M ∈ S_E that satisfies this. We aim to show that M = k

For contradiction assume M < k.

From that follows that there exists at least a vertice v_i with v_i ≠ 1/k. Also we have: min(w_M) < max(w_M)

Let v₊ be the vertex with the maximal weight (max(w_M))  and
    v₋ be the vertex with the minimal weight (min(w_M))
    
Set ε = max(w_M) − 1/k

We define a new weight function w_M' with:
1. w_M' (v₊) = w_M(v₊) - ε
2. w_M' (v₋) = w_M(v₋) + ε
3. w_M' (l) = w_M (l)   For all other vertices

Here w_M' ∈ S_E is a better distribution, with the same support (in the clique) and f(w_M') ≥ f(w_M).
Also the the number of vertex with weight 1/k increases by one (at vertex v₊). This contradicts the maximality of M.

**3. Conclusion**

Since M = k , all vertices in the support have weight 1/k.

Hence f(w_M) = ∑_{{i,j} ⊆ supp(w_M)} (1/k)·(1/k)
             = ( k (k-1)/ 2 ) (1 / k²)
             = 1/2 · (1 − 1/k)

Since G has no p-clique, best we can do is k ≤ p − 1

We apply this to the uniform distribution on all n vertices and get:
 
|E| ≤ (1 – (1 / (p–1))) · n²/2



                

