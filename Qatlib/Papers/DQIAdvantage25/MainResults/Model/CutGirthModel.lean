/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Paper model: DQI for MaxCut on high-girth graphs

Source: Ojas Parekh, *No Quantum Advantage in Decoded Quantum Interferometry for MaxCut*,
arXiv:2509.19966v2 (2025-09-30).

This file fixes the notation used by the paper (Section 2), specialised for MaxCut:

* `edgeVec`: the incidence vector `β ∈ {0,1}^E` of a finite set of edges (paper p.3–5);
* `ESet`: the set `ℰ_l = {β ∈ {0,1}^E | |β| ≤ l}` (paper p.5, Equation (1));
* `parityVector` / `parityMap`: the vertex-parity map `f(β) = Bᵀβ` over `𝔽₂`, where `B` is the
  edge–vertex incidence matrix (paper p.6, discussion before Lemma 2);
* `cutValue h(z) = (1/2) ∑_{ij ∈ E} (1 - z i * z j)` (paper p.3);
* `cycleRank μ = m - n + 1` (paper p.10, Theorem 3);
* `dijMatrix A^{(m,l)}` of Lemma 3 with off-diagonal entries `a_k = √(k(m-k+1))`, and its
  largest eigenvalue `maxEigenvalue`;
* `PolyBounded`, the paper's "runs in polynomial time" predicate (Theorems 1, Corollary 1).

The paper's convention is that the input is an infinite family of graphs with `g`, `n`, `m` the
girth, number of vertices and number of edges, and `lim_{m→∞} g/m` exists (paper p.3).
Statements about asymptotic quantities in the claim files are formulated for sequences in `m`.
-/

open scoped BigOperators
open Filter Matrix

namespace Qatlib.Papers.DQIAdvantage25.MainResults

namespace Model

variable {V : Type*}

/-! ## 1. Incidence vectors and the parity map `f` over `𝔽₂` -/

section Parity

variable [Fintype V] [DecidableEq V]

/-- The incidence vector `β ∈ {0,1}^E` of a finite set of edges, as an element of `𝔽₂^E`
(paper p.3–5: `x_γ = ∏ x_i^{γ_i}`; the cut analysis only needs the `𝔽₂` incidence vector). -/
def edgeVec (β : Finset (Sym2 V)) : Sym2 V → ZMod 2 :=
  fun e => if e ∈ β then 1 else 0

/-- The vertex-parity map `f(β) = Bᵀ β ∈ 𝔽₂^V`: the parity of the degree of each vertex in the
subgraph `β` (paper p.6: "`f(β)` as indicating the parity of the degree of vertex in `V` in the
subgraph `β`"). Here `B` is `G.incMatrix (ZMod 2)` (vertex × edge), so `Bᵀ β` is the
matrix–vector product `incMatrix *ᵥ edgeVec β`. -/
def parityVector (G : SimpleGraph V) [DecidableRel G.Adj] (β : Finset (Sym2 V)) : V → ZMod 2 :=
  G.incMatrix (ZMod 2) *ᵥ edgeVec β

/-- The domain `ℰ_l = {β ∈ {0,1}^E | |β| ≤ l}` of the parity map, restricted to subgraphs of `G`
(paper p.5, Equation (1)). -/
def ESet (G : SimpleGraph V) [DecidableRel G.Adj] (l : ℕ) : Set (Finset (Sym2 V)) :=
  {β | β ⊆ G.edgeFinset ∧ β.card ≤ l}

/-- The paper's map `f`, restricted to `ℰ_l`; the subject of Lemma 2 (paper p.6). -/
def parityMap (G : SimpleGraph V) [DecidableRel G.Adj] (l : ℕ) : ESet G l → (V → ZMod 2) :=
  fun β => parityVector G β.val

end Parity

/-! ## 2. Cut values and the cycle rank `μ = m - n + 1` -/

section Cut

variable [Fintype V] [DecidableEq V]

/-- The sign product `z_i z_j` attached to an unordered pair `{i,j}` (paper p.3). -/
noncomputable def edgeSignProd (z : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => z a * z b, by intro a b; ring⟩

/-- The cut value `h(z) = (1/2) ∑_{ij ∈ E} (1 - z_i z_j)` of a `±1` assignment `z` (paper p.3).
The paper sums over edges `ij ∈ E`; we sum over the finite edge set of `G`. -/
noncomputable def cutValue (G : SimpleGraph V) [DecidableRel G.Adj] (z : V → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, (1 - edgeSignProd z e) / 2

/-- `m`, the number of edges of `G` (paper p.3). -/
def numEdges (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := G.edgeFinset.card

/-- `n`, the number of vertices of `G` (paper p.3). -/
def numVerts (V : Type*) [Fintype V] : ℕ := Fintype.card V

/-- The cycle rank `μ = m - n + 1` of Theorem 3 (paper p.10). For a connected graph it is the
number of edges outside a spanning tree. -/
def cycleRank (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  (numEdges G : ℤ) - (numVerts V : ℤ) + 1

end Cut

/-! ## 3. The tridiagonal matrix `A^{(m,l)}` and its largest eigenvalue (Lemma 3, Lemma 4) -/

/-- The entry `a_k = √(k (m - k + 1))`, `1 ≤ k ≤ l`, of the tridiagonal matrix `A^{(m,l)}`
(paper p.8–9, Lemma 3). We use `Real.sqrt` of the (always nonnegative for `k ≤ m + 1`) radicand. -/
noncomputable def dijCoeff (m k : ℕ) : ℝ :=
  Real.sqrt ((k : ℝ) * ((m : ℝ) - k + 1))

/-- The `(l+1) × (l+1)` symmetric tridiagonal matrix `A^{(m,l)}` of Lemma 3 (paper p.9):

```
      ⎡      a₁                    ⎤
      ⎢ a₁      a₂                ⎥
 A =  ⎢    a₂     ⋱              ⎥ ,   a_k = √(k(m-k+1)).
      ⎢           ⋱     a_l      ⎥
      ⎣              a_l          ⎦
```

Off-diagonal `(i,j)` is `a_{min i j + 1}` when `|i - j| = 1`, and `0` otherwise. -/
noncomputable def dijMatrix (m l : ℕ) : Matrix (Fin (l + 1)) (Fin (l + 1)) ℝ :=
  fun i j =>
    if i.val + 1 = j.val ∨ j.val + 1 = i.val then dijCoeff m (min i.val j.val + 1) else 0

/-- The largest eigenvalue `λmax(A)`, defined as the supremum of the real spectrum of `A`.
For the symmetric matrix `A^{(m,l)}` of Lemma 3 this is the largest eigenvalue of the paper. -/
noncomputable def maxEigenvalue {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  sSup (spectrum ℝ A)

/-! ## 4. Asymptotic and complexity vocabulary

The paper indexes a family of graphs by `m` (the number of edges) and works with `g/m`, `l/m`
as `m → ∞` (paper p.3). The claim files state their conclusions in this sequence form. -/

/-- `g = Ω(m)`: girth grows at least linearly in the number of edges. -/
def GirthLinear (girth : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop, c * (m : ℝ) ≤ (girth m : ℝ)

/-- `g = o(m)`: the girth is sublinear in the number of edges. -/
def GirthSublinear (girth : ℕ → ℕ) : Prop :=
  Tendsto (fun m : ℕ => (girth m : ℝ) / (m : ℝ)) atTop (nhds 0)

/-- "Runs in polynomial time", in the paper's sense: the number of elementary steps is bounded by
a polynomial in the input size `N = n + m` (paper p.8, Theorem 1; p.10, Corollary 1). -/
def PolyBounded (steps : ℕ → ℕ) : Prop :=
  ∃ (k c : ℕ), ∀ N : ℕ, steps N ≤ c * (N + 1) ^ k

/-- The expected cut value `E_{z∼q²}[h(z)] = (m + λmax(A^{(m,l)}))/2` of DQI (paper p.8,
Lemma 3, Equation (3)). The index `m` is the number of edges and `l` the degree parameter. -/
noncomputable def dqiExpectedCut (m l : ℕ) : ℝ :=
  ((m : ℝ) + maxEigenvalue (dijMatrix m l)) / 2

end Model

end Qatlib.Papers.DQIAdvantage25.MainResults
