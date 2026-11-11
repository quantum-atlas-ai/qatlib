/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Source model of arXiv:2405.12714 (CarlemanLin24)

Fixed source: *Quantum Algorithms for Nonlinear Dynamics: Revisiting Carleman
Linearization with No Dissipative Conditions*, arXiv:2405.12714v2, QATLAS paper
`520`.  The page / equation references below are to that version.

The paper studies the quadratic ODE (Eq. (4), p. 2)

```
dx/dt = F₁ x + F₂ x^{⊗2},
```

with `F₁ ∈ ℝ^{n×n}` and `F₂ : ℝ^{n×n} → ℝ^n`, and its `N`-th Carleman
truncation (Eq. (5)–(8), p. 2–3)

```
d/dt (x, x^{⊗2}, …, x^{⊗N}) = A (x, x^{⊗2}, …, x^{⊗N}) + (0, …, 0, A_{N,N+1} x^{⊗(N+1)}),
```

where (Eq. (7))

```
A_{j,j}   = Σ_{i=1}^{j}   I^{⊗(i−1)} ⊗ F₁ ⊗ I^{⊗(j−i)},
A_{j,j+1} = Σ_{i=1}^{j}   I^{⊗(i−1)} ⊗ F₂ ⊗ I^{⊗(j−i)}.
```

This module fixes the vocabulary used by every claim module of the block:

* the tensor powers `x^{⊗j}` and the block vector `(y₁,…,y_N)`;
* the concrete Carleman matrix from Eqs. (6)–(7), built on the dependent block
  index `Σ j : Fin N, (Fin (j+1) → Fin n)` (`carlemanMat`);
* the induced matrix 1-norm (`matOneNorm`) and the vector ℓ¹ norm (`vecL1`),
  which are the norms used in Eqs. (13), (42)–(44), (50), (58);
* the spectrum set of A from Lemma 2.1, the resonance parameter `Δ` of
  Eq. (11), the condition number `κ₁(W)`, the constants `C` and `Rᵣ` of
  Eq. (14), the `G` matrices of Eq. (34), the `ξ` recursion of Definition 2.3
  and the `L` tensor-replacement operator of Lemma 2.6;
* the error block `η_j = x^{⊗j} − y_j` of Eq. (17) and the forcing vector
  `(0,…,0,A_{N,N+1}x^{⊗(N+1)})` whose `V⁻¹`-image is `ζ` (Eq. (21)/(49)).

All matrices are taken over `ℂ`: the paper's analysis itself passes to `ℂ` in
Section 2.2 and the appendices (`G ∈ ℂ^{n×n}`, left/right eigenvectors of `F₁`).
Real matrices embed componentwise.  `autoImplicit` is off.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CarlemanLin24.MainResults.Source

/-- The index set of the two tensor factors of `F₂ : ℂⁿ ⊗ ℂⁿ → ℂⁿ`. -/
abbrev PairIdx (n : ℕ) := Fin 2 → Fin n

/-- A vector of `ℂⁿ`. -/
abbrev Vec (n : ℕ) := Fin n → ℂ

/-- The index set of the `j`-fold tensor power `(ℂⁿ)^{⊗j}`: a tuple of `j`
coordinates of `Fin n`. -/
abbrev TensorIdx (n j : ℕ) := Fin j → Fin n

/-- The block index of the Carleman vector `(y₁,…,y_N)`: block `j : Fin N`
holds the tensor power of order `j.val + 1`. -/
abbrev CarlemanIdx (n N : ℕ) := Σ j : Fin N, TensorIdx n (j.1 + 1)

/-- The `j`-fold tensor power of a vector `x`, `x^{⊗j}`, evaluated on a tuple:
the product of the entries along the tuple. -/
def tensorPower {n : ℕ} (x : Vec n) (j : ℕ) : TensorIdx n j → ℂ :=
  fun u => ∏ i : Fin j, x (u i)

/-- The ℓ¹ norm of a complex vector. -/
def vecL1 {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖

/-- The induced matrix 1-norm (maximum column sum of moduli), the norm used in
Eqs. (13), (42)–(44), (50) and (58).  The maximum is taken in `ℝ≥0` (which has
a bottom `0`) so that no nonemptiness assumption on the column index is
needed; for an empty column index the norm is `0`. -/
def matOneNorm {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  ↑((Finset.univ : Finset n).sup fun j => ∑ i : m, ‖A i j‖₊)

/-- The diagonal block `A_{b,b}` of Eq. (7):
`Σ_{i=1}^{b} I^{⊗(i−1)} ⊗ F₁ ⊗ I^{⊗(b−i)}`.  Concretely, the sum over the
position `i` at which `F₁` acts, with all other positions equal. -/
def kronF1 {n : ℕ} (F1 : Matrix (Fin n) (Fin n) ℂ) (b : ℕ) :
    Matrix (TensorIdx n b) (TensorIdx n b) ℂ :=
  fun u v =>
    ∑ i : Fin b,
      if (∀ k : Fin b, k ≠ i → u k = v k) then F1 (u i) (v i) else 0

/-- The pair of consecutive entries `(v i, v (i+1))` of `v : (Fin (b+1) → Fin n)`. -/
def pairAt {n b : ℕ} (v : TensorIdx n (b + 1)) (i : Fin b) : PairIdx n :=
  fun p => v ⟨i.1 + p.1, by omega⟩

/-- The off-diagonal block `A_{b,b+1}` of Eq. (7):
`Σ_{i=1}^{b} I^{⊗(i−1)} ⊗ F₂ ⊗ I^{⊗(b−i)}`: `F₂` consumes the consecutive
positions `i, i+1` of the `(b+1)`-fold tensor and produces the `i`-th entry of
the `b`-fold tensor. -/
def kronF2 {n : ℕ} (F2 : Matrix (Fin n) (PairIdx n) ℂ) (b : ℕ) :
    Matrix (TensorIdx n b) (TensorIdx n (b + 1)) ℂ :=
  fun u v =>
    ∑ i : Fin b,
      if (∀ k : Fin b, u k = v (Fin.succAbove (Fin.castSucc i) k)) then
        F2 (u i) (pairAt v i)
      else 0

/-- One application of the Carleman matrix `A` of Eq. (6) to a block vector:
the diagonal block `A_{j,j}` plus, when it exists, the super-diagonal block
`A_{j,j+1}`. -/
def carlemanOp {n N : ℕ} (F1 : Matrix (Fin n) (Fin n) ℂ)
    (F2 : Matrix (Fin n) (PairIdx n) ℂ) (y : CarlemanIdx n N → ℂ) :
    CarlemanIdx n N → ℂ
  | ⟨j, u⟩ =>
      (∑ v : TensorIdx n (j.1 + 1), kronF1 F1 (j.1 + 1) u v * y ⟨j, v⟩) +
        if h : j.1 + 1 < N then
          ∑ v : TensorIdx n (j.1 + 2), kronF2 F2 (j.1 + 1) u v * y ⟨⟨j.1 + 1, h⟩, v⟩
        else 0

/-- The Carleman matrix `A` of Eq. (6) as a matrix on the block index (built
from the operator `carlemanOp` on the standard basis of the block space). -/
def carlemanMat {n N : ℕ} (F1 : Matrix (Fin n) (Fin n) ℂ)
    (F2 : Matrix (Fin n) (PairIdx n) ℂ) : Matrix (CarlemanIdx n N) (CarlemanIdx n N) ℂ :=
  fun u v => carlemanOp F1 F2 (Pi.single v 1) u

/-- The right-hand side `F₁ x + F₂ x^{⊗2}` of the quadratic ODE (Eq. (4)). -/
def quadraticField {n : ℕ} (F1 : Matrix (Fin n) (Fin n) ℂ)
    (F2 : Matrix (Fin n) (PairIdx n) ℂ) (x : Vec n) : Vec n :=
  F1.mulVec x + F2.mulVec (fun p : PairIdx n => x (p 0) * x (p 1))

/-- The `j`-th block of a Carleman block vector. -/
def carlemanBlockVec {n N : ℕ} (y : CarlemanIdx n N → ℂ) (j : Fin N) :
    TensorIdx n (j.1 + 1) → ℂ :=
  fun u => y ⟨j, u⟩

/-- The block of size `b` (`1 ≤ b ≤ N`) of a Carleman block vector, with the
arithmetic cast `(b−1)+1 = b` performed explicitly. -/
def blockAt {n N : ℕ} (w : CarlemanIdx n N → ℂ) (b : ℕ) (hb : 0 < b) (hbN : b ≤ N) :
    TensorIdx n b → ℂ :=
  fun u =>
    w ⟨⟨b - 1, by omega⟩, by
      have h : b - 1 + 1 = b := by omega
      exact h.symm ▸ u⟩

/-- The first block of a Carleman block vector, i.e. the approximation `y₁` of
the ODE solution `x`.  Requires `N ≥ 1`. -/
def firstBlock {n N : ℕ} (hN : 0 < N) (y : CarlemanIdx n N → ℂ) : Vec n :=
  fun i => blockAt y 1 (by omega) hN (fun _ => i)

/-- The `(k,j)` block of a matrix on the Carleman block index, i.e.
`V_{k,j}` in the notation of Theorem 2.10. -/
def blockMat {n N : ℕ} (V : Matrix (CarlemanIdx n N) (CarlemanIdx n N) ℂ)
    (k j : Fin N) : Matrix (TensorIdx n (k.1 + 1)) (TensorIdx n (j.1 + 1)) ℂ :=
  fun u v => V ⟨k, u⟩ ⟨j, v⟩

/-- The initial Carleman state `y_j(0) = x(0)^{⊗j}` of Eq. (8). -/
def carlemanInit {n N : ℕ} (x0 : Vec n) : CarlemanIdx n N → ℂ
  | ⟨j, u⟩ => tensorPower x0 (j.1 + 1) u

/-- `z` is an eigenvalue of the matrix `M`: there is a nonzero vector sent to
`z • v`. -/
def IsEigenvalue {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (z : ℂ) : Prop :=
  ∃ v : ι → ℂ, v ≠ 0 ∧ M.mulVec v = z • v

/-- The eigenvalue set of the Carleman matrix in Lemma 2.1:
`{Σ_k m_k λ_k | m_k ∈ ℕ ∪ {0}, Σ_k m_k ≤ N}`. -/
def carlemanSpectrumSet {n : ℕ} (lam : Fin n → ℂ) (N : ℕ) : Set ℂ :=
  {z | ∃ m : Fin n → ℕ, (∑ i, m i) ≤ N ∧ z = ∑ i, (m i : ℂ) * lam i}

/-- The distances `|λ_i − Σ_j m_j λ_j|` occurring in the no-resonance
condition (10) and in the resonance parameter `Δ` of Eq. (11). -/
def resonanceDistances {n : ℕ} (lam : Fin n → ℂ) : Set ℝ :=
  {d | ∃ (i : Fin n) (m : Fin n → ℕ),
      2 ≤ ∑ j, m j ∧ d = ‖lam i - ∑ j, (m j : ℂ) * lam j‖}

/-- The no-resonance condition (Eq. (10), p. 3): no eigenvalue is an integer
combination of order at least two of the eigenvalues. -/
def NoResonance {n : ℕ} (lam : Fin n → ℂ) : Prop :=
  ∀ (i : Fin n) (m : Fin n → ℕ), 2 ≤ ∑ j, m j → lam i ≠ ∑ j, (m j : ℂ) * lam j

/-- Assumption 1 of the paper (pp. 3–4): `F₁ = W Λ W⁻¹` is diagonalizable with
non-positive real-part eigenvalues and satisfies the no-resonance condition;
`Δ > 0` is the resonance parameter of Eq. (11). -/
structure AssumptionOne {n : ℕ} (F1 : Matrix (Fin n) (Fin n) ℂ)
    (W Winv : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ) (Δ : ℝ) : Prop where
  /-- `W` and `W⁻¹` are mutual inverses. -/
  left_inv : W * Winv = 1
  /-- `W` and `W⁻¹` are mutual inverses. -/
  right_inv : Winv * W = 1
  /-- The diagonalization `F₁ = W Λ W⁻¹`. -/
  diagonalizes : F1 = W * Matrix.diagonal lam * Winv
  /-- Non-positive real parts. -/
  re_nonpos : ∀ i, (lam i).re ≤ 0
  /-- No resonance (Eq. (10)). -/
  no_resonance : NoResonance lam
  /-- `Δ` is the infimum of the resonance distances (Eq. (11)). -/
  delta_isGLB : IsGLB (resonanceDistances lam) Δ
  /-- Positivity of the resonance parameter. -/
  delta_pos : 0 < Δ

/-- The condition number `κ₁(W) = ‖W‖₁ ‖W⁻¹‖₁` of the paper. -/
def kappa1 {n : ℕ} (W Winv : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  matOneNorm W * matOneNorm Winv

/-- The constant `C = κ₁(W) ‖F₂‖₁ μ²` of Eq. (14). -/
def errorConstant {n : ℕ} (W Winv : Matrix (Fin n) (Fin n) ℂ)
    (F2 : Matrix (Fin n) (PairIdx n) ℂ) (μ : ℝ) : ℝ :=
  kappa1 W Winv * matOneNorm F2 * μ ^ 2

/-- The convergence rate `Rᵣ = 4 e μ κ₁(W) ‖F₂‖₁ / Δ` of Eq. (14). -/
def convergenceRate {n : ℕ} (W Winv : Matrix (Fin n) (Fin n) ℂ)
    (F2 : Matrix (Fin n) (PairIdx n) ℂ) (Δ μ : ℝ) : ℝ :=
  4 * Real.exp 1 * μ * kappa1 W Winv * matOneNorm F2 / Δ

/-- The error block `η_j(t) = x(t)^{⊗j} − y_j(t)` of Eq. (17). -/
def etaBlock {n N : ℕ} (x : ℝ → Vec n) (y : ℝ → CarlemanIdx n N → ℂ)
    (j : Fin N) (t : ℝ) : TensorIdx n (j.1 + 1) → ℂ :=
  fun u => tensorPower (x t) (j.1 + 1) u - y t ⟨j, u⟩

/-- The forcing vector `(0,…,0, A_{N,N+1} x^{⊗(N+1)})` of Eq. (18): only the
last block is nonzero. -/
def forcingVec {n N : ℕ} (F2 : Matrix (Fin n) (PairIdx n) ℂ) (x : Vec n) :
    CarlemanIdx n N → ℂ
  | ⟨j, u⟩ =>
      if j.1 + 1 = N then
        ∑ v : TensorIdx n (j.1 + 2), kronF2 F2 (j.1 + 1) u v * tensorPower x (j.1 + 2) v
      else 0

/-- The `G` matrices of Eq. (34): `G_{i_k:i'_k} = ((λ_{i_k}+⋯+λ_{i'_k}) I − F₁)⁻¹`.
The model takes `G` as a family of matrices indexed by the pair of positions
`(start, length)` that occur in the recursion. -/
def Gmatrix {n : ℕ} (F1 : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ)
    (S : ℕ → ℕ → Fin n) (start len : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (∑ t : Fin (len + 1), lam (S start t)) • 1 - F1

/-- The `ξ` recursion of Definition 2.3 / Eq. (73): `ξ_m^{(0)} = e_m` and
`ξ_m^{(c+1)} = Σ_{a=0}^{c} F₂ (G ξ_m^{(a)}, G ξ_{m+a+1}^{(c−a)})`.
`G` is the family of Eq. (34), indexed by the start position and block length. -/
def IsXiRecursion {n : ℕ} (F2 : Matrix (Fin n) (PairIdx n) ℂ)
    (G : ℕ → ℕ → Matrix (Fin n) (Fin n) ℂ) (base : ℕ → Vec n)
    (xi : ℕ → ℕ → Vec n) : Prop :=
  (∀ m : ℕ, xi m 0 = base m) ∧
    ∀ (m c : ℕ),
      xi m (c + 1) =
        ∑ a ∈ Finset.range (c + 1),
          F2.mulVec fun p : PairIdx n =>
            (G m a).mulVec (xi m a) (p 0) * (G (m + a + 1) (c - a)).mulVec (xi (m + a + 1) (c - a)) (p 1)

/-- The tensor-replacement operator `L` of Lemma 2.6, in the rank-one form used
by the norm estimate (39): the tensor product of the `r` block vectors
`G_{p_b} ξ^{(k_b)} ∈ ℂⁿ`, one per tensor factor of the `(j−k)`-block. -/
def Ltensor {n r : ℕ} (z : Fin r → Vec n) : TensorIdx n r → ℂ :=
  fun u => ∏ b : Fin r, z b (u b)

/-- The compositions of `k` into exactly `r` nonnegative parts, the index set
of the sums in Eqs. (36), (37) and (39).  Represented as the image of the
finite type `Fin r → Fin (k+1)` of parts bounded by `k`, filtered by `Σ = k`;
this makes the composition set finite without assuming a `Fintype` instance on
`Fin r → ℕ`. -/
def compositions (k r : ℕ) : Finset (Fin r → ℕ) :=
  ((Finset.univ : Finset (Fin r → Fin (k + 1))).filter
      (fun f => ∑ i, (f i : ℕ) = k)).image (fun f i => (f i : ℕ))

/-- The right-hand side of the eigenvector expansions (36)/(37): sum over the
compositions of `k` into `r = j−k` parts of the `L`-images of the block vectors
`G_{p_b} ξ^{(k_b)}`.  `blockVec` supplies those vectors for each composition and
block. -/
def expansionRHS {n : ℕ} (k r : ℕ) (blockVec : (Fin r → ℕ) → Fin r → Vec n)
    (u : TensorIdx n r) : ℂ :=
  ∑ m ∈ compositions k r, Ltensor (fun b => blockVec m b) u

end Qatlib.Papers.CarlemanLin24.MainResults.Source
