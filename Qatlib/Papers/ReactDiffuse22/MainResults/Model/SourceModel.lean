/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option backward.isDefEq.respectTransparency false

/-!
# ReactDiffuse22 — source model

Jin--Liu--Yu, *Efficient quantum algorithm for nonlinear reaction-diffusion
equations and energy estimation*, fixed arXiv:2205.01141.

This module is the **object layer** for the paper block `ReactDiffuse22.MainResults`.
It fixes the paper's notation as concrete Lean objects so that every active
claim of the block can be stated against the same definitions:

* the grid `I = [n]^d` (`GridIndex`), the ℓ2 and ℓ∞ norms of a grid vector;
* the one-dimensional discrete Laplacians `D_h^{Dir}` (2.9) and `D_h^{per}`
  (2.10), and the `d`-dimensional Kronecker-sum Laplacian `Δ_h` (2.8);
* the discrete reaction-diffusion field (2.7) and its polynomial instance (2.16),
  together with the ODE solution predicate and the boundary side condition;
* the Carleman blocks `A_j^j` (3.2) and `A_j^{j+M-1}` (3.3) on the tensor spaces
  `I^⊗j`, the exact tensor power `U^⊗j`, and the truncation error `η_j` (3.9);
* the forward-Euler scheme (4.3), the Euler system matrix `L` (4.5), the
  condition number, and the history-state vectors of (2.15)/(4.32);
* an abstract **query ledger** for the quantum-algorithm statements: the block
  does not build a circuit model of its own, so Theorems 4.1/6.1/6.2/6.3 are
  stated over the ledger and the output guarantee, exactly as in the source
  interface style of the surrounding library.

Boundary: nothing here asserts any claim of the paper; the claim theorems live
in `MainResults/Source/` and import this file.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.ReactDiffuse22.MainResults

/-! ## 1. Grid and norms -/

/-- The spatial grid `I = [n]^d` of the paper, `n^d` points. -/
abbrev GridIndex (n d : ℕ) := Fin d → Fin n

/-- The ℓ2 norm `‖v‖` of a real grid vector. -/
def l2Norm {ι : Type} [Fintype ι] (v : ι → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- The ℓ∞ norm `‖v‖∞ = max_j |v_j|` of a real grid vector. -/
def linfNorm {ι : Type} [Fintype ι] [Nonempty ι] (v : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |v i|)

/-- The ℓ2 norm is non-negative. -/
lemma l2Norm_nonneg {ι : Type} [Fintype ι] (v : ι → ℝ) : 0 ≤ l2Norm v :=
  Real.sqrt_nonneg _

/-- The ℓ∞ norm is non-negative. -/
lemma linfNorm_nonneg {ι : Type} [Fintype ι] [Nonempty ι] (v : ι → ℝ) : 0 ≤ linfNorm v := by
  unfold linfNorm
  have h := Finset.le_sup' (fun i => |v i|) (Finset.mem_univ (Classical.arbitrary ι))
  exact (abs_nonneg _).trans h

/-- Every coordinate is bounded by the ℓ∞ norm. -/
lemma le_linfNorm {ι : Type} [Fintype ι] [Nonempty ι] (v : ι → ℝ) (j : ι) :
    |v j| ≤ linfNorm v := by
  unfold linfNorm
  exact Finset.le_sup' (fun i => |v i|) (Finset.mem_univ j)

/-- The operator ℓ∞ norm `‖A‖∞`, i.e. the maximal row sum of absolute values. -/
def opNormInf {m n : Type} [Fintype m] [Fintype n] [Nonempty m]
    (A : Matrix m n ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, |A i j|)

/-- The operator ℓ2 norm `‖A‖₂` (Mathlib's `Matrix.Norms.L2Operator`). -/
def opNorm2 {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : ℝ := ‖A‖

/-- The ℓ2 operator norm is non-negative. -/
lemma opNorm2_nonneg {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : 0 ≤ opNorm2 A := norm_nonneg A

/-! ## 2. The discrete Laplacians -/

/-- The one-dimensional central-difference Laplacian with homogeneous Dirichlet
boundary condition, `D_h^{Dir} = (n+1)^2 · tridiag(1,-2,1)` (2.9). -/
def dirichletLap1D (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    ((n : ℝ) + 1) ^ 2 *
      (if i = j then (-2 : ℝ)
       else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0)

/-- The one-dimensional discrete Laplacian with periodic boundary condition,
`D_h^{per} = n^2 · circulant(1,-2,1)` (2.10).  The wrap-around edges join
`n-1` to `0` in both directions. -/
def periodicLap1D (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    (n : ℝ) ^ 2 *
      (if i = j then (-2 : ℝ)
       else if i.val + 1 = j.val ∨ j.val + 1 = i.val
              ∨ (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then 1 else 0)

/-- The `d`-dimensional discrete Laplacian `Δ_h` (2.8): the Kronecker sum of the
per-dimension one-dimensional Laplacians `Dh c`. -/
def lapFull {n d : ℕ} (Dh : Fin d → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (GridIndex n d) (GridIndex n d) ℝ :=
  Matrix.of fun x y =>
    ∑ c : Fin d, if (∀ e : Fin d, e ≠ c → x e = y e) then Dh c (x c) (y c) else 0

/-- The mixed boundary condition of (2.3): `d1` Dirichlet dimensions followed by
`d2 = d - d1` periodic dimensions. -/
def IsMixedDiscreteLaplacian (n d d1 : ℕ) (Dh : Fin d → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  d1 ≤ d ∧ ∀ c : Fin d,
    (if c.val < d1 then Dh c = dirichletLap1D n else Dh c = periodicLap1D n)

/-- The linear part `F_1 = D Δ_h + a I` of (2.16). -/
def F1Matrix {n d : ℕ} (D a : ℝ) (Dh : Fin d → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (GridIndex n d) (GridIndex n d) ℝ :=
  Matrix.of fun x y => D * lapFull Dh x y + if x = y then a else 0

/-- The nonlinear coefficient `F_M` of (2.16): it sends the `M`-fold tensor
`u^⊗M` to the componentwise power `b · u^{.M}`, i.e. its only non-zero entries
contract a tensor all of whose factors agree. -/
def FMMatrix {n d : ℕ} (b : ℝ) (M : ℕ) :
    Matrix (GridIndex n d) (Fin M → GridIndex n d) ℝ :=
  Matrix.of fun x y => if (∀ k : Fin M, y k = x) then b else 0

/-! ## 3. The reaction-diffusion flow -/

/-- The general discrete reaction-diffusion field (2.7)
`(dU/dt)_j = D ∑_k (Δ_h)_{jk} U_k + f(U_j)`. -/
def rdFieldGen {n d : ℕ} (D : ℝ) (Dh : Fin d → Matrix (Fin n) (Fin n) ℝ)
    (f : ℝ → ℝ) (U : GridIndex n d → ℝ) : GridIndex n d → ℝ :=
  fun j => D * ∑ k, lapFull Dh j k * U k + f (U j)

/-- The polynomial field (2.16), `f(u) = a u + b u^M`. -/
def rdFieldPoly {n d : ℕ} (D a b : ℝ) (M : ℕ) (Dh : Fin d → Matrix (Fin n) (Fin n) ℝ)
    (U : GridIndex n d → ℝ) : GridIndex n d → ℝ :=
  fun j => D * ∑ k, lapFull Dh j k * U k + a * U j + b * (U j) ^ M

/-- `U` solves the initial value problem (2.7) with initial datum `u0`. -/
def IsRDESolution {n d : ℕ} (D : ℝ) (Dh : Fin d → Matrix (Fin n) (Fin n) ℝ)
    (f : ℝ → ℝ) (u0 : GridIndex n d → ℝ) (U : ℝ → GridIndex n d → ℝ) : Prop :=
  U 0 = u0 ∧ ∀ t, 0 ≤ t → HasDerivAt U (rdFieldGen D Dh f (U t)) t

/-- `U` solves the polynomial system (2.16). -/
def IsRDEPSolution {n d : ℕ} (D a b : ℝ) (M : ℕ)
    (Dh : Fin d → Matrix (Fin n) (Fin n) ℝ) (u0 : GridIndex n d → ℝ)
    (U : ℝ → GridIndex n d → ℝ) : Prop :=
  U 0 = u0 ∧ ∀ t, 0 ≤ t → HasDerivAt U (rdFieldPoly D a b M Dh (U t)) t

/-- The boundary side condition of Lemma 2.1: on the boundary indices `B` the
solution stays inside `[γ1, γ2]` for all `t ≥ 0`. -/
def BoundaryWithin {n d : ℕ} (B : Set (GridIndex n d)) (γ1 γ2 : ℝ)
    (U : ℝ → GridIndex n d → ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ j ∈ B, γ1 ≤ U t j ∧ U t j ≤ γ2

/-- `γ` is a root of `f`. -/
def IsRoot (f : ℝ → ℝ) (γ : ℝ) : Prop := f γ = 0

/-- `γ` is the largest absolute value of the roots of `f`, as in Lemma 2.1(ii). -/
def LargestAbsRoot (f : ℝ → ℝ) (γ : ℝ) : Prop :=
  (∃ r, IsRoot f r ∧ |r| = γ) ∧ ∀ r, IsRoot f r → |r| ≤ γ

/-! ## 4. Carleman linearization -/

/-- The tensor space `I^⊗j`, indexed by `j`-tuples of grid points. -/
abbrev TensorIndex (ι : Type) (j : ℕ) := Fin j → ι

/-- The exact tensor power `U^⊗j` (3.1). -/
def exactTensor {ι : Type} (U : ι → ℝ) (j : ℕ) : TensorIndex ι j → ℝ :=
  fun x => ∏ k : Fin j, U (x k)

/-- The diagonal Carleman block `A_j^j` (3.2): the Kronecker sum of `j` copies of
`F_1`, acting on `I^⊗j`. -/
def carlemanDiagBlock {ι : Type} [Fintype ι] [DecidableEq ι]
    (F1 : Matrix ι ι ℝ) (j : ℕ) : Matrix (TensorIndex ι j) (TensorIndex ι j) ℝ :=
  Matrix.of fun x y =>
    ∑ ν : Fin j, if (∀ e : Fin j, e ≠ ν → x e = y e) then F1 (x ν) (y ν) else 0

/-- The off-diagonal Carleman block `A_j^{j+M-1}` (3.3): the sum over the `j`
ways of placing the nonlinearity `F_M` on `M` consecutive tensor slots, with
identities elsewhere.  The untouched `j-1` output slots are matched against the
input tuple with the contracted block deleted (the `if e.val < ν.val` shift). -/
def carlemanCrossBlock {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (FM : Matrix ι (Fin M → ι) ℝ) (j : ℕ) (hM : 1 ≤ M) :
    Matrix (TensorIndex ι j) (TensorIndex ι (j + (M - 1))) ℝ :=
  Matrix.of fun x y =>
    ∑ ν : Fin j,
      if (∀ e : Fin j, e ≠ ν →
            x e = y ⟨if e.val < ν.val then e.val else e.val + (M - 1), by
              have he : e.val < j := e.isLt
              have hν : ν.val < j := ν.isLt
              split_ifs <;> omega⟩) then
        FM (x ν) (fun k : Fin M => y ⟨ν.val + k.val, by
          have hν : ν.val < j := ν.isLt
          have hk : k.val < M := k.isLt
          omega⟩)
      else 0

/-- The truncation error `η_j(t) = U(t)^⊗j − ŷ_j(t)` of (3.9). -/
def truncError {ι : Type} (U : ℝ → ι → ℝ)
    (yhat : (j : ℕ) → ℝ → TensorIndex ι j → ℝ) (j : ℕ) (t : ℝ) :
    TensorIndex ι j → ℝ :=
  fun x => exactTensor (U t) j x - yhat j t x

/-- `λ1` is the largest eigenvalue of `A`: real eigenvector characterisation. -/
def IsLargestEigenvalue {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lam1 : ℝ) : Prop :=
  (∃ v : ι → ℝ, v ≠ 0 ∧ A *ᵥ v = lam1 • v) ∧
    ∀ (μ : ℝ) (v : ι → ℝ), v ≠ 0 → A *ᵥ v = μ • v → μ ≤ lam1

/-! ## 5. Forward Euler, the Euler system matrix, history states -/

/-- The forward-Euler step (4.3) `y^{k+1} = y^k + h A y^k = (I + hA) y^k`. -/
def eulerStep {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (h : ℝ) (y : ι → ℝ) : ι → ℝ :=
  y + h • (A *ᵥ y)

/-- The `k`-th forward-Euler iterate `y^k = (I + hA)^k y^0`. -/
def eulerIterate {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (h : ℝ) (k : ℕ) (y0 : ι → ℝ) : ι → ℝ :=
  ((1 + h • A) ^ k) *ᵥ y0

/-- The Euler system matrix `L` of (4.5), acting on the history space
`(m+1) × I`: identity on the diagonal blocks and `-(I + Ah)` on the subdiagonal. -/
def eulerSystemMatrix {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (h : ℝ) (m : ℕ) :
    Matrix (Fin (m + 1) × ι) (Fin (m + 1) × ι) ℝ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then (if p.2 = q.2 then (1 : ℝ) else 0)
    else if p.1.val = q.1.val + 1 then
      (-(if p.2 = q.2 then (1 : ℝ) else 0) - h * A p.2 q.2)
    else 0

/-- The condition number `κ(L) = ‖L‖ ‖L⁻¹‖` of a square matrix. -/
def conditionNumber {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℝ) : ℝ :=
  opNorm2 L * opNorm2 L⁻¹

/-- The history state vector `Y = ∑_k y^k |k⟩` of (4.32), as a function on
`(k, block, grid point)`. -/
def historyVector {ι : Type} (N m : ℕ) (y : Fin (m + 1) → Fin N → ι → ℝ) :
    Fin (m + 1) × Fin N × ι → ℝ :=
  fun p => y p.1 p.2.1 p.2.2

/-- The squared norm of the history state restricted to the first block
`Y_evo = ∑_k y_1^k |k⟩`, appearing in (4.36). -/
def firstBlockNormSq {ι : Type} [Fintype ι] {N : ℕ} [NeZero N] (m : ℕ)
    (y : Fin (m + 1) → Fin N → ι → ℝ) : ℝ :=
  ∑ k : Fin (m + 1), l2Norm (y k 0) ^ 2

/-- The squared norm of the full history state `‖|Y⟩‖²` of (4.38). -/
def fullHistoryNormSq {ι : Type} [Fintype ι] (N m : ℕ)
    (y : Fin (m + 1) → Fin N → ι → ℝ) : ℝ :=
  ∑ k : Fin (m + 1), ∑ j : Fin N, l2Norm (y k j) ^ 2

/-- The measurement probability `P_measure = ‖Y_evo‖² / ‖Y‖²` of (4.39). -/
def measureProbability {ι : Type} [Fintype ι] (N m : ℕ) [NeZero N]
    (y : Fin (m + 1) → Fin N → ι → ℝ) : ℝ :=
  firstBlockNormSq m y / fullHistoryNormSq N m y

/-! ## 6. The query ledger of the algorithms -/

/-- The query ledger of a quantum algorithm: the number of queries it makes to
each of the available oracles and the number of elementary gates.  The block
does not formalize a circuit model; the paper's algorithms are represented by
their ledger together with the output guarantee (see `QCLRun`). -/
structure QueryLedger where
  /-- queries to the oracle `O_{F_1}` -/
  qF1 : ℝ
  /-- queries to the oracle `O_{F_M}` (or `O_D` in Section 6) -/
  qFM : ℝ
  /-- queries to the state-preparation oracle `O_x` / `A` -/
  qx : ℝ
  /-- applications of the reflection `I - 2P` -/
  qProj : ℝ
  /-- number of elementary gates -/
  gates : ℝ

/-- The total number of oracle queries of a ledger. -/
def QueryLedger.total (q : QueryLedger) : ℝ := q.qF1 + q.qFM + q.qx + q.qProj

/-- The output guarantee of the quantum Carleman-linearization algorithm of
Theorem 4.1: an `ℓ2`-normalized error `l2Error`, a success probability, a
success flag, and the query ledger that produced them. -/
structure QCLRun where
  ledger : QueryLedger
  /-- ℓ2-normalized error between the output state and `|Ŷ_evo⟩` -/
  l2Error : ℝ
  /-- success probability of the flag -/
  successProb : ℝ
  /-- the algorithm carries a success flag that is correct with `successProb` -/
  flagSound : Prop

/-! ## 7. Section-specific constants and Section 6 output carriers -/

/-- The ceiling division `⌈a / b⌉` used in the exponents of Theorem 3.2/3.3. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- The constant `C(λ)` of (3.15). -/
def Cconst (d1 : ℕ) (a lam1 lam : ℝ) : ℝ :=
  if a ≠ 0 then
    |lam1| / a * (Real.exp (Real.log 3 * (d1 : ℝ) / (2 * (lam - lam1)) * a) - 1)
      + |lam1| / |lam|
  else
    Real.log 3 * (d1 : ℝ) / (2 * (lam - lam1)) * |lam1| + |lam1| / |lam|

/-- The convergence radius `γ = (|a|/|b|)^{1/(M-1)}` of (2.6)/(3.14). -/
def gammaRad (a b : ℝ) (M : ℕ) : ℝ := (|a| / |b|) ^ ((1 : ℝ) / ((M : ℝ) - 1))

/-- The ℓ∞ convergence radius `R_D` of (3.14). -/
def RDconst (a b lam1 lam : ℝ) (d1 M : ℕ) : ℝ :=
  |b| / |lam1| * (gammaRad a b M) ^ (M - 1) * Cconst d1 a lam1 lam

/-- The mean-square amplitude ratio (6.3): the fraction of the squared ℓ2 mass
lying in the domain `Dset`. -/
def meanSquareRatio {ι : Type} [Fintype ι] (Dset : Set ι) (v : ι → ℝ) : ℝ := by
  classical
  exact (∑ i ∈ Finset.univ.filter (fun i => i ∈ Dset), v i ^ 2) / (∑ i, v i ^ 2)

/-- Output carrier of the amplitude-estimation algorithm of Theorem 6.1. -/
structure RatioEstimator where
  ledger : QueryLedger
  /-- the estimated value of the ratio (6.3) -/
  output : ℝ
  successProb : ℝ

/-- Output carrier of the gradient-state preparation algorithm of Theorem 6.2. -/
structure GradientPreparer (ιgrad : Type) where
  ledger : QueryLedger
  /-- the prepared (unnormalised) gradient vector (6.20) -/
  output : ιgrad → ℝ
  /-- ℓ2 distance to the target gradient vector -/
  outputError : ℝ
  successProb : ℝ

/-- Output carrier of the composed kinetic-energy-ratio algorithm of
Corollary 6.3. -/
structure KineticRatioEstimator where
  ledger : QueryLedger
  output : ℝ
  successProb : ℝ

/-- An instance of the quantum quadratic ODE problem (Problem 1) at the level of
the paper's reaction-diffusion reduction: the convergence radius `R`, the a
priori bound `γ`, and the initial data. -/
structure QuadraticODEInstance (ι : Type) where
  R : ℝ
  gamma : ℝ
  Uin : ι → ℝ

/-- An abstract algorithm for preparing `u(T)/‖u(T)‖`; only its worst-case
query count and its target guarantee are recorded. -/
structure StatePrepAlgorithm where
  T : ℝ
  worstCaseQueries : ℝ
  preparesTarget : Prop

end Qatlib.Papers.ReactDiffuse22.MainResults
