/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# FastFwdDissip24 — source model

Jin–Liu–Yu, *Fast-forwarding quantum algorithms for linear dissipative
differential equations*, arXiv:2410.13189 (fixed version; accepted in Quantum
2026-01-04).

The paper studies the linear ODE `u'(t) = A(t) u(t) + b(t)` (Eq. (1)) under the
dissipativity condition `A(t) + A(t)† ⪯ -2η < 0` (Eq. (11)), discretized by a
single-step scheme `L_j u_{j+1} = R_j u_j + v_j` (Eq. (15)), and assembled into
the all-at-once block matrix `A_{M,Mp-1}` of Eq. (26).

This file fixes the shared model: the paper's time-ordered exponential
`T exp(∫ A)` (identified with the library Dyson propagator of generator `-A`),
the dissipativity predicate, the block matrix of Eq. (26), and the query-cost
bookkeeping used by Theorems 8–10 and Corollaries 11–19.

Boundary: this is a paper-layer model. It reuses the frozen Dyson propagator
`QuantumAlgorithm.Papers.QLinearODE17.TaylorAnalysis.orderedEvolution` and the
frozen `EuclideanSpace` representation bridge; it introduces no new axioms and
does not touch shared Foundations/Concepts.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.FastFwdDissip24.MainResults

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath.BornBridge

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The paper's time-ordered exponential `T exp(∫_s^t A)` for the ODE
`u' = A u`: it is the library's Dyson propagator of the generator `-A`
(which solves `d/dt V = A V`). Eq. (12)/(13) are stated in this notation. -/
def paperPropagator (A : ℝ → Matrix I I ℂ) (s t : ℝ) : Matrix I I ℂ :=
  orderedEvolution (fun u => -A u) s t

/-- Dissipativity, Eq. (11): `A(t) + A(t)† ⪯ -2η`, expressed as positive
semidefiniteness of the Hermitian part of `-(A(t) + η • 1)` — i.e. of the
generator exposed by `orderedEvolution`, whose Hermitian part is then PSD. -/
def Dissipative (A : ℝ → Matrix I I ℂ) (η : ℝ) : Prop :=
  ∀ t, ((-(A t + η • (1 : Matrix I I ℂ))) +
        (-(A t + η • (1 : Matrix I I ℂ)))ᴴ).PosSemidef

/-- A single-step scheme Eq. (15): `L_j u_{j+1} = R_j u_j + v_j`. `h` is the
step size; the paper writes `L_j = L(j,h)` etc. (Eq. (16)). -/
structure SingleStep (I : Type) [Fintype I] [DecidableEq I] where
  /-- Step matrix `L_j`. -/
  L : ℕ → Matrix I I ℂ
  /-- Step matrix `R_j`. -/
  R : ℕ → Matrix I I ℂ
  /-- Inhomogeneous source `v_j`. -/
  v : ℕ → I → ℂ

/-- Diagonal block of `A_{M,Mp-1}` at block row `i` (Eq. (26)): the identity
on row `0`, `L_{i-1}` on rows `1..M-1`, and the padding identity on rows `≥ M`. -/
def allAtOnceDiag (L : ℕ → Matrix I I ℂ) (M i : ℕ) : Matrix I I ℂ :=
  if i = 0 then 1 else if i < M then L (i - 1) else 1

/-- Sub-diagonal block of `A_{M,Mp-1}` at block row `i ≥ 1` (Eq. (26)):
`-R_{i-1}` on rows `1..M-1` and the padding `-1` on rows `≥ M`. -/
def allAtOnceSub (R : ℕ → Matrix I I ℂ) (M i : ℕ) : Matrix I I ℂ :=
  if i < M then -R (i - 1) else -1

/-- The all-at-once block matrix `A_{M,Mp-1}` of Eq. (26): a block bidiagonal
matrix with diagonal blocks `allAtOnceDiag` and sub-diagonal blocks
`allAtOnceSub`. Block size is the (finite) system dimension `I`. -/
def allAtOnce (L R : ℕ → Matrix I I ℂ) (M Mp : ℕ) :
    Matrix (Fin (M + Mp - 1) × I) (Fin (M + Mp - 1) × I) ℂ :=
  fun p q =>
    if p.1 = q.1 then
      allAtOnceDiag L M (p.1 : ℕ) p.2 q.2
    else if (q.1 : ℕ) + 1 = (p.1 : ℕ) then
      allAtOnceSub R M (p.1 : ℕ) p.2 q.2
    else 0

/-- The diagonal-block submatrix `M_{i,j}` (block `(i,j)`) of a matrix indexed
by `ι × κ`; this is the `M_{ij}` of Lemma 6. -/
def blockSub {ι κ : Type} (M : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) :
    Matrix κ κ ℂ :=
  M.submatrix (fun a => (i, a)) (fun b => (j, b))

/-- Maximum, over `j < M`, of `‖L j‖` (paper's `max_j ‖L_j‖`), taken in `ℝ≥0`
so that the empty range gives `0`. -/
def maxNorm (L : ℕ → Matrix I I ℂ) (M : ℕ) : NNReal :=
  (Finset.range M).sup (fun j => ‖L j‖₊)

/-- Maximum, over `j < M`, of `‖(L j)⁻¹‖` (paper's `max_j ‖L_j⁻¹‖`). -/
def maxInvNorm (L : ℕ → Matrix I I ℂ) (M : ℕ) : NNReal :=
  (Finset.range M).sup (fun j => ‖(L j)⁻¹‖₊)

/-- The paper's step size `h = T / M`. -/
def stepSize (T : ℝ) (M : ℕ) : ℝ := T / M

/-- A vec `v` is an `ε`-approximation (in Euclidean norm) of the target `w`. -/
def EpsilonApprox (v w : I → ℂ) (ε : ℝ) : Prop :=
  ‖toEuclidean_fromVec (v - w)‖ ≤ ε

/-- History-state error, Eq. (23): the all-at-once vector `[u(0); u(h); …; u(Mh)]`
compared with the ideal trajectory. -/
def IsHistoryApprox (traj : ℕ → I → ℂ) (M : ℕ) (idealtraj : ℕ → I → ℂ) (ε : ℝ) : Prop :=
  ∀ k ≤ M, EpsilonApprox (traj k) (idealtraj k) ε

/-- Query cost of the quantum linear-system step: `κ log(1/δ)`, the standard
cost of a QLSA in the condition number times a logarithmic accuracy factor.
This is the cost model the paper's Theorems 8–10 use (cf. Eq. (112), (113)). -/
def qlsaQueries (κ δ : ℝ) : ℝ := κ * Real.log (1 / δ)

/-- Total history-state query cost: QLSA queries times the amplitude-amplification
repetitions `M/(ηT)` used by the paper (Eq. (51), (91)). -/
def historyQueries (κ M ηT ε : ℝ) : ℝ := qlsaQueries κ (ε / 2) * (M / ηT)

/-- The single-step solution of Eq. (15): `u_0 = u0` and
`u_{k+1} = L_k^{-1} (R_k u_k + v_k)`. This is the vector the all-at-once linear
system of Eq. (26) is solved for, restricted to time `k h`. -/
def discreteSol (S : SingleStep I) (u0 : I → ℂ) : ℕ → I → ℂ
  | 0 => u0
  | k + 1 => (S.L k)⁻¹ *ᵥ (S.R k *ᵥ discreteSol S u0 k + S.v k)

/-- Grid sampling of a `ℕ`-indexed trajectory: `gridFun u h t = u ⌊t/h⌋`. This lets a
single-step solution `discreteSol` be compared with a continuous exact solution in
`historyStateError`; on the sample points `p.1 * h` of Eq. (23) one has
`⌊(p.1 * h)/h⌋ = p.1` when `h > 0`. -/
noncomputable def gridFun (u : ℕ → I → ℂ) (h : ℝ) : ℝ → I → ℂ :=
  fun t => u (Nat.floor (t / h))

/-- `u` is the exact classical solution of the ODE Eq. (1) on `[0,T]` with initial
value `u0`: `u(0) = u0` and `d/dt u(t) = A(t) u(t) + b(t)` for all `t ∈ [0,T]`.
Uniqueness is the content of the classical ODE theory (not reproved here). -/
def IsExactSolution (A : ℝ → Matrix I I ℂ) (b : ℝ → I → ℂ) (u0 : I → ℂ)
    (u : ℝ → I → ℂ) (T : ℝ) : Prop :=
  u 0 = u0 ∧ ∀ t ∈ Set.Icc 0 T, HasDerivAt u (A t *ᵥ u t + b t) t

/-- The normalized Euclidean vector `x / ‖x‖`. -/
noncomputable def normalizeE {J : Type} [Fintype J] (x : EuclideanSpace ℂ J) :
    EuclideanSpace ℂ J :=
  ((‖x‖ : ℂ))⁻¹ • x

/-- The history vector `[u(0); u(h); …; u(M h)]` of Eq. (23) as a single vector over
the index set `Fin (M+1) × I`, equipped with the Euclidean norm. -/
def bigHistory (u : ℝ → I → ℂ) (h : ℝ) (M : ℕ) : EuclideanSpace ℂ (Fin (M + 1) × I) :=
  toEuclidean_fromVec (fun p : Fin (M + 1) × I => u ((p.1 : ℕ) * h) p.2)

/-- History-state error, Eq. (23): the Euclidean distance between the normalized
big history vector of the algorithm's trajectory and that of the exact solution. -/
noncomputable def historyStateError (u v : ℝ → I → ℂ) (h : ℝ) (M : ℕ) : ℝ :=
  ‖normalizeE (bigHistory u h M) - normalizeE (bigHistory v h M)‖

/-- Final-state error at time `T`: the Euclidean distance between the normalized
algorithm output and the normalized exact solution. -/
noncomputable def finalStateError (u v : I → ℂ) : ℝ :=
  ‖normalizeE (toEuclidean_fromVec u) - normalizeE (toEuclidean_fromVec v)‖

/-- The condition-number proxy used by Theorems 8–10 and Corollary 11, assembled from
Lemma 7: `(1 + max‖L_j‖ + max‖R_j‖)(1 + max‖L_j^{-1}‖)(2eM/(ηT) + M_p)`. -/
def conditionNumber (L R : ℕ → Matrix I I ℂ) (M Mp : ℕ) (ηT : ℝ) : ℝ :=
  (1 + (maxNorm L M : ℝ) + (maxNorm R M : ℝ)) *
    (1 + (maxInvNorm L M : ℝ)) * (2 * Real.exp 1 * (M : ℝ) / ηT + (Mp : ℝ))

end Qatlib.Papers.FastFwdDissip24.MainResults
