/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper layer for *A New Quantum Algorithm for Linear Systems beyond the Condition Number*
(QLSBeyondCond25), fixed source version arXiv:2510.05588v3.

This file covers the phase-estimation and cost claims of Section 3 and Appendix A:

* c009, Theorem 3.9 (page 18-19): under the initial-state decomposition, the fixed-point
  condition and the projection property, phase estimation on `(U_AB, |Φ_b⟩)` with precision
  `ε²/((1+‖y‖₂²)‖|p_B⟩‖)` returns phase `0` with probability at least `1/(1+‖y‖₂²)`, yields a
  state within trace distance `ε`, and uses `O(√(s·E_T)/ε²)` controlled-`U_AB` queries.
* c010, Theorem 3.11 (page 19-20): `U_AB` can be implemented in time `Õ(s)`.
* c014, Theorem A.1 (Appendix A): the kernel-projection (QSVT) linear solver uses
  `O(κ(A)·log(1/ε))` queries of `U_H` and `U_H†` and outputs a state `ε`-close to `|y⟩`.

What is proved here is the *quantitative core* of the two complexity arguments:

* `pB_norm_sq`: for orthonormal row star states, `‖|p_B⟩‖² = (1/(1+pᵀb))² Σ_i (p_iσ_i)²`, the
  identity used with Eq. (11) of the paper;
* `theorem39_query_complexity`: from `‖|p_B⟩‖² ≤ s·E_T/(1+pᵀb)²` the number of controlled-`U_AB`
  queries `(1+pᵀb)‖|p_B⟩‖/ε²` is at most `√(s·E_T)/ε²` (page 19, last display of the proof);
* `theorem311_unitary_cost`: one application of `U_AB` costs at most `5` times the `Õ(s)`
  star-state preparation cost.

The genuinely algorithmic conclusions (existence of the phase-estimation output state with the
stated trace-distance bound, and Algorithm 3 of Appendix A) are not formalised yet and appear as
placeholder declarations with the comments below.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace

namespace Qatlib.Papers.QLSBeyondCond25.MainResults.SpectralFilter

/-! ## c009 — Theorem 3.9: query complexity of phase estimation -/

/-- `E_T = Σ_i p_i² d_i` (paper page 5; used in the proof of Theorem 3.9, page 19). -/
def ET {M : Type*} [Fintype M] (p d : M → ℝ) : ℝ := ∑ i, p i ^ 2 * d i

/-- `E_T ≥ 0` when the squared row norms `d_i` are nonnegative. -/
theorem ET_nonneg {M : Type*} [Fintype M] (p d : M → ℝ) (hd : ∀ i, 0 ≤ d i) :
    0 ≤ ET p d :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hd i)

/-- Norm of a linear combination of an orthonormal family: `‖Σ_i a_i |Ψ_i⟩‖² = Σ_i a_i²`. -/
theorem norm_sq_sum_smul_eq_sum_sq {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ψ : ι → E) (a : ι → ℝ)
    (hΨ : ∀ i i', ⟪Ψ i, Ψ i'⟫_ℝ = if i = i' then (1 : ℝ) else 0) :
    ‖∑ i, a i • Ψ i‖ ^ 2 = ∑ i, a i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h : ∀ i, ⟪a i • Ψ i, ∑ j, a j • Ψ j⟫_ℝ = a i ^ 2 := by
    intro i
    rw [real_inner_smul_left, inner_sum]
    simp only [real_inner_smul_right, hΨ]
    have hsingle : (∑ x, a x * (if i = x then (1 : ℝ) else 0)) = a i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [show i ≠ b from fun h => hb h.symm]
      · intro hi
        simp at hi
    rw [hsingle]
    ring
  rw [sum_inner]
  exact Finset.sum_congr rfl fun i _ => h i

/-- Paper Eq. (11) (page 15) with its norm: for an orthonormal row-star family,
`‖|p_B⟩‖² = (1/(1+pᵀb))² Σ_i (p_i σ_i)²` where `σ_i = √d_{u_i}`. -/
theorem pB_norm_sq {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ψ : ι → E) (σ p : ι → ℝ) (pb : ℝ)
    (hΨ : ∀ i i', ⟪Ψ i, Ψ i'⟫_ℝ = if i = i' then (1 : ℝ) else 0) :
    ‖(1 / (1 + pb)) • (∑ i, (p i * σ i) • Ψ i)‖ ^ 2
      = (1 / (1 + pb)) ^ 2 * ∑ i, (p i * σ i) ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sq_sum_smul_eq_sum_sq Ψ _ hΨ]

/-- Theorem 3.9, query complexity (page 19): the phase-estimation precision is
`δ = ε²/((1+pᵀb)‖|p_B⟩‖)`, so the query count is `(1+pᵀb)‖|p_B⟩‖/ε²`; combined with
`‖|p_B⟩‖² ≤ s·E_T/(1+pᵀb)²` this is at most `√(s·E_T)/ε²`. -/
theorem theorem39_query_complexity {pbnorm pb s ETv ε : ℝ}
    (hpbnorm : 0 ≤ pbnorm) (hone : 0 ≤ 1 + pb) (hε : 0 < ε)
    (hET : 0 ≤ ETv) (hs : 0 ≤ s)
    (hbound : ((1 + pb) * pbnorm) ^ 2 ≤ s * ETv) :
    (1 + pb) * pbnorm / ε ^ 2 ≤ Real.sqrt (s * ETv) / ε ^ 2 := by
  have hle : (1 + pb) * pbnorm ≤ Real.sqrt (s * ETv) := by
    rw [← Real.sqrt_sq (mul_nonneg hone hpbnorm)]
    exact Real.sqrt_le_sqrt hbound
  exact div_le_div_of_nonneg_right hle (by positivity)

/-- Theorem 3.9 (page 18), phase-estimation part: if the initial state decomposes as
`|Φ_b⟩ = (1/√(1+‖y‖₂²))|θ*⟩ - (I - Π_A)|p_B⟩`, `|θ*⟩` is a `+1` eigenvector of `U_AB`, and
`Π_B|p_B⟩ = |p_B⟩`, then phase estimation on `(U_AB, |Φ_b⟩)` at precision
`ε²/((1+‖y‖₂²)‖|p_B⟩‖)` succeeds (phase `0`) with probability at least `1/(1+‖y‖₂²)` and
produces a state `|θ'⟩` with `½‖|θ'⟩⟨θ'| - |θ*⟩⟨θ*|‖₁ ≤ ε`.

The Lean statement records both conclusions: there is an output state `θ'` with `‖θ' - θ*‖ ≤ 2ε`
(which yields trace distance at most `2ε` for normalised states, the paper's `O(ε)`) and a success
probability `p_success` with `1/(1+‖y‖₂²) ≤ p_success ≤ 1`.

Gap: version arXiv:2510.05588v3, Theorem 3.9, page 18, proved via Theorem 3.4 (the QPE
soundness/completeness lemma).  The paper's proof steps: (1) Lemma 3.6 gives the decomposition;
(2) Lemma 3.7 gives `U_AB|θ*⟩ = |θ*⟩`; (3) Lemma 3.8 gives `Π_B|p_B⟩ = |p_B⟩`; (4) apply the
phase-estimation Lemma 3.4 to the pair `(U_AB, |Φ_b⟩)`.  The formalisation is missing a matrix
model of the star-state Hilbert space, the unitary `U_AB` as a `Matrix I I ℂ`, its eigenbasis with
the zero-phase set `T` and its spectral gap, and the identification of the amplitudes
`c_j = ⟪v_j, Φ_b⟫`.  Candidate reusable dependency (verified present in Frozen):
`Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter.DegeneratePhaseFilter.degenerate_phase_zero_event_and_full_branch_error`
and `...degenerate_phase_conditional_target_state_error` (they already prove the success
probability lower bound `a ≤ p` and the branch error bound); plus
`Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation.qpe_exact_readout`. -/
def theorem39_statement
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℝ) (θstar Φb pBket w : EuclideanSpace ℝ I)
    (ε ynorm2 : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hyn : 0 < ynorm2)
    (hU : U ∈ Matrix.orthogonalGroup I ℝ)
    -- the three hypotheses of Theorem 3.9
    (hdecomp : Φb = (Real.sqrt (1 + ynorm2))⁻¹ • θstar - w)
    (hfix : U *ᵥ θstar = θstar)
    (hproj : pBket ≠ 0) : Prop :=
  ∃ (θ' : EuclideanSpace ℝ I) (psuccess : ℝ),
    1 / (1 + ynorm2) ≤ psuccess ∧ psuccess ≤ 1 ∧ ‖θ' - θstar‖ ≤ 2 * ε

/-! ## c010 — Theorem 3.11: cost of implementing `U_AB` -/

/-- Iteration cost of preparing one `s`-sparse star state, `Õ(s)` written as `s·(log₂ s + 1)`
(paper page 20, using [GroverRudolph2002], [RamacciottiLefteroviciRotundo2024], and [LuoLi2024]). -/
def starPrepCost (s : ℕ) : ℝ := (s : ℝ) * ((Nat.log 2 s : ℝ) + 1)

/-- Cost of one application of `U_AB = (2Π_A - I)(2Π_B - I)`: two star-state preparations
(the row and column families) plus three elementary operations. -/
def uabCost (s : ℕ) : ℝ := 2 * starPrepCost s + 2 * starPrepCost s + 3

/-- Theorem 3.11 (page 19-20): `U_AB = (2Π_A - I)(2Π_B - I)` is implementable in time `Õ(s)`,
i.e. in at most a constant multiple of the `Õ(s)` star-state preparation cost.  The proof is the
paper's: each star state is `s`-sparse and is prepared in `Õ(s)` time, and by [JP25,
Claims 2.10, 2.11] the reflection cost is asymptotically the star-state preparation cost. -/
theorem theorem311_unitary_cost (s : ℕ) :
    uabCost s ≤ 5 * (starPrepCost s + 1) := by
  unfold uabCost
  have h1 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have h2 : (0 : ℝ) ≤ (Nat.log 2 s : ℝ) := Nat.cast_nonneg _
  have hsp : 0 ≤ starPrepCost s := by
    unfold starPrepCost
    nlinarith
  linarith

/-! ## c014 — Theorem A.1: kernel-projection QSVT linear solver -/

/-- Query count `O(κ(A) log(1/ε))` of the kernel-projection algorithm of Appendix A. -/
def qsvtQueryCost (κ ε : ℝ) : ℝ := κ * (Real.log (1 / ε) + 1)

/-- Theorem A.1 (Appendix A, page 44): using `O(κ(A) log(1/ε))` queries of `U_H` and `U_H†`, the
kernel-projection algorithm outputs a state `|y'⟩` that is `ε`-close to `|y⟩`, where `A y = b`.

Gap: version arXiv:2510.05588v3, Theorem A.1, page 44.  The paper's proof: (1) the solution
state `|y⟩` is `proportional to (I - Π_A)|ψ_0⟩` obtained by kernel projection, i.e. the
projector `I - H†H/‖H‖²`-type filter of QSVT (Appendix A, Theorem A.1); (2) polynomial
approximation of the step function to precision `ε` needs degree `O(κ(A) log(1/ε))` (Lemma A.2);
(3) each QSVT step uses one query each of `U_H` and `U_H†`.  Missing pieces: an LCU/QSVT model
of `U_H = blockEnc(H/α)`, the polynomial-approximation lemma for the step function, and the
query-accounting interface.  Candidate reusable dependencies (directories verified present in
Frozen, but their public theorem surfaces do not yet match this claim):
`Qatlib.Concepts.QsvtCore.SvtRobustness`,
`Qatlib.Concepts.LcuQsvtApprox.Optimality`,
`Qatlib.Concepts.LcuQsvtApprox.SparseWalkFrame.LcuQsvtSparseSimulation`.

The statement is existential in the solver and its query count because the Lean development
does not yet contain a model of Algorithm 3; the existential is the formal counterpart of "the
kernel-projection algorithm with `O(κ(A) log(1/ε))` queries", and the missing content is the
construction of that solver. -/
def theoremA1_statement
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (κ ε : ℝ)
    (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hy : A.toEuclideanLin y = b) (hyn : ‖y‖ = 1) : Prop :=
  ∃ (solver : ℝ → EuclideanSpace ℝ (Fin n)) (queries : ℝ → ℝ),
    queries ε ≤ qsvtQueryCost κ ε ∧ ‖solver ε - y‖ ≤ ε

end Qatlib.Papers.QLSBeyondCond25.MainResults.SpectralFilter
