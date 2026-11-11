/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper layer for *A New Quantum Algorithm for Linear Systems beyond the Condition Number*
(QLSBeyondCond25), fixed source version arXiv:2510.05588v3.

This file covers the headline algorithmic claims of the paper:

* c001, Theorem 1.1 (page 3): Algorithm 1 prepares `|y'⟩` with
  `½‖|y'⟩⟨y'| - |y⟩⟨y|‖₁ ≤ O(ε)` in time
  `Õ((1/‖y‖₂⁶ + ‖y‖₂²)·√(s³·E_T)/ε²)`;
* c002, Theorem 1.2 (page 4): for a quadratic polynomial system with a unique Boolean solution of
  Hamming weight `h`, Algorithm 2 recovers it with probability at least `1 - δ` in time
  `Õ(√E_T·log(1/δ))`;
* c003, Theorem 1.3 (page 4): for the planted MIS, if the independent-set counts satisfy
  `I_i = poly(n)·C(h,i)`, then `E_T` is poly-bounded and Algorithm 2 runs in polynomial time;
* c015, the welded-tree main result (page 5): `E_T, ‖p‖, s = O(1)` give `O(1/ε²)` time even though
  `κ(B)` is exponential.

The cost formulas are defined faithfully (`algorithmTime`, `ET`) and their arithmetic is proved
(`sqrt_cube_mul`, `gamma_bounds`, `ET_le_card_mul_of_term_bound`,
`theorem15_time_bound`).  The algorithm-level guarantees (state preparation, recovery probability,
and the instance-dependent `E_T` analysis) are recorded as placeholder statements with the paper's
proof route and the missing Lean ingredients documented on each declaration.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Qatlib.Papers.QLSBeyondCond25.MainResults.MainTheorems

/-! ## `E_T` and the runtime formula -/

/-- `E_T = Σ_i p_i²·d_i`, where `d_i` is the squared ℓ₂ norm of the `i`-th row of the augmented
matrix (paper page 3, Theorem 1.1). -/
def ET {M : Type*} [Fintype M] (p d : M → ℝ) : ℝ := ∑ i, p i ^ 2 * d i

/-- Runtime of Algorithm 1 (Theorem 1.1 page 3, Theorem 3.12 page 21):
`Õ((1/‖y‖₂⁶ + ‖y‖₂²)·√(s³·E_T)/ε²)`, written with `ynorm2 = ‖y‖₂²`, so `1/‖y‖₂⁶ = 1/ynorm2³`. -/
def algorithmTime (ynorm2 s ETv ε : ℝ) : ℝ :=
  (1 / ynorm2 ^ 3 + ynorm2) * Real.sqrt (s ^ 3 * ETv) / ε ^ 2

/-- `√(s³·E_T) = s·√(s·E_T)`: the `s³` form of Theorem 1.1 (page 3) equals the `s·√(s·E_T)` form
that arises from the phase-estimation query count of Theorem 3.9 (page 19). -/
theorem sqrt_cube_mul (s ETv : ℝ) (hs : 0 ≤ s) (hET : 0 ≤ ETv) :
    Real.sqrt (s ^ 3 * ETv) = s * Real.sqrt (s * ETv) := by
  have h : s ^ 3 * ETv = s ^ 2 * (s * ETv) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

/-- Theorem 3.12 (page 21): `γ = ‖y‖₂²/(1+‖y‖₂²)` lies in `[0,1)`. -/
theorem gamma_bounds (ynorm2 : ℝ) (h : 0 ≤ ynorm2) :
    0 ≤ ynorm2 / (1 + ynorm2) ∧ ynorm2 / (1 + ynorm2) < 1 := by
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]
    linarith

/-! ## c001 — Theorem 1.1 -/

/-- Trace distance `½‖ρ - σ‖₁` of two real density matrices, with the trace norm written as the sum
of the singular values (`LinearMap.singularValues`). -/
noncomputable def traceDistance {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (1 / 2) * ∑ i ∈ Finset.range d, (ρ - σ).toEuclideanLin.singularValues i

/-- The rank-one density matrix `|ψ⟩⟨ψ|`. -/
def rankOne {d : ℕ} (ψ : EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ψ i * ψ j

/-- Theorem 1.1 (page 3), *New QLS algorithm*: Algorithm 1 prepares a state `|y'⟩` whose trace
distance to `|y⟩` is `O(ε)` and whose runtime is at most
`(1/‖y‖₂⁶ + ‖y‖₂²)·√(s³·E_T)/ε²` (the `Õ` suppressing the `log` factors of Theorem 3.11/3.12).

Gap: version arXiv:2510.05588v3, Theorem 1.1, page 3; proof combines Theorem 3.9 (phase estimation
succeeds with probability at least `1/(1+‖y‖₂²)` and returns an `ε`-close state) with Theorem 3.12
(amplitude amplification with `γ = ‖y‖₂²/(1+‖y‖₂²)`, giving the time bound on page 21) and
Theorem 3.11 (`U_AB` in time `Õ(s)`, page 20).  Missing formal ingredients: a matrix model of
Algorithm 1 (star-state preparation, block encoding of `U_AB`, and the amplification step), and a
proof that trace distance is bounded by the state-preparation error.  The declaration below is
recorded as a `Prop`-valued definition rather than a theorem: the existential says that some
prepared state and runtime obey the displayed bounds, but nothing in the Lean development
constructs that state or proves that Algorithm 1 produces it.  Candidate reusable dependencies:
`QuantumAlgorithm.Concepts.SpectralFilter.ZeroPhaseFilter.DegeneratePhaseFilter.degenerate_phase_zero_event_and_full_branch_error`,
`QuantumAlgorithm.Concepts.LcuQsvtApprox.SparseWalkFrame.LcuQsvtSparseSimulation`,
`QuantumAlgorithm.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation.qpe_exact_readout`.
Suggested next tactic: instantiate `theorem311_unitary_cost` and `theorem39_query_complexity`
(this development) and close the trace-distance step with
`‖|ψ⟩⟨ψ| - |φ⟩⟨φ|‖₁ ≤ 2‖ψ - φ‖`. -/
def theorem11_guarantee
    {N : ℕ} (y : EuclideanSpace ℝ (Fin N)) (s ETv ε C : ℝ)
    (hε : 0 < ε) (hC : 0 < C) (hs : 0 ≤ s) (hET : 0 ≤ ETv) (hyn : 0 < ‖y‖) : Prop :=
  ∃ (ψ : EuclideanSpace ℝ (Fin N)) (time : ℝ),
    traceDistance (rankOne ψ) (rankOne y) ≤ C * ε ∧
      time ≤ algorithmTime (‖y‖ ^ 2) s ETv ε

/-! ## c002 — Theorem 1.2 -/

/-- Theorem 1.2 (page 4), *Quantum algorithm for multivariate polynomial systems*: for a system of
quadratic polynomials with a unique Boolean solution `s` of Hamming weight `h`, Algorithm 2 recovers
`s` with probability at least `1 - δ` in time `Õ(√E_T·log(1/δ))`, where `E_T` is computed with
respect to the weighted Boolean Macaulay linear system `AD z = b`.

Gap: version arXiv:2510.05588v3, Theorem 1.2, page 4.  The paper's route: (1) build the weighted
Boolean Macaulay linear system (`AD z = b`, Definition 5.4, page 28) with sparse `AD` and
`‖z‖ = √h` (page 28); (2) apply Theorem 1.1 with `‖z‖₂² = h` to prepare `|z⟩` in time
`Õ(√E_T/ε²)`; (3) recover `S` (hence `s`) from `O(log n + log(1/δ))` measurements of `|z⟩`
(Lemma 5.6); (4) set `ε = 1/poly(n)` so the measurement error does not change the support
condition `(h+1)/(2h) > 1/2`.  Missing formal ingredients: the Macaulay-matrix model of the
polynomial system, the link `D z = y` between the weighted and unweighted solutions, and the
probabilistic measurement pipeline of Lemma 5.6 (the union-bound and sample-count arithmetic of
that lemma are proved in `Section5/MeasurementRecovery.lean`).  Candidate reusable dependencies:
`QuantumAlgorithm.Concepts.QlsReadoutSpec.PseudoInverse.spectralSupport` and
`QuantumAlgorithm.Concepts.QlsReadoutSpec.PseudoInverse.leastSquares_minimum_residual_and_norm`.
Suggested next tactic: instantiate the recovery theorem
`lemma56_measurement_recovery` with the outcome distribution of `|z⟩` and telescope the
`h ≤ n` factor through `Real.sqrt`. -/
def theorem12_guarantee
    {n M : ℕ} (p d : Fin M → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : Prop :=
  ∃ (recovered : Fin n → Bool) (successProb time : ℝ),
    1 - δ ≤ successProb ∧ successProb ≤ 1 ∧
      time ≤ Real.sqrt (ET p d) * Real.log (1 / δ)

/-! ## c003 — Theorem 1.3 -/

/-- `E_T` is poly-bounded as soon as each summand is bounded by `P`: this is the elementary part of
the proof of Theorem 1.3 (page 4), where the hypothesis `I_i = poly(n)·C(h,i)` makes every term
`p_i²·d_i` polynomially bounded. -/
theorem ET_le_card_mul_of_term_bound {M : Type*} [Fintype M]
    (p d : M → ℝ) (P : ℝ) (hterm : ∀ i, p i ^ 2 * d i ≤ P) :
    ET p d ≤ (Fintype.card M : ℝ) * P := by
  unfold ET
  calc (∑ i, p i ^ 2 * d i) ≤ ∑ _i : M, P := Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card M : ℝ) * P := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Theorem 1.3 (page 4), *Polynomial-time quantum algorithm for the planted MIS*: if for every
`1 ≤ i ≤ h` the number of independent sets of size `i` satisfies `I_i = poly(n)·C(h,i)`, then the
parameter `E_T` of Algorithm 2 is bounded by `poly(n)`, and consequently Algorithm 2 recovers the
planted set `S` in polynomial time with high probability.

Gap: version arXiv:2510.05588v3, Theorem 1.3, page 4.  The paper's proof: the amplitudes of the
Macaulay system for the planted MIS are supported on the independent sets, and `I_i = poly(n)·C(h,i)`
bounds the row norms `d_i` and the coefficients `p_i` polynomially, so `E_T = Σ p_i² d_i = poly(n)`
(the elementary bound is `ET_le_card_mul_of_term_bound`); then Theorem 1.2 with `δ = 1/poly(n)`
recovers `S` in polynomial time.  Missing formal ingredients: the graph-theoretic encoding of the
planted MIS as a Boolean Macaulay system, the identification of the support with the independent
sets, and the polynomial bound on the resulting row norms.  Candidate reusable dependencies:
`QuantumAlgorithm.Concepts.QlsReadoutSpec.PseudoInverse.spectralSupport`.  Suggested next tactic:
derive `∀ i, p i ^ 2 * d i ≤ P` from `I_i = poly(n)·C(h,i)` by unfolding the star-state
normalisation `σ_i = √d_{u_i}` and apply `ET_le_card_mul_of_term_bound`. -/
theorem theorem13_planted_mis
    {M : ℕ} (p d : Fin M → ℝ) (P : ℝ) (hP : 0 < P)
    (hterm : ∀ i, p i ^ 2 * d i ≤ P) :
    ET p d ≤ (M : ℝ) * P := by
  simpa using ET_le_card_mul_of_term_bound p d P hterm

/-! ## c015 — welded-tree main result -/

/-- c015 (page 5), the O(1/ε²) runtime of the welded-tree example: when `s` and `E_T` are bounded by
constants `Cs`, `CE` and `‖y‖₂² ≥ 1`, the runtime formula of Theorem 1.1 is at most
`(ynorm2 + Cs)·√(Cs³·CE)/ε²` — in particular `O(1/ε²)`.

This is the provable cost half of the claim; the exponential lower bound on `κ(B)` is Proposition 5.7
(`proposition57_exponential_condition_number`). -/
theorem theorem15_time_bound (ynorm2 s ETv ε Cs CE : ℝ)
    (hyn : 1 ≤ ynorm2) (hs : 0 ≤ s) (hET : 0 ≤ ETv)
    (hsCs : s ≤ Cs) (hETCE : ETv ≤ CE) (hCs : 0 ≤ Cs) (hCs1 : 1 ≤ Cs) (hCE : 0 ≤ CE)
    (hε : 0 < ε) :
    algorithmTime ynorm2 s ETv ε ≤ (ynorm2 + Cs) * Real.sqrt (Cs ^ 3 * CE) / ε ^ 2 := by
  have hyn0 : (0 : ℝ) < ynorm2 := by linarith
  have hcoef : 1 / ynorm2 ^ 3 + ynorm2 ≤ ynorm2 + Cs := by
    have hinv : 1 / ynorm2 ^ 3 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have h3 : (1 : ℝ) ^ 3 ≤ ynorm2 ^ 3 := pow_le_pow_left₀ (by norm_num) hyn 3
      simpa using h3
    nlinarith
  have hsqrt : Real.sqrt (s ^ 3 * ETv) ≤ Real.sqrt (Cs ^ 3 * CE) := by
    apply Real.sqrt_le_sqrt
    have h1 : s ^ 3 ≤ Cs ^ 3 := by
      apply pow_le_pow_left₀ hs hsCs
    exact mul_le_mul h1 hETCE hET (by positivity)
  unfold algorithmTime
  have hden : (0 : ℝ) < ε ^ 2 := by positivity
  apply div_le_div_of_nonneg_right _ hden.le
  exact mul_le_mul hcoef hsqrt (Real.sqrt_nonneg _) (by linarith)

/-- c015 (page 5), *welded-tree main result*: for the welded-tree linear system the parameters are
`E_T = O(1)`, `‖p‖ = O(1)`, `s = O(1)`, and the algorithm runs in `O(1/ε²)` time while `κ(B)` is
`Ω(2^{n/2})`.

Gap: version arXiv:2510.05588v3, page 5 (welded-tree electrical flow).  The paper's argument uses
the structure of `b` (a single 1 and a single -1 for `s-t` electrical flow) to show `p_i` and `d_i`
are `O(1)` on the support, giving `E_T = O(1)`, `s = O(1)`, and then Theorem 1.1 gives `O(1/ε²)`;
the exponential `κ(B)` is Proposition 5.7 (proved in `Section5/ConditionNumber.lean` as a statement
with the arithmetic core `proposition57_lower_bound`).  The provable cost half is
`theorem15_time_bound`.  Missing formal ingredients: the welded-tree graph and its incidence matrix,
the `s-t` electrical-flow solution structure, and the row-norm bounds `d_i = O(1)`.  Suggested next
tactic: bound `(Fintype.card M : ℝ)` by the number of tree monomials and apply
`ET_le_card_mul_of_term_bound` with a constant `P`. -/
theorem theorem15_welded_tree_main
    {n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (s ETv ynorm2 : ℝ) (hs : 0 ≤ s) (hET : 0 ≤ ETv) (hyn : 1 ≤ ynorm2)
    (Cs CE : ℝ) (hsCs : s ≤ Cs) (hETCE : ETv ≤ CE) (hCs : 0 ≤ Cs) (hCs1 : 1 ≤ Cs)
    (hCE : 0 ≤ CE) :
    ∃ C : ℝ, 0 < C ∧ algorithmTime ynorm2 s ETv ε ≤ C / ε ^ 2 := by
  refine ⟨(ynorm2 + Cs) * (Real.sqrt (Cs ^ 3 * CE) + 1), ?_, ?_⟩
  · apply mul_pos (by linarith)
    have := Real.sqrt_nonneg (Cs ^ 3 * CE)
    linarith
  · have h := theorem15_time_bound ynorm2 s ETv ε Cs CE hyn hs hET hsCs hETCE hCs hCs1 hCE hε
    have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
    have hle : (ynorm2 + Cs) * Real.sqrt (Cs ^ 3 * CE) / ε ^ 2
        ≤ (ynorm2 + Cs) * (Real.sqrt (Cs ^ 3 * CE) + 1) / ε ^ 2 := by
      apply div_le_div_of_nonneg_right _ hε2.le
      have hs0 := Real.sqrt_nonneg (Cs ^ 3 * CE)
      have h1 : (0 : ℝ) ≤ ynorm2 + Cs := by linarith
      nlinarith
    linarith

end Qatlib.Papers.QLSBeyondCond25.MainResults.MainTheorems
