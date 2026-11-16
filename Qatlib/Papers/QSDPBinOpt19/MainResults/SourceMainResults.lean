/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

namespace Qatlib.Papers.QSDPBinOpt19.MainResults

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `n` as a real number (the number of variables of the SDP). -/
def ncard (ι : Type*) [Fintype ι] : ℝ := (Fintype.card ι : ℝ)

/-- The uniform diagonal matrix `I/n`, the diagonal part of a feasible point of the
renormalized MaxQP SDP (3) (arXiv:1909.04613v3, eq. (3)). -/
def uniformDiag (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℝ :=
  Matrix.diagonal (fun _ => (ncard ι)⁻¹)

/-- Diagonal part of a matrix. -/
def diagPart (ρ : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => ρ i i)

/-- Feasibility for the renormalized MaxQP SDP (3): psd, trace one, diagonal `1/n`. -/
def RenormFeasible (ρ : Matrix ι ι ℝ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ ∀ i, ρ i i = (ncard ι)⁻¹

/-- Feasibility for the MaxQP SDP (2): psd, trace `n`, unit diagonal. -/
def MaxQPFeasible (X : Matrix ι ι ℝ) : Prop :=
  X.PosSemidef ∧ Matrix.trace X = ncard ι ∧ ∀ i, X i i = 1

/-- Optimal value of the renormalized MaxQP SDP (3), as a supremum of feasible values. -/
def renormValue (A : Matrix ι ι ℝ) : ℝ :=
  sSup {v : ℝ | ∃ ρ, RenormFeasible ρ ∧ v = Matrix.trace (A * ρ)}

/-- Optimal value of the MaxQP SDP (2). -/
def maxqpValue (A : Matrix ι ι ℝ) : ℝ :=
  sSup {v : ℝ | ∃ X, MaxQPFeasible X ∧ v = Matrix.trace (A * X)}

/-- A state that is an approximate solution of the renormalized MaxQP SDP with accuracy `δ`:
psd, trace one, diagonal `δ`-close in trace norm to `I/n`, and value `δ`-optimal. -/
def IsApproxSolution (A : Matrix ι ι ℝ) (δ : ℝ) (ρ : Matrix ι ι ℝ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
    Matrix.traceNorm (diagPart ρ - uniformDiag ι) ≤ δ ∧
    renormValue A - δ ≤ Matrix.trace (A * ρ)

/-- `n ρ` is `n ε`-close in trace distance to a feasible point of the MaxQP SDP (2). -/
def ScaledCloseToFeasible (ρ : Matrix ι ι ℝ) (ε : ℝ) : Prop :=
  ∃ X, MaxQPFeasible X ∧ Matrix.traceNorm ((ncard ι) • ρ - X) ≤ ncard ι * ε

/-- Additive value accuracy `err` of the scaled state `n ρ` for the MaxQP SDP (2). -/
def IsAdditiveOptimal (A : Matrix ι ι ℝ) (ρ : Matrix ι ι ℝ) (err : ℝ) : Prop :=
  |Matrix.trace (A * ((ncard ι) • ρ)) - maxqpValue A| ≤ err

/-- Column sparsity: at most `s` nonzero entries per column. -/
def ColumnSparse (A : Matrix ι ι ℝ) (s : ℕ) : Prop :=
  ∀ j, (Finset.univ.filter (fun i => A i j ≠ 0)).card ≤ s

/-- The Gibbs state `exp(-H)/tr(exp(-H))` of a Hamiltonian `H`. -/
def GibbsState (H : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ((Matrix.trace (NormedSpace.exp (-H)))⁻¹) • NormedSpace.exp (-H)

/-- A quantum solver for the MaxQP SDP: it produces a state, together with the guarantees of
Theorem I / Corollary 2.2 (approximate feasibility, scaled feasibility, value accuracy) and the
structural fact that its output is a Gibbs state of a Hamiltonian `a A + D`. -/
structure QuantumSolver (A : Matrix ι ι ℝ) where
  run : ℝ → ℝ
  output : ℝ → Matrix ι ι ℝ
  approx : ∀ ε : ℝ, 0 < ε → IsApproxSolution A (ε ^ 4) (output ε)
  scaled_close : ∀ ε : ℝ, 0 < ε → ScaledCloseToFeasible (output ε) ε
  value_accurate : ∀ ε : ℝ, 0 < ε → IsAdditiveOptimal A (output ε) (ncard ι * ‖A‖ * ε)
  gibbs_form : ∀ ε : ℝ, 0 < ε →
    ∃ (a : ℝ) (d : ι → ℝ), output ε = GibbsState (a • A + Matrix.diagonal d)

/-- A classical solver for the MaxQP SDP: it outputs a feasible point of (2) with value accuracy
`n ‖A‖ ε`. -/
structure ClassicalSolver (A : Matrix ι ι ℝ) where
  run : ℝ → ℝ
  output : ℝ → Matrix ι ι ℝ
  feasible : ∀ ε : ℝ, 0 < ε → MaxQPFeasible (ncard ι • output ε)
  value_accurate : ∀ ε : ℝ, 0 < ε → IsAdditiveOptimal A (output ε) (ncard ι * ‖A‖ * ε)

/-- Sign function with `sign 0 = 1`. -/
def realSign (x : ℝ) : ℝ := if x < 0 then -1 else 1

/-- The sign of a real number is `±1`. -/
theorem realSign_mem (x : ℝ) : realSign x = 1 ∨ realSign x = -1 := by
  unfold realSign
  split_ifs <;> simp

/-- The canonical i.i.d. standard Gaussian measure on `ι → ℝ`. -/
def standardGaussianMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)

end

end Qatlib.Papers.QSDPBinOpt19.MainResults

namespace Qatlib.Papers.QSDPBinOpt19.MainResults

section

/-- The product of standard real Gaussian laws is a probability measure. -/
instance standardGaussianMeasure_isProbability {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (standardGaussianMeasure ι) := by
  unfold standardGaussianMeasure
  infer_instance

end

end Qatlib.Papers.QSDPBinOpt19.MainResults

namespace Qatlib.Papers.QSDPBinOpt19.MainResults

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- One sample of the rounding: `(sign(S g))_i`. -/
def roundVector (S : Matrix ι ι ℝ) (g : ι → ℝ) : ι → ℝ :=
  fun i => realSign (∑ j, S j i * g j)

/-- Expected rounded quadratic form `E[∑_{ij} A_{ij} x_i x_j]`, `x = sign(S g)`. -/
def roundingValue (A : Matrix ι ι ℝ) (S : Matrix ι ι ℝ) : ℝ :=
  ∫ g : ι → ℝ, ∑ i, ∑ j, A i j * roundVector S g i * roundVector S g j
    ∂(standardGaussianMeasure ι)

/-- The symmetric block matrix `A' = [[0, A], [Aᵀ, 0]]` of Theorem II. -/
def blockMatrix (A : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks (0 : Matrix ι ι ℝ) A Aᴴ (0 : Matrix ι ι ℝ)

/-- Expected off-diagonal block value of the two-vector rounding of Theorem 3.1. -/
def pairValue (A : Matrix ι ι ℝ) (S : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : ℝ :=
  ∫ g : ι ⊕ ι → ℝ, ∑ i, ∑ j,
      A i j * roundVector S g (Sum.inl i) * roundVector S g (Sum.inr j)
    ∂(standardGaussianMeasure (ι ⊕ ι))

/-- The `∞→1` norm (`cut norm`) of `A`: supremum of `∑ A_{ij} x_i y_j` over sign vectors. -/
def cutNorm (A : Matrix ι ι ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x y : ι → ℝ,
    (∀ i, x i = 1 ∨ x i = -1) ∧ (∀ i, y i = 1 ∨ y i = -1) ∧
      v = ∑ i, ∑ j, A i j * x i * y j}

/-- The rounding ratio `γ = 2/π` if `A` is psd, `4/π - 1` otherwise (Theorem II). -/
def gamma (A : Matrix ι ι ℝ) : ℝ := by
  classical
  exact if A.PosSemidef then 2 / Real.pi else 4 / Real.pi - 1

/-- `H♯` encodes an approximately optimal solution of the renormalized MaxQP SDP (3) with
accuracy `ε⁴` for the block matrix `A'` (Theorem II). -/
def EncodesApproxOptimal (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (A : Matrix ι ι ℝ) (ε : ℝ) : Prop :=
  IsApproxSolution (blockMatrix A) (ε ^ 4) (GibbsState H)

/-- A rounding procedure: the sampled matrix `S` (columns are the vectors `v_i`) and its cost. -/
structure RoundingProcedure (ι : Type*) [Fintype ι] where
  S : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ
  cost : ℝ

/-- Abstract state of Algorithm 1: number of constraints, current state, the separation oracle
predicate, the infeasibility certificate, and the initialization `I/n`. -/
structure HUInstance (ι : Type*) [Fintype ι] [DecidableEq ι] where
  m : ℕ
  state : ℕ → Matrix ι ι ℝ
  sepOK : Matrix ι ι ℝ → Prop
  infeasible : Prop
  initial : state 0 = uniformDiag ι

/-- The iteration bound `T = ⌈64 log(n)/ε²⌉ + 1` of Theorem 2.1. -/
def huIterationBound (n : ℕ) (ε : ℝ) : ℕ := ⌈64 * Real.log (n : ℝ) / ε ^ 2⌉₊ + 1

/-- `α♯ = tr(A' ‖A'‖⁻¹ ρ♯)` (Proposition 2.1). -/
def alphaSharp (A : Matrix ι ι ℝ) (ρ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : ℝ :=
  Matrix.trace (((‖blockMatrix A‖)⁻¹ : ℝ) • (blockMatrix A * ρ))

/-- The relaxed value `α* = tr(A ρ)` (Proposition 3.2). -/
def alphaStar (A : Matrix ι ι ℝ) (ρ : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (A * ρ)

/-- Uniform diagonal `I/n` over `ℂ`. -/
def uniformDiagC (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℂ :=
  Matrix.diagonal (fun _ => ((ncard ι : ℝ) : ℂ)⁻¹)

/-- Diagonal part of a complex matrix. -/
def diagPartC (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ρ i i)

/-- The Gibbs state `exp(-H)/tr(exp(-H))` for a Hermitian complex Hamiltonian. -/
def GibbsStateC (H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((Matrix.trace (NormedSpace.exp (-H)))⁻¹) • NormedSpace.exp (-H)

/-- The truncated exponential `T_l = ∑_{k=0}^l (1/k!) (-H)^k` (Lemma 3.2). -/
def truncExpC (H : Matrix ι ι ℂ) (l : ℕ) : Matrix ι ι ℂ :=
  ∑ k ∈ Finset.range (l + 1), ((k.factorial : ℂ)⁻¹) • ((-H) ^ k)

/-- The truncated exponential `S_l = ∑_{k=0}^l (1/k!) (-H/2)^k` (Lemma 3.6). -/
def truncExp (H : Matrix ι ι ℝ) (l : ℕ) : Matrix ι ι ℝ :=
  ∑ k ∈ Finset.range (l + 1), ((k.factorial : ℝ)⁻¹) • ((-((2 : ℝ)⁻¹) • H) ^ k)

/-- Scaling factor `1/(n √x)` appearing in the diagonal renormalization of Lemma 3.5. -/
def normFactor (ι : Type*) [Fintype ι] (x : ℝ) : ℂ :=
  (((ncard ι) * Real.sqrt x : ℝ) : ℂ)⁻¹

/-- The renormalized correlation matrix `σ_{ij} = ρ_{ij}/(n √(ρ_{ii} ρ_{jj}))` of Lemma 3.5. -/
def normalizeCorrelation (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => (ncard ι : ℂ) * (normFactor ι (ρ i i).re * ρ i j * normFactor ι (ρ j j).re)

/-- The exceptional set `B = {i : |ρ_{ii} - 1/n| > ε²/n}` of Lemma 3.5. -/
def largeDeviationSet (ρ : Matrix ι ι ℂ) (ε : ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => |(ρ i i).re - (ncard ι)⁻¹| > ε ^ 2 / ncard ι)

/-- The complement submatrix `ρ_{B̄}` of Lemma 3.5. -/
def complSubmatrix (ρ : Matrix ι ι ℂ) (B : Finset ι) :
    Matrix {i // i ∉ B} {i // i ∉ B} ℂ :=
  ρ.submatrix Subtype.val Subtype.val

/-- `g` is a standard Gaussian vector under `μ`: its characteristic function is
`t ↦ exp(-‖t‖²/2)`.  This is the weakest standard hypothesis needed for the moment identities
used in Lemma 3.4. -/
def IsStandardGaussianVector {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Ω → ι → ℝ) : Prop :=
  ∀ t : ι → ℝ,
    (∫ ω, Complex.exp (Complex.I * (((∑ i, t i * g ω i : ℝ) : ℂ))) ∂μ) =
      Complex.exp (-(((∑ i, (t i) ^ 2 : ℝ) : ℂ)) / 2)

/-- An `ε`-separation oracle for the renormalized MaxQP SDP: two candidate separating matrices
`P_half`, `P_diag`; a zero matrix means the input passes the corresponding test. -/
def IsEpsilonSeparationOracle (A : Matrix ι ι ℝ) (ρ Phalf Pdiag : Matrix ι ι ℝ) (ε : ℝ) : Prop :=
  ((Phalf = 0 → renormValue A - ε ≤ Matrix.trace (A * ρ)) ∧
    (Phalf ≠ 0 → Matrix.trace (Phalf * (ρ - uniformDiag ι)) ≥ ε / 2)) ∧
  ((Pdiag = 0 → Matrix.traceNorm (diagPart ρ - uniformDiag ι) ≤ ε) ∧
    (Pdiag ≠ 0 → Matrix.trace (Pdiag * (ρ - uniformDiag ι)) ≥ ε / 2))

/-- A construction converting an approximate solution of (3) into a feasible point of (2)
(Proposition 3.1), with its runtime cost. -/
structure FeasibleConverter (ι : Type*) [Fintype ι] where
  toFeasible : Matrix ι ι ℝ → Matrix ι ι ℝ
  cost : ℝ

/-- Feasibility of the dual of the MaxQP SDP, in the form `y₀ I + diag(y) - B ⪰ 0`, `y ≥ 0`. -/
def DualFeasible (B : Matrix ι ι ℝ) (y : ι → ℝ) (y0 : ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (y0 • (1 : Matrix ι ι ℝ) + Matrix.diagonal y - B).PosSemidef

/-- `y` is a `δ`-optimal solution of the dual MaxQP SDP with objective value at most
`maxqpValue B + δ`. -/
def IsDeltaOptimalDual (B : Matrix ι ι ℝ) (y : ι → ℝ) (y0 : ℝ) (δ : ℝ) : Prop :=
  DualFeasible B y y0 ∧ ncard ι * y0 + ∑ i, y i ≤ maxqpValue B + δ

/-- Algebraic core of Lemma 3.4 (arXiv:1909.04613v3, eq. (23)): for any finite weighted family
of samples whose moments satisfy `E[X_u X_w] = c`, `E[X_u S_w] = E[S_u X_w] = c/√(π/2)` and
`E[S_u S_w] = s`, the identity
`(π/2) s = c + E[(X_u - √(π/2) S_u)(X_w - √(π/2) S_w)]` holds. -/
theorem lemma_3_4_moment_identity
    {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ)
    (Xu Xw Su Sw : Ω → ℝ) (c s : ℝ)
    (h1 : ∑ ω, μ ω * (Xu ω * Xw ω) = c)
    (h2 : Real.sqrt (Real.pi / 2) * (∑ ω, μ ω * (Su ω * Xw ω)) = c)
    (h3 : Real.sqrt (Real.pi / 2) * (∑ ω, μ ω * (Xu ω * Sw ω)) = c)
    (h4 : ∑ ω, μ ω * (Su ω * Sw ω) = s) :
    (Real.pi / 2) * s =
      c + ∑ ω, μ ω * ((Xu ω - Real.sqrt (Real.pi / 2) * Su ω) *
                        (Xw ω - Real.sqrt (Real.pi / 2) * Sw ω)) := by
  have hsq : Real.sqrt (Real.pi / 2) * Real.sqrt (Real.pi / 2) = Real.pi / 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_mul_self (by positivity)
  have hterm : ∀ ω : Ω,
      μ ω * ((Xu ω - Real.sqrt (Real.pi / 2) * Su ω) *
          (Xw ω - Real.sqrt (Real.pi / 2) * Sw ω)) =
        μ ω * (Xu ω * Xw ω)
          - Real.sqrt (Real.pi / 2) * (μ ω * (Su ω * Xw ω))
          - Real.sqrt (Real.pi / 2) * (μ ω * (Xu ω * Sw ω))
          + (Real.sqrt (Real.pi / 2) * Real.sqrt (Real.pi / 2)) *
              (μ ω * (Su ω * Sw ω)) := by
    intro ω
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [h1, h2, h3, h4, hsq]
  ring

/-- `ℓ₁` norm of a matrix (sum of absolute values of the entries). -/
def l1Norm (A : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, |A i j|

end

end Qatlib.Papers.QSDPBinOpt19.MainResults
