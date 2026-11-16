/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Trainability23.HaarAverages.HaarMeasure
public import Qatlib.Papers.Trainability23.VarianceScaling.Concentration.SourceModelConcentration
public import Qatlib.Papers.Trainability23.VarianceScaling.MMDLoss
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Constructions.Pi
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


/-!
# Concentration source results

These finite probability identities and conditional estimates preserve closed
results from arXiv:2305.02881v2. They do not assert the missing full Haar-product
MMD variance identity or an unconditional trainability theorem.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.Trainability23.VarianceScaling
open Qatlib.Papers.Trainability23.HaarAverages
open scoped BigOperators Matrix
namespace Qatlib.Papers.Trainability23.VarianceScaling.Concentration

open Qatlib.Papers.Trainability23.VarianceScaling.Concentration

/-

/-- Module-local measurable structure on the matrix algebra (`Matrix m n ℂ` is definitionally
`m → n → ℂ`); repeated from the Frozen Haar development, where it is file-local. -/
local instance instMeasMatrix (m n : Type*) :
    MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

/-- The law of the tensor-product ansatz `U = ⊗ᵢ Uᵢ(θᵢ)` with single-qubit Haar-random factors:
the `n`-fold product of `haarUnitaryGroup (Fin 2)`. -/
def prodHaar (n : ℕ) : MeasureTheory.Measure (Fin n → Matrix.unitaryGroup (Fin 2) ℂ) :=
  MeasureTheory.Measure.pi fun _ => haarUnitaryGroup (Fin 2)

/-- The computational-basis index of a bit. -/
def bitIdx (b : Bool) : Fin 2 := if b then 1 else 0

/-- The tensor-product model probability `q_θ(x) = ∏ᵢ |Uᵢ(xᵢ, 0)|²` of the Born-rule model
(Eqs. (199)–(204)). -/
def bornProb {n : ℕ} (V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ) (x : Fin n → Bool) : ℝ :=
  ∏ i, bornProbOne (V i) (bitIdx (x i))

 -/
/-! ## Definition 1: the two notions of exponential concentration -/

/-- **Definition 1, Eq. (17).**  `X` is *deterministically exponentially concentrated* in the
number of qubits towards `μ` if there are `b > 1` and `C > 0` with
`|Xₙ(α) − μₙ| ⩽ C · b⁻ⁿ` for every `n` and every parameter setting `α`. -/
def DetExpConc {Ω : Type*} (X : ℕ → Ω → ℝ) (μ : ℕ → ℝ) : Prop :=
  ∃ b : ℝ, 1 < b ∧ ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ω : Ω), |X n ω - μ n| ≤ C * b ^ (-(n : ℤ))

/-- **Definition 1, Eq. (18).**  `X` is *probabilistically exponentially concentrated* if, for
every deviation `δ > 0`, `Pr[|Xₙ − μ| ≥ δ] ⩽ C · b⁻ⁿ / δ²` with `b > 1` and `C > 0` uniform in
`n` and `δ`.  The argument `Pr` is the tail probability of `Xₙ` as a function of `δ`. -/
def ProbExpConc (Pr : ℕ → ℝ → ℝ) : Prop :=
  ∃ b : ℝ, 1 < b ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (δ : ℝ), 0 < δ → Pr n δ ≤ C * b ^ (-(n : ℤ)) / δ ^ 2

/-! ## The Chebyshev engine behind Eq. (18) -/

/-- **Chebyshev's inequality**, as used to pass from a second moment to Eq. (18): for a
square-integrable real statistic on a probability space,
`μ{ω | δ ≤ |X ω − E X|} ⩽ Var(X)/δ²`.  This is Mathlib's
`ProbabilityTheory.meas_ge_le_variance_div_sq`, re-exported under the paper's name. -/
theorem chebyshev {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MeasureTheory.MemLp X 2 μ) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | δ ≤ |X ω - ∫ ω, X ω ∂μ|} ≤
      ENNReal.ofReal (ProbabilityTheory.variance X μ / δ ^ 2) :=
  ProbabilityTheory.meas_ge_le_variance_div_sq hX hδ

/-- **Chebyshev with explicit first and second moments.**  If `∫ X = m₁` and
`Var(X) = m₂ − m₁²`, then Eq. (18) holds with `β = m₂ − m₁²`. -/
theorem cheb_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MeasureTheory.MemLp X 2 μ) {δ m₁ m₂ : ℝ} (hδ : 0 < δ)
    (hmean : (∫ ω, X ω ∂μ) = m₁) (hvar : ProbabilityTheory.variance X μ = m₂ - m₁ ^ 2) :
    μ {ω | δ ≤ |X ω - m₁|} ≤ ENNReal.ofReal ((m₂ - m₁ ^ 2) / δ ^ 2) := by
  have h := chebyshev (μ := μ) X hX hδ
  rw [hmean] at h
  rw [hvar] at h
  exact h

/-
/-! ## Proposition 2: concentration of the model probabilities -/

/-- **The deviation profile is positive:** `(1/4)ⁿ < (1/3)ⁿ` for `n ≥ 1`, so the variance
`(1/3)ⁿ − (1/4)ⁿ` appearing in Proposition 2 is strictly positive (the model really does
fluctuate) — the arithmetic side-check of Eq. (18). -/
theorem beta_pos (n : ℕ) (hn : 1 ≤ n) : 0 < (1 / 3 : ℝ) ^ n - (1 / 4 : ℝ) ^ n := by
  have h : (1 / 4 : ℝ) ^ n < (1 / 3 : ℝ) ^ n :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  linarith

/-- The deviation profile is nonnegative for every `n`. -/
theorem beta_nonneg (n : ℕ) : 0 ≤ (1 / 3 : ℝ) ^ n - (1 / 4 : ℝ) ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; norm_num
  · exact (beta_pos n hn).le
-/


end Qatlib.Papers.Trainability23.VarianceScaling.Concentration
