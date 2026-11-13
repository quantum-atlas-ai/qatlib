/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.VarianceScaling.MMDLoss
import Qatlib.Papers.Trainability23.HaarAverages.HaarMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Exponential Concentration of Single-Layer Haar-Random Born Models

This module formalizes Definition 1 (Eqs. (17)--(18)) and Proposition 2 (single-layer
tensor-product Haar family) of Rudolph et al., establishing exact first and second Haar
moments `2^{-n}` and `3^{-n}` and Chebyshev exponential concentration of Born-rule
circuit probabilities `q_θ(x)`.

## Main definitions

* `prodHaar`, `bitIdx`, `bornProb`: `n`-qubit product Haar measure and Born probability `q_V(x)`.
* `DetExpConcentrated`, `ProbExpConcentrated`: Definition 1 deterministic and probabilistic concentration.

## Main statements

* `chebyshev_two_moments`, `chebyshev_of_moments`: Chebyshev tail bounds from first and second moments.
* `proposition2_single_layer_concentration`: Proposition 2, tail bound `((1/3)^n - (1/4)^n) / δ^2`.
* `proposition2_exponential_concentration`: Proposition 2, uniform exponential concentration in `n`.
* `beta_pos`, `beta_nonneg`: positivity and nonnegativity of `(1/3)^n - (1/4)^n`.

## References

* [Rudolph et al., 2024][RudolphEtAl2024], Definition 1 and Proposition 2, pp. 9--10.
-/

set_option autoImplicit false

open Qatlib.Papers.Trainability23.VarianceScaling
open Qatlib.Papers.Trainability23.HaarAverages
open scoped BigOperators

namespace Qatlib.Papers.Trainability23.VarianceScaling.Concentration

noncomputable section

/-- Module-local measurable structure on the matrix algebra (`Matrix m n ℂ` is definitionally
`m → n → ℂ`); repeated from the Frozen Haar development, where it is file-local. -/
local instance instMeasurableSpaceMatrix (m n : Type*) :
    MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance instBorelSpaceMatrix (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

local instance instProbabilityHaar :
    MeasureTheory.IsProbabilityMeasure (haarUnitaryGroup (Fin 2)) :=
  ⟨haarUnitaryGroup_univ (Fin 2)⟩

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

local instance instProbabilityProdHaar (n : ℕ) :
    MeasureTheory.IsProbabilityMeasure (prodHaar n) :=
  MeasureTheory.Measure.pi.instIsProbabilityMeasure _

private theorem bornProbOne_memLp (j : Fin 2) :
    MeasureTheory.MemLp (fun V => bornProbOne V j) 2 (haarUnitaryGroup (Fin 2)) := by
  refine MeasureTheory.MemLp.of_bound
    ((continuous_unitaryEntry j 0).norm.pow 2).aestronglyMeasurable 1 ?_
  filter_upwards with V
  rw [bornProbOne, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_one₀ (norm_nonneg _) (unitaryGroup_entry_norm_le_one V.2 j 0)

private theorem integral_bornProbOne (j : Fin 2) :
    (∫ V, bornProbOne V j ∂haarUnitaryGroup (Fin 2)) = 1 / 2 := by
  fin_cases j
  · simpa [symMoment, bornProbOne] using symMoment_one.1
  · simpa [symMoment, bornProbOne] using symMoment_one.2

private theorem integral_bornProbOne_sq (j : Fin 2) :
    (∫ V, (bornProbOne V j) ^ 2 ∂haarUnitaryGroup (Fin 2)) = 1 / 3 := by
  fin_cases j
  · simpa [symMoment, bornProbOne, ← pow_mul] using symMoment_two.1
  · simpa [symMoment, bornProbOne, ← pow_mul] using symMoment_two.2.2

private theorem bornProb_memLp (n : ℕ) (x : Fin n → Bool) :
    MeasureTheory.MemLp (fun V => bornProb V x) 2 (prodHaar n) := by
  have hmeas : Measurable (fun V => bornProb V x) := by
    unfold bornProb bornProbOne
    exact Finset.measurable_prod Finset.univ fun i _ =>
      (((continuous_unitaryEntry (bitIdx (x i)) 0).norm.pow 2).measurable.comp
        (measurable_pi_apply i))
  apply (MeasureTheory.memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr
  simpa only [bornProb, prodHaar, ← Finset.prod_pow] using
    (MeasureTheory.Integrable.fintype_prod
      (fun i : Fin n => (bornProbOne_memLp (bitIdx (x i))).integrable_sq))

private theorem integral_bornProb (n : ℕ) (x : Fin n → Bool) :
    (∫ V, bornProb V x ∂prodHaar n) = (1 / 2 : ℝ) ^ n := by
  unfold bornProb prodHaar
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun i V => bornProbOne V (bitIdx (x i)))]
  simp only [integral_bornProbOne, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem integral_bornProb_sq (n : ℕ) (x : Fin n → Bool) :
    (∫ V, (bornProb V x) ^ 2 ∂prodHaar n) = (1 / 3 : ℝ) ^ n := by
  simp only [bornProb, prodHaar, ← Finset.prod_pow]
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun i V => (bornProbOne V (bitIdx (x i))) ^ 2)]
  simp only [integral_bornProbOne_sq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/- ## Definition 1: the two notions of exponential concentration -/

/-- **Definition 1, Eq. (17).**  `X` is *deterministically exponentially concentrated* in the
number of qubits towards `μ` if there are `b > 1` and `C > 0` with
`|Xₙ(α) − μₙ| ⩽ C · b⁻ⁿ` for every `n` and every parameter setting `α`. -/
def DetExpConcentrated {Ω : Type*} (X : ℕ → Ω → ℝ) (μ : ℕ → ℝ) : Prop :=
  ∃ b : ℝ, 1 < b ∧ ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ω : Ω), |X n ω - μ n| ≤ C * b ^ (-(n : ℤ))

/-- **Definition 1, Eq. (18).**  `X` is *probabilistically exponentially concentrated* if, for
every deviation `δ > 0`, `Pr[|Xₙ − μ| ≥ δ] ⩽ C · b⁻ⁿ / δ²` with `b > 1` and `C > 0` uniform in
`n` and `δ`.  The argument `Pr` is the tail probability of `Xₙ` as a function of `δ`. -/
def ProbExpConcentrated (Pr : ℕ → ℝ → ℝ) : Prop :=
  ∃ b : ℝ, 1 < b ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (δ : ℝ), 0 < δ → Pr n δ ≤ C * b ^ (-(n : ℤ)) / δ ^ 2

/- ## The Chebyshev engine behind Eq. (18) -/

/-- **Chebyshev's inequality**, as used to pass from a second moment to Eq. (18): for a
square-integrable real statistic on a probability space,
`μ{ω | δ ≤ |X ω − E X|} ⩽ Var(X)/δ²`.  This is Mathlib's
`ProbabilityTheory.meas_ge_le_variance_div_sq`, re-exported under the paper's name. -/
theorem chebyshev_two_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MeasureTheory.MemLp X 2 μ) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | δ ≤ |X ω - ∫ ω, X ω ∂μ|} ≤
      ENNReal.ofReal (ProbabilityTheory.variance X μ / δ ^ 2) :=
  ProbabilityTheory.meas_ge_le_variance_div_sq hX hδ

/-- **Chebyshev with explicit first and second moments.**  If `∫ X = m₁` and
`Var(X) = m₂ − m₁²`, then Eq. (18) holds with `β = m₂ − m₁²`. -/
theorem chebyshev_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MeasureTheory.MemLp X 2 μ) {δ m₁ m₂ : ℝ} (hδ : 0 < δ)
    (hmean : (∫ ω, X ω ∂μ) = m₁) (hvar : ProbabilityTheory.variance X μ = m₂ - m₁ ^ 2) :
    μ {ω | δ ≤ |X ω - m₁|} ≤ ENNReal.ofReal ((m₂ - m₁ ^ 2) / δ ^ 2) := by
  have h := chebyshev_two_moments (μ := μ) X hX hδ
  rw [hmean] at h
  rw [hvar] at h
  exact h

/- ## Proposition 2: concentration of the model probabilities -/

/-- **Proposition 2, single-layer family, Eq. (18).**  For the tensor-product ansatz of
independent single-qubit Haar unitaries, the Born probability of any fixed bitstring has mean
`2⁻ⁿ` and second moment `3⁻ⁿ` (one-qubit uniform `|U(x,0)|² ∼ Beta(1,1)` with
`E|U|² = 1/2`, `E|U|⁴ = 1/3`, multiplied over the `n` independent factors).  Chebyshev therefore
gives, for every `δ > 0`,
`Pr_V[ |q_V(x) − 2⁻ⁿ| ≥ δ ] ⩽ ((1/3)ⁿ − (1/4)ⁿ) / δ²`.

The deviation probability is the Haar product measure of the event. -/
theorem proposition2_single_layer_concentration (n : ℕ) (x : Fin n → Bool)
    (δ : ℝ) (hδ : 0 < δ) :
    prodHaar n {V | δ ≤ |bornProb V x - (1 / 2 : ℝ) ^ n|} ≤
      ENNReal.ofReal ((((1 / 3 : ℝ) ^ n) - ((1 / 4 : ℝ) ^ n)) / δ ^ 2) := by
  have hvar : ProbabilityTheory.variance (fun V => bornProb V x) (prodHaar n)
      = (1 / 3 : ℝ) ^ n - ((1 / 2 : ℝ) ^ n) ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub (bornProb_memLp n x), integral_bornProb]
    exact congrArg (fun a => a - ((1 / 2 : ℝ) ^ n) ^ 2) (integral_bornProb_sq n x)
  have h := chebyshev_of_moments (prodHaar n) (fun V => bornProb V x)
    (bornProb_memLp n x) hδ (integral_bornProb n x) hvar
  have hpow : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4 : ℝ) ^ n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rwa [hpow] at h

/-- **Proposition 2, uniform-in-`x` form.**  There is an exponentially small deviation profile
`C · b⁻ⁿ` valid simultaneously for every bitstring `x` and every deviation `δ > 0`; this is
Proposition 2 read through Definition 1 (Eq. (18)), with `b = 3` and `C = 1`. -/
theorem proposition2_exponential_concentration :
    ∃ b : ℝ, 1 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (x : Fin n → Bool) (δ : ℝ), 0 < δ →
        prodHaar n {V | δ ≤ |bornProb V x - (1 / 2 : ℝ) ^ n|}
          ≤ ENNReal.ofReal (C * b ^ (-(n : ℤ)) / δ ^ 2) := by
  refine ⟨3, by norm_num, 1, one_pos, ?_⟩
  intro n x δ hδ
  refine (proposition2_single_layer_concentration n x δ hδ).trans
    (ENNReal.ofReal_le_ofReal ?_)
  apply div_le_div_of_nonneg_right _ (sq_nonneg δ)
  rw [one_mul, zpow_neg, zpow_natCast, ← inv_pow, ← one_div]
  exact sub_le_self _ (by positivity)

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

/-
## `proposition2_gap` — proof route and current library gap

Fixed paper version: arXiv:2305.02881v2 (npj QI 2024, DOI 10.1038/s41534-024-00902-0),
Definition 1 Eqs. (17)–(18), p.~9; Proposition 2, p.~9 (discussion pp.~9–10).

Paper proof steps for the single-layer family: (i) `q_θ(x) = ∏ᵢ |(Uᵢ)ₓᵢ,0|²` factors over qubits
by Eq. (200); (ii) each single-qubit factor is uniform on `[0,1]` under the Haar measure
(`Beta(1,1)`), with first moment `1/2` and second moment `1/3`; (iii) independence gives
`E q = 2⁻ⁿ` and `E q² = 3⁻ⁿ`, hence `Var = 3⁻ⁿ − 4⁻ⁿ ∈ O(3⁻ⁿ)`; (iv) Chebyshev (Eq. (18)) yields
`Pr[|q − 2⁻ⁿ| ≥ δ] ⩽ (3⁻ⁿ − 4⁻ⁿ)/δ²`.  The other three bullets of Proposition 2 replace step
(ii)–(iii) by the second-moment property of a `k`-local 2-design / approximate 2-design, and by
the noise-induced depolarisation estimate; the final Chebyshev step is unchanged.

The single-layer family is proved here using `symMoment_one`, `symMoment_two`,
`MeasureTheory.integral_fintype_prod_eq_prod`, and `ProbabilityTheory.variance_eq_sub`.
The remaining model-side gap is the moment or depolarisation estimate for the other three
families in Proposition 2; their Chebyshev step can reuse `chebyshev_of_moments`.
-/

end

end Qatlib.Papers.Trainability23.VarianceScaling.Concentration
