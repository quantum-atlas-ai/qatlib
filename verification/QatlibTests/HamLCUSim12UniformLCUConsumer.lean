module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Papers.HamLCUSim12.FullSimulation.Figure3OutcomeUnique
public import Qatlib.Papers.HamLCUSim12.FullSimulation.RetryErrorBudget
public import Qatlib.Papers.HamLCUSim12.FullSimulation.UniformLCUFailure

@[expose] public section

/-!
# Concrete consumer for the uniform HamLCUSim12 LCU bounds

The examples instantiate the uniform failure bounds on the non-degenerate one-qubit
register `Fin 2` (`0 < 1`): the phase gate `S = diagonal ![1, I]` is at Euclidean
operator distance `√2 > 0` from the identity, and the antipodal pair `1, -1` is at
distance `2 > 0`. The corrected Lemma 2 failure bound is exercised in both
Euclidean operator-norm form and uniform state-action form. The retry budget theorem
and its real-power variant are instantiated on `Fin 4` at positive operator distance.
The Figure 3 uniqueness example uses Hadamard preparation and measurement gates, with
an explicit successful outcome.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.HamLCUSim12UniformLCUConsumer

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.LCUDeferred
open Qatlib.Papers.HamLCUSim12.FullSimulation
open scoped Matrix.Norms.L2Operator

/-- The one-qubit phase gate `S = diagonal ![1, I]`. -/
noncomputable def phaseGate : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal ![1, Complex.I]

/-- The phase gate is unitary. -/
private theorem phaseGate_mem_unitary :
    phaseGate ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGate, Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply]

/-- The identity on `Fin 2` is unitary. -/
private theorem one_mem_unitary :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp

/-- The negated identity on `Fin 2` is unitary. -/
private theorem negOne_mem_unitary :
    (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp

/-- The identity and its negation on `Fin 2` are at Euclidean operator distance `2`. -/
private theorem one_negOne_distance :
    ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) - (-1)‖ = 2 := by
  have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) - (-1) = (2 : ℂ) • 1 := by
    rw [sub_neg_eq_add]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]
  rw [h, norm_smul, CStarRing.norm_one, mul_one]
  norm_num

/-- `1 - S = diagonal ![0, 1 - I]` for the phase gate. -/
private theorem one_sub_phaseGate :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) - phaseGate
      = diagonal ((![0, 1 - Complex.I] : Fin 2 → ℂ)) := by
  rw [← Matrix.diagonal_one', phaseGate, Matrix.diagonal_sub]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The phase gate is at Euclidean operator distance exactly `√2` from the identity. -/
private theorem one_phaseGate_distance :
    ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) - phaseGate‖ = Real.sqrt 2 := by
  -- A diagonal matrix's Euclidean operator norm equals its largest diagonal magnitude.
  rw [one_sub_phaseGate, Matrix.l2_opNorm_diagonal]
  have hsq : ‖(1 : ℂ) - Complex.I‖ ^ 2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    norm_num [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  have hnorm : ‖((![0, 1 - Complex.I] : Fin 2 → ℂ))‖ = ‖(1 : ℂ) - Complex.I‖ := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro i
      fin_cases i
      · simp [Matrix.cons_val_zero]
      · simp [Matrix.cons_val_one]
    · have h1 := norm_le_pi_norm (f := ((![0, 1 - Complex.I] : Fin 2 → ℂ))) 1
      simpa using h1
  rw [hnorm]
  have hnonneg : 0 ≤ ‖(1 : ℂ) - Complex.I‖ := norm_nonneg _
  have : Real.sqrt 2 = ‖(1 : ℂ) - Complex.I‖ := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) hnonneg]
    exact hsq.symm
  rw [this]

/-- The register is non-degenerate: the identity and the phase gate are genuinely
`√2 > 0` apart, and the identity and its negation are `2 > 0` apart. -/
example : 0 < ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) - phaseGate‖
    ∧ 0 < ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) - (-1)‖ := by
  rw [one_phaseGate_distance, one_negOne_distance]
  exact ⟨by positivity, by norm_num⟩

/-- Uniform operator-norm failure bound on the one-qubit register, instantiated with the
antipodal pair `1, -1`: the corrected Lemma 2 circuit failure is at most one. -/
example (ψ : QState (Fin 2)) (hψ : Normalized ψ) :
    lemma2FailureProbCorrected 1 (1 : Matrix (Fin 2) (Fin 2) ℂ) (-1) ψ ≤ 1 := by
  obtain ⟨C, rfl, _, h⟩ := uniform_nqubit_lcu_failure_opNorm
  have hd := one_negOne_distance
  have hbound := h 1 (by norm_num) (1 : Matrix (Fin 2) (Fin 2) ℂ) (-1)
    one_mem_unitary negOne_mem_unitary 1 2 (by norm_num) (by norm_num)
    (by rw [hd])
  norm_num at hbound
  exact hbound ψ hψ

/-- Uniform state-action failure bound on the one-qubit register, instantiated with the
phase gate: every normalized state is moved by `1 - S` with squared norm at most `2`,
so the corrected Lemma 2 circuit failure is at most `1 / 2`. -/
example (ψ : QState (Fin 2)) (hψ : Normalized ψ) :
    lemma2FailureProbCorrected 1 (1 : Matrix (Fin 2) (Fin 2) ℂ) phaseGate ψ ≤ 1 / 2 := by
  obtain ⟨C, rfl, _, h⟩ := uniform_nqubit_lcu_failure_stateAction
  have hclose : ∀ φ : QState (Fin 2), Normalized φ →
      (∑ x : Fin 2, ‖(((1 : Matrix (Fin 2) (Fin 2) ℂ) - phaseGate) *ᵥ φ) x‖ ^ 2)
        ≤ (Real.sqrt 2) ^ 2 := by
    intro φ hφ
    rw [Real.sq_sqrt (by norm_num)]
    have hpoint : ∀ x : Fin 2,
        (((1 : Matrix (Fin 2) (Fin 2) ℂ) - phaseGate) *ᵥ φ) x
          = (if x = 1 then 1 - Complex.I else 0) * φ x := by
      intro x
      rw [one_sub_phaseGate, Matrix.mulVec_diagonal]
      fin_cases x <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Fin.sum_univ_two, hpoint 0, hpoint 1]
    have hcase0 : ‖(if (0 : Fin 2) = 1 then (1 - Complex.I) else 0) * φ 0‖ ^ 2 = 0 := by
      have h01 : ¬ ((0 : Fin 2) = 1) := by norm_num
      simp only [h01, ite_false, zero_mul, norm_zero,
        zero_pow (show (2 : ℕ) ≠ 0 by norm_num)]
    have hcase1 : ‖(if (1 : Fin 2) = 1 then (1 - Complex.I) else 0) * φ 1‖ ^ 2
        = 2 * ‖φ 1‖ ^ 2 := by
      simp only [ite_true]
      rw [norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      norm_num [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    rw [hcase0, hcase1, zero_add]
    have hφ' : ‖φ 0‖ ^ 2 + ‖φ 1‖ ^ 2 = 1 := by
      rw [← hφ, Fin.sum_univ_two]
    nlinarith [sq_nonneg (‖φ 0‖), sq_nonneg (‖φ 1‖)]
  have hbound := h 1 (by norm_num) (1 : Matrix (Fin 2) (Fin 2) ℂ) phaseGate
    one_mem_unitary phaseGate_mem_unitary 1 (Real.sqrt 2) (by norm_num)
    (Real.sqrt_nonneg 2) hclose
  have := hbound ψ hψ
  rw [Real.sq_sqrt (by norm_num)] at this
  convert this using 1
  norm_num

/-- With order index one and two repetitions, the powered budget and the operator
deficit both reach equality at error `5/16` on a two-qubit register. -/
example : 0 < ‖(5 / 16 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - 0‖ ∧
    ‖(5 / 16 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - 0‖ ≤ 5 / 16 := by
  obtain ⟨C, rfl, _, h⟩ := retry_error_budget
  have hdist : ‖(5 / 16 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - 0‖ = 5 / 16 := by
    norm_num [norm_smul, CStarRing.norm_one, Real.norm_eq_abs]
  refine ⟨by rw [hdist]; norm_num, ?_⟩
  exact h 1 2 1 (5 / 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((5 / 16 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) 0
    (by rw [hdist]; norm_num)

/-- The real-power budget with order index one and one repetition certifies the
positive deficit of the scaled identity on a two-qubit register. -/
example : 0 < ‖(5 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - 0‖ ∧
    ‖(5 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - 0‖ ≤ 5 := by
  obtain ⟨C, rfl, _, h⟩ := retry_error_budget_rpow
  have hdist : ‖(5 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - 0‖ = 5 := by
    norm_num [norm_smul, CStarRing.norm_one, Real.norm_eq_abs]
  refine ⟨by rw [hdist]; norm_num, ?_⟩
  exact h 1 1 1 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simp) ((5 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) 0 (by rw [hdist]; norm_num)

/-- With Hadamard preparation and measurement, outcome `false` realizes the constant
coefficient family at scale `1/2`. Outcome `true` cannot realize it at any nonzero scale. -/
example :
    (∀ m : Bool, Hadamard false m * Hadamard m false = (1 / 2 : ℂ)) ∧
    ∀ K : ℂ, K ≠ 0 → ¬ (∀ m : Bool, Hadamard true m * Hadamard m false = K) := by
  have hsuccess (m : Bool) : Hadamard false m * Hadamard m false = (1 / 2 : ℂ) := by
    have hscale : (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2) : ℂ)⁻¹ = 1 / 2 := by
      rw [← pow_two, inv_pow, sqrt2_sq, inv_eq_one_div]
    cases m <;> simpa [Hadamard] using hscale
  refine ⟨hsuccess, ?_⟩
  intro K hK hsecond
  exact figure3_success_outcome_unique Hadamard Hadamard hadamard_unitary
    false true false Bool.false_ne_true (fun _ => 1) (fun _ => one_ne_zero)
    (1 / 2) K hK (by simpa using hsuccess) (by simpa using hsecond)

end QatlibTests.HamLCUSim12UniformLCUConsumer
