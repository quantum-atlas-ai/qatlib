/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.ThermalSourceMoments

/-!
# Prefix Identities for Thermal Source Paths

This module extends the one-step thermal source identities of [JiangEtAl2026] to finite path
prefixes. `pathKraus_snoc` and `pathInstrument_branch_snoc` describe appending an outcome, and
`pathBornLaw_snoc` factors an extended path probability through the conditional state of its
prefix.

The resulting identities recover prefix marginals, compute the next-index marginal, and express
centered operator moments without dividing by the prefix probability. They therefore also apply
to prefixes of zero probability, with the supplied reference states handling conditional-state
values there.

## Main statements

- `pathBornLaw_prefix_marginal` and `pathBornLaw_next_index` compute extension marginals.
* `pathBornLaw_centered_prefix` and `pathBornLaw_prefix_covariance` give probability-weighted
  centered moments.
- `pathBornLaw_centered_update` centers an arbitrary operator-valued update.
- `pathBornLaw_predictable_centered` permits a complex multiplier depending on the fixed prefix.

## References

* [Jiang et al., 2026][JiangEtAl2026], *Thermal-Drift Sampling: Generating Thermal Ensembles for
  Learning Many-Body Systems*.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix
open scoped BigOperators

/-- Appending an outcome to a path left-multiplies its ordered Kraus product by the new
outcome's Kraus operator. -/
theorem pathKraus_snoc {O : Type} {d : ℕ} (K : O → Qatlib.Foundations.PureStateMath.Operator d) (N : ℕ)
    (w : Fin N → O) (o : O) :
    pathKraus K (N + 1) (Fin.snoc w o) = K o * pathKraus K N w := by
  induction N with
  | zero => simp [pathKraus, Fin.snoc_zero]
  | succ N ih =>
    obtain ⟨first, tail, rfl⟩ := Fin.exists_cons w
    rw [← Fin.cons_snoc_eq_snoc_cons]
    change pathKraus K (N + 1) (Fin.snoc tail o) * K first =
      K o * (pathKraus K N tail * K first)
    rw [ih]
    exact Matrix.mul_assoc _ _ _

/-- The instrument branch for a path with one appended outcome applies the prefix branch first
and then the ideal one-step branch at the new outcome. -/
theorem pathInstrument_branch_snoc {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool)
    (o : Fin L × Bool) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    (pathInstrument F p a (N + 1)).branch (Fin.snoc w o) rho =
      (idealInstrument F p a).branch o ((pathInstrument F p a N).branch w rho) := by
  simp only [pathInstrument_branch, pathKraus_snoc, idealInstrument_branch,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The probability of an extended path is its prefix probability times the one-step Born
probability computed from the prefix's conditional density, for any reference-state family. -/
theorem pathBornLaw_snoc {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool)
    (o : Fin L × Bool) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d)
    (reference : (Fin N → Fin L × Bool) → Qatlib.Foundations.PureStateMath.DensityOperator d) :
    (pathBornLaw F p a (N + 1) rho).prob (Fin.snoc w o) =
      (pathBornLaw F p a N rho).prob w *
        (bornLaw F p a (pathBornState F p a N rho reference w)).prob o := by
  change Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb
      (pathInstrument F p a (N + 1)) rho.val (Fin.snoc w o) = _
  rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb, pathInstrument_branch_snoc,
      ← pathBornState_branch F p a N rho reference w]
  rw [map_smul, Matrix.trace_smul]
  change _ = _ * Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (idealInstrument F p a)
    (pathBornState F p a N rho reference w).val o
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- Summing all one-outcome extensions of a fixed prefix recovers that prefix's path
probability. -/
theorem pathBornLaw_prefix_marginal {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (reference : (Fin N → Fin L × Bool) → Qatlib.Foundations.PureStateMath.DensityOperator d) :
    ∑ o : Fin L × Bool, (pathBornLaw F p a (N + 1) rho).prob (Fin.snoc w o) =
      (pathBornLaw F p a N rho).prob w := by
  simp_rw [pathBornLaw_snoc F p a N w _ rho reference]
  rw [← Finset.mul_sum, (bornLaw F p a (pathBornState F p a N rho reference w)).sum_one, mul_one]

/-- Summing the two extensions with next index `j` gives the prefix probability times `p.prob
j`, including when the prefix has probability zero. -/
theorem pathBornLaw_next_index {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (reference : (Fin N → Fin L × Bool) → Qatlib.Foundations.PureStateMath.DensityOperator d)
    (j : Fin L) :
    ∑ b : Bool, (pathBornLaw F p a (N + 1) rho).prob (Fin.snoc w (j,b)) =
      (pathBornLaw F p a N rho).prob w * p.prob j := by
  simp_rw [pathBornLaw_snoc F p a N w _ rho reference]
  rw [← Finset.mul_sum, bornLaw_index]

/-- For a fixed thermal path prefix, summing the next signed increments centered by the
conditional state's `logDrift`, weighted by extended-path probabilities, gives the zero
operator. -/
theorem pathBornLaw_centered_prefix {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (tau : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (reference : (Fin N → Fin L × Bool) → Qatlib.Foundations.PureStateMath.DensityOperator d) :
    ∑ o : Fin L × Bool, ((pathBornLaw F p (Real.tanh (tau / 2)) (N + 1) rho).prob
      (Fin.snoc w o) : ℂ) •
        (logStep F tau o - logDrift F p tau
          (pathBornState F p (Real.tanh (tau / 2)) N rho reference w)) = 0 := by
  simp_rw [pathBornLaw_snoc F p (Real.tanh (tau / 2)) N w _ rho reference,
    Complex.ofReal_mul, ← smul_smul]
  rw [← Finset.smul_sum, bornLaw_centered_mean, smul_zero]

/-- For a fixed thermal prefix, the extended-path weighted square of the centered next increment
is the prefix probability times `tau^2*I - D*D`, where `D` is the drift at its conditional
state. -/
theorem pathBornLaw_prefix_covariance {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (tau : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (reference : (Fin N → Fin L × Bool) → Qatlib.Foundations.PureStateMath.DensityOperator d) :
    let D := logDrift F p tau (pathBornState F p (Real.tanh (tau / 2)) N rho reference w)
    ∑ o : Fin L × Bool, ((pathBornLaw F p (Real.tanh (tau / 2)) (N + 1) rho).prob
      (Fin.snoc w o) : ℂ) • ((logStep F tau o - D) * (logStep F tau o - D)) =
      ((pathBornLaw F p (Real.tanh (tau / 2)) N rho).prob w : ℂ) •
        (((tau ^ 2 : ℝ) : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) - D * D) := by
  (try dsimp only)
  simp_rw [pathBornLaw_snoc F p (Real.tanh (tau / 2)) N w _ rho reference,
    Complex.ofReal_mul, ← smul_smul]
  rw [← Finset.smul_sum, bornLaw_logStep_covariance]

/-- For any operator-valued update `G`, subtracting its mean under the prefix conditional
state's one-step Born law gives zero when summed against the extended-path probabilities. -/
theorem pathBornLaw_centered_update {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (reference : (Fin N → Fin L × Bool) → Qatlib.Foundations.PureStateMath.DensityOperator d)
    (G : (Fin L × Bool) → Qatlib.Foundations.PureStateMath.Operator d) :
    let q := bornLaw F p a (pathBornState F p a N rho reference w)
    ∑ o : Fin L × Bool, ((pathBornLaw F p a (N + 1) rho).prob (Fin.snoc w o) : ℂ) •
      (G o - ∑ v : Fin L × Bool, (q.prob v : ℂ) • G v) = 0 := by
  (try dsimp only)
  simp_rw [pathBornLaw_snoc F p a N w _ rho reference, Complex.ofReal_mul, ← smul_smul]
  rw [← Finset.smul_sum]
  have hm : (∑ o : Fin L × Bool,
      ((bornLaw F p a (pathBornState F p a N rho reference w)).prob o : ℂ) •
      (G o - ∑ v : Fin L × Bool,
        ((bornLaw F p a (pathBornState F p a N rho reference w)).prob v : ℂ) • G v)) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum,
      (bornLaw F p a (pathBornState F p a N rho reference w)).sum_one, Complex.ofReal_one, one_smul,
      sub_self]
  rw [hm, smul_zero]

/-- Multiplying the centered next thermal increment by any complex scalar depending on the fixed
prefix preserves its zero sum under the extended-path probabilities. -/
theorem pathBornLaw_predictable_centered {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (tau : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (reference : (Fin N → Fin L × Bool) → Qatlib.Foundations.PureStateMath.DensityOperator d)
    (predictable : (Fin N → Fin L × Bool) → ℂ) :
    ∑ o : Fin L × Bool, ((pathBornLaw F p (Real.tanh (tau / 2)) (N + 1) rho).prob
      (Fin.snoc w o) : ℂ) • (predictable w •
        (logStep F tau o - logDrift F p tau
          (pathBornState F p (Real.tanh (tau / 2)) N rho reference w))) = 0 := by
  simp only [smul_comm _ (predictable w)]
  rw [← Finset.smul_sum, pathBornLaw_centered_prefix, smul_zero]

end Qatlib.Papers.ThermalDrift26.ThermalSampling
