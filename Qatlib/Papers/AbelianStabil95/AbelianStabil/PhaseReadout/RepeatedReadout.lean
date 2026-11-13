/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseHadamardTest
import Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout.HadamardWord

/-!
# Repeated phase samples with fresh controls

`runPhase` and `runDist` describe two blocks of Hadamard-test samples, at phases `φ` and `φ + 1
/ 4`. `freshControlState` realizes their product amplitudes with a common data state, and
`freshControl_controlLaw` identifies the control marginal with `eigenphaseSampleLaw` when the
data state is normalized. The development follows [Kitaev1995].

## Main statements

* `freshControl_controlLaw`: identifies the control sampling law.
* `repeatedQueryWord_counts`: computes `2 * s` queries and `4 * s` ordinary gates.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.KitaevReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators Classical

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Multiplication of `eigenPhase φ` by the imaginary unit shifts the phase by one quarter. -/
theorem i_mul_eigenPhase (φ : ℝ) :
    Complex.I * eigenPhase φ = eigenPhase (φ + 1 / 4) := by
  unfold eigenPhase
  have hcast : ((φ + 1 / 4 : ℝ) : ℂ) = (φ : ℂ) + 1 / 4 := by
    push_cast; norm_num
  rw [hcast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((φ : ℂ) + 1 / 4)
      = 2 * (Real.pi : ℂ) * Complex.I * (φ : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_add]
  have hhalf : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I]
    simp []
  rw [hhalf]
  ring

omit [DecidableEq I] in

/-- An eigenvector of `U` with phase `φ` is an eigenvector of `i • U` with phase `φ + 1 / 4`, as
used in [Kitaev1995]. -/
theorem iU_eigenvector (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hU : U *ᵥ ψ = eigenPhase φ • ψ) :
    ((Complex.I : ℂ) • U) *ᵥ ψ = eigenPhase (φ + 1 / 4) • ψ := by
  rw [Matrix.smul_mulVec, hU, smul_smul, i_mul_eigenPhase]

/-- The Hadamard query word for `i • U` preserves the eigenvector and produces the control state
and cosine probabilities at phase `φ + 1 / 4`, as used in [Kitaev1995]. -/
theorem iU_queryWord_eigenstate (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hU : U *ᵥ ψ = eigenPhase φ • ψ) :
    Run (eigenphaseControlledGate I ((Complex.I : ℂ) • U)) (hadamardQueryWord I)
        (TensorState ψ (Ket false)) =
      TensorState ψ (hadamardTestBitState (eigenPhase (φ + 1 / 4))) ∧
    BornProb (hadamardTestBitState (eigenPhase (φ + 1 / 4))) false =
      (1 + Real.cos (2 * Real.pi * (φ + 1 / 4))) / 2 ∧
    BornProb (hadamardTestBitState (eigenPhase (φ + 1 / 4))) true =
      (1 - Real.cos (2 * Real.pi * (φ + 1 / 4))) / 2 :=
  hadamardQueryWord_eigenstate I ((Complex.I : ℂ) • U) ψ (φ + 1 / 4)
    (iU_eigenvector U ψ φ hU)

/-- The phase factor for a run index: phase `φ` in the first `s` runs and phase `φ + 1 / 4` in
the next `s`. -/
def runPhase (φ : ℝ) (s : ℕ) (j : Fin (s + s)) : ℂ :=
  if (j : ℕ) < s then eigenPhase φ else eigenPhase (φ + 1 / 4)

/-- The Hadamard-bit distribution at phase `φ` for the first `s` runs and at phase `φ + 1 / 4`
for the next `s`. -/
def runDist (φ : ℝ) (s : ℕ) (j : Fin (s + s)) : FinDist Bool :=
  if (j : ℕ) < s then hadamardBitDist φ else hadamardBitDist (φ + 1 / 4)

/-- The probability of a bit under `runDist` equals its Born probability in the Hadamard-test
bit state specified by `runPhase`. -/
theorem runDist_prob (φ : ℝ) (s : ℕ) (j : Fin (s + s)) (b : Bool) :
    (runDist φ s j).prob b = BornProb (hadamardTestBitState (runPhase φ s j)) b := by
  unfold runDist runPhase
  split_ifs <;> rfl

/-- The data amplitudes multiplied by the product of the `2 * s` Hadamard-test control
amplitudes. -/
def freshControlState (ψ : QState I) (φ : ℝ) (s : ℕ) : QState (I × (Fin (s + s) → Bool)) :=
  fun p => ψ p.1 * ∏ j : Fin (s + s), hadamardTestBitState (runPhase φ s j) (p.2 j)

omit [Fintype I] [DecidableEq I] in

/-- The Born probability of a data index and control record factors into the data Born
probability and the product of the individual control Born probabilities, as used in
[Kitaev1995]. -/
theorem bornProb_freshControlState (ψ : QState I) (φ : ℝ) (s : ℕ)
    (i : I) (ω : Fin (s + s) → Bool) :
    BornProb (freshControlState ψ φ s) (i, ω)
      = BornProb ψ i * ∏ j, BornProb (hadamardTestBitState (runPhase φ s j)) (ω j) := by
  simp only [BornProb, freshControlState, norm_mul, mul_pow, norm_prod]
  have hsq : (∏ j : Fin (s + s),
        ‖hadamardTestBitState (runPhase φ s j) (ω j)‖) ^ 2
      = ∏ j : Fin (s + s),
        ‖hadamardTestBitState (runPhase φ s j) (ω j)‖ ^ 2 := by
    rw [pow_two, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => (pow_two _).symm
  rw [hsq]

/-- For a normalized data state, summing the joint Born probabilities over the data index yields
the probability of the control record under `eigenphaseSampleLaw`, as used in [Kitaev1995]. -/
theorem freshControl_controlLaw (ψ : QState I) (hψ : Normalized ψ) (φ : ℝ) (s : ℕ)
    (ω : Fin (s + s) → Bool) :
    (∑ i, BornProb (freshControlState ψ φ s) (i, ω))
      = (eigenphaseSampleLaw φ s).prob ω := by
  simp only [bornProb_freshControlState]
  rw [← Finset.sum_mul]
  have hnorm : (∑ i, BornProb ψ i) = 1 := hψ
  rw [hnorm, one_mul]
  have key : (eigenphaseSampleLaw φ s).prob ω
      = ∏ j, BornProb (hadamardTestBitState (runPhase φ s j)) (ω j) := by
    change (independentSampleLaw (runDist φ s)).prob ω = _
    unfold independentSampleLaw
    simp only [runDist_prob]
  rw [key]

/-- Repeating the one-query, two-gate Hadamard word `2 * s` times gives `2 * s` queries and `4 *
s` ordinary gates, as used in [Kitaev1995]. -/
theorem repeatedQueryWord_counts (s : ℕ) :
    2 * s * QueryCount (hadamardQueryWord I) = 2 * s ∧
    2 * s * GateCount (hadamardQueryWord I) = 4 * s := by
  obtain ⟨hq, hg⟩ := hadamardQueryWord_counts I
  rw [hq, hg]
  constructor <;> omega

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
