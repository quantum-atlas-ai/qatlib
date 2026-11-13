/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean

/-!
# Hadamard examples of quantum mean estimation

This module specializes signed and relative-variance quantum mean estimators to the uniform
Boolean distribution prepared by a Hadamard gate. `signed_offset_hadamard_actual_consumer`
treats the payoff with values 99 and 101, while `relative_variance_hadamard_actual_consumer`
treats the payoff with values 0 and 2. These examples instantiate the bounded-variance and
relative-error mean-estimation settings of Theorems 5 and 6 in [Montanaro2015].

The access-ledger theorems compute the corresponding source preparations, layer copies,
measurements, forward and inverse accesses, queries, and gates.
`signed_offset_hadamard_fresh_access_ledger` also records the scaling for an odd number of fresh
repetitions.

## Main statements

* `signed_offset_hadamard_actual_consumer`: a mean-100, variance-one example.
* `relative_variance_hadamard_actual_consumer`: a nonnegative mean-one example.
* `signed_offset_hadamard_fresh_access_ledger`: resources for fresh repetitions.

## References

* [Montanaro, 2015][Montanaro2015], *Quantum speedup of Monte Carlo methods*.
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- Measuring the Hadamard image of `Ket false` gives each Boolean outcome probability `1 / 2`. -/
theorem signedMean_hadamard_born (i : Bool) : BornProb (ApplyGate Hadamard (Ket false)) i=1/2 := by
  have hs : ApplyGate Hadamard (Ket false) i=((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [applyGate_eq_mulVec_ket, hadamard_apply_false]
  change ‖ApplyGate Hadamard (Ket false) i‖^2=1/2
  rw [hs, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2), inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The Boolean payoff with value 99 at `false` and 101 at `true`. -/
def signedOffsetPayoff : Bool → ℝ := fun b => if b then 101 else 99

/-- The Boolean payoff with value zero at `false` and two at `true`. -/
def relativeHadamardPayoff : Bool → ℝ := fun b => if b then 2 else 0

/-- For `k ≥ 4`, the Hadamard payoff with values 99 and 101 has mean 100 and variance one, and
its signed mean estimate is within `8 * (1 / 2)^k` of 100 with probability at least `2 / 3`.
This is a concrete instance of the bounded-variance mean-estimation setting of Theorem 5 in
[Montanaro2015]. -/
theorem signed_offset_hadamard_actual_consumer (k : ℕ) (hk : 4 ≤ k) :
    let f : Bool → ℝ := fun b => if b then 101 else 99
    let σ : ℝ := 1
    (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i*f i)=100 ∧
      (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i*(f i-100)^2)=1 ∧
      (∑ ω with |signedMeanEstimate k f σ ω-100| ≤ 8*(1/2 : ℝ)^k,
        (signedMeanLaw k Hadamard false f σ hadamard_unitary).prob ω) ≥ 2/3 := by
  have hμ : (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i*signedOffsetPayoff i)=100 := by
    simp [signedMean_hadamard_born, signedOffsetPayoff]
    norm_num
  have hv : (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i*(signedOffsetPayoff i-100)^2)=1 := by
    simp [signedMean_hadamard_born, signedOffsetPayoff]
    norm_num
  refine ⟨hμ, hv, ?_⟩
  have hg := signed_centered_same_program_mean_guarantee Bool k Hadamard false signedOffsetPayoff 1
    hadamard_unitary hk (by norm_num)
  rw [hμ] at hg
  simpa only [mul_one] using! hg (by rw [hv]; norm_num)

/-- For `k ≥ 4` and the stated nonnegativity hypothesis, the Hadamard payoff with values zero
and two has mean one, and its relative mean estimate is within `3 * Real.sqrt 2 * (1 / 2)^k`
of one with probability at least `2 / 3`. This is a concrete instance of the relative-error
mean-estimation setting of Theorem 6 in [Montanaro2015]. -/
theorem relative_variance_hadamard_actual_consumer (k : ℕ)
    (hf : ∀ i : Bool, 0 ≤ (if i then 2 else 0 : ℝ)) (hk : 4 ≤ k) :
    let f : Bool → ℝ := fun i => if i then 2 else 0
    (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i*f i)=1 ∧
      (∑ ω with |relativeMeanEstimate 1 k f ω-1| ≤ 3*Real.sqrt 2*(1/2 : ℝ)^k,
        (relativeMeanLaw 1 k Hadamard false f hadamard_unitary hf).prob ω) ≥ 2/3 := by
  have hμ : (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i*relativeHadamardPayoff i)=1 := by
    simp [signedMean_hadamard_born, relativeHadamardPayoff]
  have hv : (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i*(relativeHadamardPayoff i-1)^2)=1 := by
    simp [signedMean_hadamard_born, relativeHadamardPayoff]
    norm_num
  refine ⟨hμ, ?_⟩
  have hg := relative_variance_actual_conditional_estimator Bool 1 k Hadamard false
    relativeHadamardPayoff hadamard_unitary hf (by norm_num) hk
  rw [hμ] at hg
  simpa only [Nat.cast_one, one_add_one_eq_two, mul_one] using!
    hg (by norm_num) (by rw [hv]; norm_num)

/-- The exact resource ledger of the signed Hadamard mean estimator, with one source preparation
and `2 * q` layer copies for `q = (k + 2) * (2 * layerRepetitions k + 1)`. The remaining
fields give its measurement, access, query, and gate counts. -/
theorem signed_offset_hadamard_access_ledger (k : ℕ) (x : Bool) :
    let q := (k+2)*(2*layerRepetitions k+1)
    signedMeanResources k Hadamard false x signedOffsetPayoff 1 =
      ⟨1,2*q,1+2*q,2*q*layerGrid k,2*q*(layerGrid k-1),2*q*(layerGrid k-1),
        1+2*q*(5*(layerGrid k-1)+3)⟩ :=
  signed_centered_full_resources k Hadamard false x signedOffsetPayoff 1

/-- The resource ledger for `2 * r + 1` fresh repetitions of the signed Hadamard mean estimator
is the single-run ledger multiplied componentwise by `2 * r + 1`. -/
theorem signed_offset_hadamard_fresh_access_ledger (k r : ℕ) (x : Fin (2*r+1) → Bool) :
    let q := (k+2)*(2*layerRepetitions k+1)
    let m := 2*r+1
    signedMeanMedianResources k r Hadamard false x signedOffsetPayoff 1 =
      ⟨m,m*(2*q),m*(1+2*q),m*(2*q*layerGrid k),m*(2*q*(layerGrid k-1)),
        m*(2*q*(layerGrid k-1)),m*(1+2*q*(5*(layerGrid k-1)+3))⟩ :=
  signed_centered_fresh_full_resources k r Hadamard false x signedOffsetPayoff 1

/-- The exact resource ledger of the relative-variance Hadamard mean estimator with parameter
one, including 32 source preparations and the stated layered measurement, access, query, and
gate counts. -/
theorem relative_variance_hadamard_access_ledger (k : ℕ) (ω : Fin 32 → Bool) :
    let q := (k+2)*(2*layerRepetitions k+1)
    relativeMeanResources 1 k Hadamard false relativeHadamardPayoff ω =
      ⟨32,q,32+q,q*layerGrid k,q*(layerGrid k-1),q*(layerGrid k-1),
        32+q*(5*(layerGrid k-1)+3)⟩ :=
  relative_variance_full_resources 1 k Hadamard false relativeHadamardPayoff ω
end Qatlib.Concepts.AdversaryBounds.AdvDuality
