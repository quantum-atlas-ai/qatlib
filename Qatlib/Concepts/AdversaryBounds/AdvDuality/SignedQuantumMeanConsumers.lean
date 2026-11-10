/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix
open scoped Classical BigOperators
set_option warningAsError false
set_option autoImplicit false

theorem signedMean_hadamard_born (i : Bool) : BornProb (ApplyGate Hadamard (Ket false)) i=1/2 := by
  have hs : ApplyGate Hadamard (Ket false) i=((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [applyGate_eq_mulVec_ket, hadamard_apply_false]
  change ‖ApplyGate Hadamard (Ket false) i‖^2=1/2
  rw [hs, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2), inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

def signedOffsetPayoff : Bool → ℝ := fun b => if b then 101 else 99

def relativeHadamardPayoff : Bool → ℝ := fun b => if b then 2 else 0

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

theorem signed_offset_hadamard_access_ledger (k : ℕ) (x : Bool) :
    let q := (k+2)*(2*layerRepetitions k+1)
    signedMeanResources k Hadamard false x signedOffsetPayoff 1 =
      ⟨1,2*q,1+2*q,2*q*layerGrid k,2*q*(layerGrid k-1),2*q*(layerGrid k-1),
        1+2*q*(5*(layerGrid k-1)+3)⟩ :=
  signed_centered_full_resources k Hadamard false x signedOffsetPayoff 1

theorem signed_offset_hadamard_fresh_access_ledger (k r : ℕ) (x : Fin (2*r+1) → Bool) :
    let q := (k+2)*(2*layerRepetitions k+1)
    let m := 2*r+1
    signedMeanMedianResources k r Hadamard false x signedOffsetPayoff 1 =
      ⟨m,m*(2*q),m*(1+2*q),m*(2*q*layerGrid k),m*(2*q*(layerGrid k-1)),
        m*(2*q*(layerGrid k-1)),m*(1+2*q*(5*(layerGrid k-1)+3))⟩ :=
  signed_centered_fresh_full_resources k r Hadamard false x signedOffsetPayoff 1

theorem relative_variance_hadamard_access_ledger (k : ℕ) (ω : Fin 32 → Bool) :
    let q := (k+2)*(2*layerRepetitions k+1)
    relativeMeanResources 1 k Hadamard false relativeHadamardPayoff ω =
      ⟨32,q,32+q,q*layerGrid k,q*(layerGrid k-1),q*(layerGrid k-1),
        32+q*(5*(layerGrid k-1)+3)⟩ :=
  relative_variance_full_resources 1 k Hadamard false relativeHadamardPayoff ω
end Qatlib.Concepts.AdversaryBounds.AdvDuality
