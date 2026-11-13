/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarPairWordSemanticsAmpl
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalTigh

/-!
# Amplitude identities for Haar pair readout

This module computes the action of a Hadamard on each Boolean pair after a phase query. Equal
input amplitudes within a pair cause the incorrect parity amplitude to vanish, and
`haar_marked_correct_mass` transfers all marked-pair mass to the correct orientation in the
setting of [Cornwell2014].

## Main statements

* `haar_wrong_amplitude`: When the two input amplitudes of a pair agree, a phase query followed
  by a Hadamard gives zero amplitude in the orientation opposite to the pair parity.
* `haar_pair_mass`: For equal input amplitudes within a pair, the correct parity outcome after
  the phase query and Hadamard has probability equal to the sum of the pair's input
  probabilities.
* `haar_marked_correct_mass`: If every marked pair has equal input amplitudes and the same
  parity b, the marked mass after phase querying and a Hadamard lies entirely in orientation b.

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Concepts.SearchStopping.KnownCount

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.GateCore

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.SearchStopping.KnownCount Qatlib.Concepts.SearchStopping.GateCore Matrix
open scoped Classical BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Applying the Hadamard on the Boolean register acts within each fixed pair-index fiber by the
two-term Hadamard sum. -/
theorem haar_pair_fiber (ψ : QState (I × Bool)) (i : I) (b : Bool) :
    (TensorGate (1 : Matrix I I ℂ) Hadamard *ᵥ ψ) (i,b) =
      ∑ c : Bool, Hadamard b c * ψ (i,c) := by
  simp only [Matrix.mulVec, dotProduct, TensorGate, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    rw [if_neg (fun h : i = x => hx h.symm)]
    simp
  · simp

/-- When the two input amplitudes of a pair agree, a phase query followed by a Hadamard gives
zero amplitude in the orientation opposite to the pair parity. -/
theorem haar_wrong_amplitude (ψ : QState (I × Bool)) (S : I × Bool → Bool)
    (i : I) (b : Bool) (heq : ψ (i,false) = ψ (i,true))
    (hb : (S (i,false) != S (i,true)) = b) :
    (TensorGate (1 : Matrix I I ℂ) Hadamard *ᵥ (PhaseOracle S *ᵥ ψ)) (i,!b) = 0 := by
  rw [haar_pair_fiber]
  simp only [Fintype.sum_bool]
  change Hadamard (!b) true * ApplyGate (PhaseOracle S) ψ (i,true) +
    Hadamard (!b) false * ApplyGate (PhaseOracle S) ψ (i,false) = 0
  rw [applyGate_phaseOracle, applyGate_phaseOracle]
  cases h0 : S (i,false) <;> cases h1 : S (i,true) <;> cases b <;>
    simp [h0,h1] at hb ⊢ <;> simp [Hadamard, heq]

/-- For equal input amplitudes within a pair, the correct parity outcome after the phase query
and Hadamard has probability equal to the sum of the pair's input probabilities. -/
theorem haar_pair_mass (ψ : QState (I × Bool)) (S : I × Bool → Bool)
    (i : I) (b : Bool) (heq : ψ (i,false) = ψ (i,true))
    (hb : (S (i,false) != S (i,true)) = b) :
    BornProb (TensorGate (1 : Matrix I I ℂ) Hadamard *ᵥ (PhaseOracle S *ᵥ ψ)) (i,b) =
      BornProb ψ (i,false) + BornProb ψ (i,true) := by
  let γ : QState Bool := fun c => ψ (i,c)
  let f : Bool → Bool := fun c => S (i,c)
  have hf (c : Bool) :
      (TensorGate (1 : Matrix I I ℂ) Hadamard *ᵥ (PhaseOracle S *ᵥ ψ)) (i,c) =
      (Hadamard *ᵥ (PhaseOracle f *ᵥ γ)) c := by
    rw [haar_pair_fiber]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro d _
    congr 1
    change ApplyGate (PhaseOracle S) ψ (i,d) = ApplyGate (PhaseOracle f) γ d
    simp only [applyGate_phaseOracle, f, γ]
  have hm := sum_normSq_mulVec_of_mem_unitaryGroup hadamard_unitary
    (PhaseOracle f *ᵥ γ)
  rw [sum_normSq_mulVec_of_mem_unitaryGroup (phaseOracle_unitary f) γ] at hm
  simp only [Complex.normSq_eq_norm_sq, Fintype.sum_bool, γ] at hm
  have hw := haar_wrong_amplitude ψ S i b heq hb
  unfold BornProb
  rw [hf b]
  cases b <;> simp only [Bool.not_false, Bool.not_true] at hw
  · rw [hf true] at hw
    rw [hw] at hm
    simpa [γ, add_comm] using hm
  · rw [hf false] at hw
    rw [hw] at hm
    simpa [γ, add_comm] using hm

/-- The marked pair set is the Cartesian product of E with all Boolean orientations. -/
theorem haar_pair_marked_eq (E : Finset I) :
    aqHaarPairMarked E = E ×ˢ (Finset.univ : Finset Bool) := by
  ext z
  simp [aqHaarPairMarked]

/-- The marked pair set has cardinality twice the cardinality of E. -/
theorem haar_pair_marked_card (E : Finset I) : (aqHaarPairMarked E).card = 2 * E.card := by
  rw [haar_pair_marked_eq, Finset.card_product]
  simp [Nat.mul_comm]

/-- If every marked pair has equal input amplitudes and the same parity b, the marked mass after
phase querying and a Hadamard lies entirely in orientation b. -/
theorem haar_marked_correct_mass (ψ : QState (I × Bool)) (E : Finset I)
    (S : I × Bool → Bool) (b : Bool)
    (heq : ∀ i ∈ E, ψ (i,false) = ψ (i,true))
    (hb : ∀ i ∈ E, (S (i,false) != S (i,true)) = b) :
    MeasureProb (TensorGate (1 : Matrix I I ℂ) Hadamard *ᵥ (PhaseOracle S *ᵥ ψ))
      (Finset.univ.filter fun z => z.1 ∈ E ∧ z.2 = b) =
      MeasureProb ψ (aqHaarPairMarked E) := by
  have hs : (Finset.univ.filter fun z : I × Bool => z.1 ∈ E ∧ z.2 = b) =
      E ×ˢ ({b} : Finset Bool) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
  rw [hs, haar_pair_marked_eq]
  simp only [MeasureProb, Finset.sum_product, Finset.sum_singleton,
    Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [add_comm] using haar_pair_mass ψ S i b (heq i hi) (hb i hi)

end Qatlib.Concepts.AmpTransform.HaarPairTest
