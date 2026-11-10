/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarPairWordSemanticsAmpl
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalTigh
set_option warningAsError false

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

theorem haar_pair_marked_eq (E : Finset I) :
    aqHaarPairMarked E = E ×ˢ (Finset.univ : Finset Bool) := by
  ext z
  simp [aqHaarPairMarked]

theorem haar_pair_marked_card (E : Finset I) : (aqHaarPairMarked E).card = 2 * E.card := by
  rw [haar_pair_marked_eq, Finset.card_product]
  simp [Nat.mul_comm]

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
