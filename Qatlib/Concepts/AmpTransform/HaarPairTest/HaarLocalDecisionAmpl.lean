/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarLocalDecisionStat
import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarPairAmplitude

/-!
# Local decision by amplified Haar pairs

`haarLocalDecision` proves the circuit validity, resource counts, and orientation success bounds
for amplified Haar pairs. A common marked-pair parity determines the successful orientation, as
in the amplified Haar-transform analysis of [Cornwell2014].

## Main statements

* `haarLocalDecision`: Proves the local Haar-pair decision contract, including exact circuit
  counts, marked correct-orientation mass, a success lower bound of 1−M/|I|, and a 2/3 bound
  when 3M ≤ |I|; see [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.GateCore

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.SearchStopping.KnownCount Qatlib.Concepts.SearchStopping.GateCore Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators

/-- Proves the local Haar-pair decision contract, including exact circuit counts, marked
correct-orientation mass, a success lower bound of 1−M/|I|, and a 2/3 bound when 3M ≤ |I|;
see [Cornwell2014]. -/
theorem haarLocalDecision : HaarLocalDecision := by
  intro I _ _ hN T' seed hT hprep M θ hθpos hθπ hθ
  let k := Nat.floor (Real.pi / (4 * θ))
  have hw := haarPairWordSemantics I T' seed hT hprep k
  refine ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, ?_⟩
  intro E hE S b hb
  have hNpair : 0 < Fintype.card (I × Bool) := by
    simp only [Fintype.card_prod, Fintype.card_bool]
    omega
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hangle : Real.sin θ ^ 2 =
      ((aqHaarPairMarked E).card : ℝ) / (Fintype.card (I × Bool) : ℝ) := by
    rw [haar_pair_marked_card, hE, Fintype.card_prod, Fintype.card_bool]
    push_cast
    rw [hθ]
    field_simp
  have hpairAndProb :
      (∀ i ∈ E, GroverState (aqHaarPairMarked E) k (i,false) =
        GroverState (aqHaarPairMarked E) k (i,true)) ∧
      MeasureProb (GroverState (aqHaarPairMarked E) k) (aqHaarPairMarked E) =
        Real.sin (((2*k+1 : ℕ) : ℝ)*θ)^2 := by
    rcases lt_or_eq_of_le hθπ with hlt | hfull
    · have hs : Real.sin θ ≠ 0 :=
        (Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [Real.pi_pos])).ne'
      have hc : Real.cos θ ≠ 0 :=
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩).ne'
      constructor
      · intro i hi
        rw [groverState_eq hNpair _ θ hangle hs hc]
        simp [MarkedVector, aqHaarPairMarked, hi]
      · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
          measureProb_groverState hNpair (aqHaarPairMarked E) θ hangle hs hc k
    · have hk : k = 0 := by
        have hr : Real.pi / (4*(Real.pi/2)) = (1/2 : ℝ) := by
          field_simp
          ring
        norm_num [k, hfull, hr]
      have hm : (M : ℝ) = (Fintype.card I : ℝ) := by
        have hd : (M : ℝ) / (Fintype.card I : ℝ) = 1 := by
          rw [← hθ, hfull, Real.sin_pi_div_two]
          norm_num
        exact (div_eq_one_iff_eq hn).mp hd
      have hmNat : M = Fintype.card I := by exact_mod_cast hm
      have he : E = Finset.univ := Finset.eq_univ_of_card E (hE.trans hmNat)
      have ha : aqHaarPairMarked E = Finset.univ := by simp [he, aqHaarPairMarked]
      constructor
      · intro i _
        simp [hk, GroverState, GroverCircuit, RepeatCircuit, Uniform]
      · simp only [hk, GroverState, GroverCircuit, RepeatCircuit, Run]
        rw [ha, measureProb_univ (normalized_uniform hNpair)]
        simp [hfull, Real.sin_pi_div_two]
  have hexact : MeasureProb (aqHaarPairOutput T' seed k E S)
      (Finset.univ.filter fun z => z.1 ∈ E ∧ z.2 = b) =
      Real.sin (((2*k+1 : ℕ) : ℝ)*θ)^2 := by
    rw [(hw.2.2.2.2 E S).1]
    exact (haar_marked_correct_mass _ E S b hpairAndProb.1 hb).trans hpairAndProb.2
  have hsub : (Finset.univ.filter fun z : I × Bool => z.1 ∈ E ∧ z.2 = b) ⊆
      (Finset.univ.filter fun z => z.2 = b) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hz.2
  have hmono : MeasureProb (aqHaarPairOutput T' seed k E S)
      (Finset.univ.filter fun z => z.1 ∈ E ∧ z.2 = b) ≤
      MeasureProb (aqHaarPairOutput T' seed k E S)
      (Finset.univ.filter fun z => z.2 = b) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => bornProb_nonneg _ z)
  have hsuccess : 1 - (M : ℝ)/(Fintype.card I : ℝ) ≤
      Real.sin (((2*k+1 : ℕ) : ℝ)*θ)^2 := by
    rw [← hθ]
    simpa only [k, groverIterations, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using groverIterations_success hθpos hθπ
  have hlower := hsuccess.trans (hexact ▸ hmono)
  refine ⟨hexact, hlower, ?_⟩
  intro hsparse
  have hsparseReal : 3 * (M : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast hsparse
  have hratio : (M : ℝ)/(Fintype.card I : ℝ) ≤ (1/3 : ℝ) := by
    apply (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < Fintype.card I)).mpr
    linarith
  linarith

end Qatlib.Concepts.AmpTransform.HaarPairTest
