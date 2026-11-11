/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartExpectedReceiptTigh
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-!
# Verified classical search retries

This module identifies zero iteration Grover sampling with uniform classical sampling and
charges one Boolean oracle query for verification. The theorem `classical_verified_retry`
derives the first success law, almost sure termination, and expected query cost for the high
density search regime discussed in [BoyerEtAl1998].

## Main statements

* `classical_verified_retry`: Gives the geometric first success law and expected query cost.
* `classical_verified_kernel`: Identifies one verified trial with uniform sampling followed by a
  membership check.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false

set_option autoImplicit false
open scoped Classical BigOperators ENNReal
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Papers.QSearchBoyer98.MainResults

noncomputable section
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

omit [Nonempty I] in

/-- The marked mass of the initial Grover state is the marked fraction |A|/|I|. -/
theorem zero_grover_mass (A : Finset I) :
    MeasureProb (GroverState A 0) A = (A.card:ℝ)/(Fintype.card I:ℝ) := by
  simpa only [GroverState,GroverCircuit,RepeatCircuit,Run] using measureProb_uniform A

omit [Nonempty I] in

/-- Every address has Born probability 1/|I| before any Grover iterations. -/
theorem zero_grover_born (A : Finset I) (i : I) :
    BornProb (GroverState A 0) i = 1/(Fintype.card I:ℝ) := by
  have h := measureProb_uniform ({i}:Finset I)
  simpa only [GroverState,GroverCircuit,RepeatCircuit,Run,MeasureProb,
    Finset.sum_singleton,Finset.card_singleton,Nat.cast_one] using h

/-- The zero iteration search circuit with identity preparation is unitary and uses no oracle
queries. -/
theorem classical_uniform_word :
    IsUnitaryCircuit (bbhtBitSearchCircuit (1:Matrix I I ℂ) (Uniform I) 0) ∧
    QueryCount (bbhtBitSearchCircuit (1:Matrix I I ℂ) (Uniform I) 0) = 0 := by
  have h := actualRestartSearchWord I Fintype.card_pos (1:Matrix I I ℂ) (Uniform I)
    (Submonoid.one_mem _) (normalized_uniform Fintype.card_pos) (by simp) (∅:Finset I) 0
  exact ⟨h.1,h.2.1⟩

/-- The restart transition for uniform address sampling followed by verification, charging one
query per trial. -/
def classicalVerifiedNext (A : Finset I) : Unit → PMF ((I ⊕ Unit) × ℕ) :=
  bbhtActualRestartNextPrice (1:Matrix I I ℂ) (Uniform I) 0 A classical_uniform_word.1
    (normalized_uniform Fintype.card_pos) 1

/-- The zero iteration search circuit followed by a Boolean verification query uses exactly one
query. See [BoyerEtAl1998]. -/
theorem classical_trial_actual_queries :
    QueryCount (bbhtBitSearchCircuit (1:Matrix I I ℂ) (Uniform I) 0) +
      QueryCount ([Step.query] : Circuit (I × Bool)) = 1 := by
  rw [classical_uniform_word.2]
  rfl

/-- For nonempty A, verified uniform retries have a geometric first success law, never return an
unmarked address, terminate almost surely, and have expected charged time |I|/|A|. See
[BoyerEtAl1998]. -/
theorem classical_verified_retry (A : Finset I) (hA : 0 < A.card) :
    (∀ r i, branchHaltJoint (classicalVerifiedNext A) (Sum.inr ()) i (r+1) =
      ENNReal.ofReal (1-(A.card:ℝ)/(Fintype.card I:ℝ))^r *
        (if i∈A then ENNReal.ofReal (1/(Fintype.card I:ℝ)) else 0)) ∧
    (∀ i k, i∉A → branchHaltJoint (classicalVerifiedNext A) (Sum.inr ()) i k=0) ∧
    generalNeverMass (branchClockNext (classicalVerifiedNext A)) (branchClockEmbed (Sum.inr ()))=0 ∧
    generalUnboundedTime (branchClockNext (classicalVerifiedNext A)) (branchClockEmbed (Sum.inr ()))=
      ENNReal.ofReal ((Fintype.card I:ℝ)/(A.card:ℝ)) := by
  have hN : 0 < Fintype.card I := Fintype.card_pos
  have hn : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr hN
  have ht : (0:ℝ) < A.card := Nat.cast_pos.mpr hA
  have hp : 0 < MeasureProb (GroverState A 0) A := by rw [zero_grover_mass]; positivity
  have hs := actualRestartFirstSuccess I hN (1:Matrix I I ℂ) (Uniform I)
    (Submonoid.one_mem _) (normalized_uniform hN) (by simp) A 0 classical_uniform_word.1 1 (by norm_num)
  have he := (actualRestartExpectedReceipt I hN (1:Matrix I I ℂ) (Uniform I)
    (Submonoid.one_mem _) (normalized_uniform hN) (by simp) A 0 classical_uniform_word.1 1 (by norm_num)).2 hp
  have hdiv : (1:ℝ)/((A.card:ℝ)/(Fintype.card I:ℝ)) = (Fintype.card I:ℝ)/(A.card:ℝ) := by
    field_simp
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [classicalVerifiedNext,zero_grover_mass,zero_grover_born,Nat.mul_one] using hs.1
  · exact hs.2.1
  · exact he.1
  · simpa only [classicalVerifiedNext,zero_grover_mass,Nat.cast_one,hdiv] using he.2.1

omit [DecidableEq I] in

/-- If more than three quarters of the addresses are marked, the ratio |I|/|A| is strictly below
4/3. See [BoyerEtAl1998]. -/
theorem classical_high_density_queries (A : Finset I)
    (hdense : 3*Fintype.card I < 4*A.card) :
    (Fintype.card I:ℝ)/(A.card:ℝ) < 4/3 := by
  have ht : 0 < A.card := by have := Fintype.card_pos (α:=I); omega
  have htr : (0:ℝ) < A.card := Nat.cast_pos.mpr ht
  have hd : 3*(Fintype.card I:ℝ) < 4*(A.card:ℝ) := by exact_mod_cast hdense
  apply (div_lt_iff₀ htr).mpr
  nlinarith

/-- For nonempty A, the total mass of all first success outputs and stopping times is one. See
[BoyerEtAl1998]. -/
theorem classical_first_success_normalized (A : Finset I) (hA : 0 < A.card) :
    (∑' i : I, ∑' k : ℕ, branchHaltJoint (classicalVerifiedNext A) (Sum.inr ()) i k)=1 := by
  have hl := actualRestartAttemptLaw I Fintype.card_pos (1:Matrix I I ℂ) (Uniform I)
    (Submonoid.one_mem _) (normalized_uniform Fintype.card_pos) (by simp)
    A 0 classical_uniform_word.1 1
  have hpos := unitRestart_positive (classicalVerifiedNext A) 1 hl.2.2 (by norm_num)
  have hc := (branch_cost_output_pending_never_conservation Unit I (classicalVerifiedNext A)
    hpos (Sum.inr ())).1
  rw [(classical_verified_retry A hA).2.2.1,add_zero] at hc
  exact hc

/-- Summing the zero iteration verified sample law over the Boolean register gives uniform
address mass 1/|I|. -/
theorem classical_uniform_address_marginal (A : Finset I) (i : I) :
    (∑ b : Bool, bbhtBitSearchSamples (1:Matrix I I ℂ) (Uniform I) 0 A
      classical_uniform_word.1 (normalized_uniform Fintype.card_pos) (i,b)) =
      ENNReal.ofReal (1/(Fintype.card I:ℝ)) := by
  simpa only [zero_grover_born] using bbhtBitSearchSamples_marginal Fintype.card_pos
    (1:Matrix I I ℂ) (Uniform I) (Submonoid.one_mem _) (normalized_uniform Fintype.card_pos)
    (by simp) A 0 classical_uniform_word.1 i

/-- The address marginal of the zero iteration verified sampling distribution is the uniform
distribution on I. -/
theorem classical_uniform_address_law (A : Finset I) :
    (bbhtBitSearchSamples (1:Matrix I I ℂ) (Uniform I) 0 A
      classical_uniform_word.1 (normalized_uniform Fintype.card_pos)).map Prod.fst =
      PMF.uniformOfFintype' I := by
  ext i
  rw [PMF.uniformOfFintype'_apply]
  calc
    _ = ∑ b : Bool, bbhtBitSearchSamples (1:Matrix I I ℂ) (Uniform I) 0 A
        classical_uniform_word.1 (normalized_uniform Fintype.card_pos) (i,b) := by
      rw [PMF.map_apply,tsum_fintype,Fintype.sum_prod_type,Finset.sum_eq_single i]
      · simp
      · intro a _ hai
        simp [Ne.symm hai]
      · simp
    _ = ENNReal.ofReal (1/(Fintype.card I:ℝ)) := classical_uniform_address_marginal A i
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (Fintype.card_pos (α:=I))),
        ENNReal.ofReal_one,ENNReal.ofReal_natCast,one_div]

/-- One classical restart step is uniform sampling followed by a markedness test, with query
charge one. See [BoyerEtAl1998]. -/
theorem classical_verified_kernel (A : Finset I) :
    classicalVerifiedNext A () = (PMF.uniformOfFintype' I).map
      (fun i => (((if i∈A then Sum.inl i else Sum.inr ()) : I ⊕ Unit),1)) := by
  rw [classicalVerifiedNext,bbhtActualRestartNextPrice_eq_map,
    ← classical_uniform_address_law A,PMF.map_comp]
  rfl

end

end Qatlib.Papers.QSearchBoyer98.MainResults
