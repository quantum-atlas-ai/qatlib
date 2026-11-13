/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartAttemptLawStat
import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartSearchWordTigh

/-!
# Distribution of one verified restart attempt

Proves `actualRestartAttemptLaw` by reducing verification to a deterministic membership test and
extracting the address marginal of the search circuit. `bbhtActualRestartNextPrice_eq_map`
expresses the full paid transition as a pushforward of the circuit samples. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `bbhtActualRestartNextPrice_eq_map`: Expresses a paid restart transition as the search-sample
  distribution mapped to a marked address or a retry state, paired with the fixed price.
* `bbhtBitSearchSamples_marginal`: For a unitary preparation of the uniform state on a nonempty
  finite space, the address marginal of the bit-search samples equals the Born probability of
  the Grover state.
* `actualRestartAttemptLaw`: Establishes the one-attempt law `ActualRestartAttemptLaw` for the
  verified Grover restart transition.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The verification distribution is the point mass at the Boolean membership test for `i ∈ A`. -/
theorem bbhtVerificationLaw_eq_pure (A : Finset I) (i : I) :
    bbhtVerificationLaw A i = PMF.pure (decide (i ∈ A)) := by
  simp only [bbhtVerificationLaw, run_query_bitOracleOn_ket, Bool.false_xor,
    bornDistribution_ket, PMF.pure_map]

/-- Expresses a paid restart transition as the search-sample distribution mapped to a marked
address or a retry state, paired with the fixed price. -/
theorem bbhtActualRestartNextPrice_eq_map (T' : Matrix I I ℂ) (v : QState I) (j : ℕ)
    (A : Finset I) (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j))
    (hv : Normalized v) (price : ℕ) :
    bbhtActualRestartNextPrice T' v j A hC hv price () =
      (bbhtBitSearchSamples T' v j A hC hv).map
        (fun q => ((if q.1 ∈ A then Sum.inl q.1 else Sum.inr ()), price)) := by
  simp only [bbhtActualRestartNextPrice, bbhtVerificationLaw_eq_pure, PMF.pure_map,
    decide_eq_true_eq]
  rfl

/-- For a unitary preparation of the uniform state on a nonempty finite space, the address
marginal of the bit-search samples equals the Born probability of the Grover state. -/
theorem bbhtBitSearchSamples_marginal (hN : 0 < Fintype.card I)
    (T' : Matrix I I ℂ) (v : QState I) (hT : T' ∈ Matrix.unitaryGroup I ℂ)
    (hv : Normalized v) (hprep : T' *ᵥ v = Uniform I) (A : Finset I) (j : ℕ)
    (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j)) (i : I) :
    (∑ b : Bool, bbhtBitSearchSamples T' v j A hC hv (i,b)) =
      ENNReal.ofReal (BornProb (GroverState A j) i) := by
  have hr := (actualRestartSearchWord I hN T' v hT hv hprep A j).2.2.2
  have hb : ∀ b : Bool, bbhtBitSearchSamples T' v j A hC hv (i,b) =
      ENNReal.ofReal (BornProb (GroverState A j) i * BornProb Minus b) := by
    intro b
    unfold bbhtBitSearchSamples
    simp only [hr, bornDistribution_apply, bornProb_tensorState]
  simp_rw [hb, ENNReal.ofReal_mul (bornProb_nonneg _ _)]
  rw [← Finset.mul_sum]
  have hm : (∑ b : Bool, ENNReal.ofReal (BornProb Minus b)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => bornProb_nonneg Minus b)]
    have h := measureProb_univ normalized_minus
    simpa only [MeasureProb, ENNReal.ofReal_one] using congrArg ENNReal.ofReal h
  rw [hm, mul_one]

/-- Establishes the one-attempt law `ActualRestartAttemptLaw` for the verified Grover restart
transition. See [BoyerEtAl1998]. -/
theorem actualRestartAttemptLaw : ActualRestartAttemptLaw := by
  intro I _ _ hN T' v hT hv hprep A j hC price
  (try dsimp only)
  have hmap := bbhtActualRestartNextPrice_eq_map T' v j A hC hv price
  have hm := bbhtBitSearchSamples_marginal hN T' v hT hv hprep A j hC
  have hi (i : I) : bbhtActualRestartNextPrice T' v j A hC hv price () (Sum.inl i,price) =
      if i ∈ A then ENNReal.ofReal (BornProb (GroverState A j) i) else 0 := by
    rw [hmap, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    have he (q : I) (b : Bool) :
        (if (Sum.inl i,price) = ((if q ∈ A then Sum.inl q else Sum.inr ()),price) then
          bbhtBitSearchSamples T' v j A hC hv (q,b) else 0) =
        if i = q then (if i ∈ A then bbhtBitSearchSamples T' v j A hC hv (q,b) else 0) else 0 := by
      by_cases hq : q ∈ A <;> by_cases hie : i = q <;> simp [hq,hie] at *
    simp_rw [he]
    by_cases hia : i ∈ A
    · simpa [hia] using hm i
    · simp [hia]
  have hk (cfg : I ⊕ Unit) (k : ℕ) (hne : k ≠ price) :
      bbhtActualRestartNextPrice T' v j A hC hv price () (cfg,k) = 0 := by
    rw [hmap, PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro q
    simp [hne]
  refine ⟨hi, ?_, hk⟩
  have ht := (bbhtActualRestartNextPrice T' v j A hC hv price ()).tsum_coe
  rw [tsum_prod_type', ENNReal.tsum_comm] at ht
  have he : (∑' k : ℕ, ∑' cfg : I ⊕ Unit,
      bbhtActualRestartNextPrice T' v j A hC hv price () (cfg,k)) =
      ∑' cfg : I ⊕ Unit, bbhtActualRestartNextPrice T' v j A hC hv price () (cfg,price) := by
    apply tsum_eq_single price
    intro k hne
    simp only [hk _ k hne, tsum_zero]
  rw [he, tsum_sum_type', tsum_fintype, tsum_fintype] at ht
  simp only [hi, Fintype.sum_unique] at ht
  have hs : (∑ i : I, if i ∈ A then ENNReal.ofReal (BornProb (GroverState A j) i) else 0) =
      ENNReal.ofReal (MeasureProb (GroverState A j) A) := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => bornProb_nonneg _ i)).symm
  rw [hs] at ht
  have hsub : bbhtActualRestartNextPrice T' v j A hC hv price () (Sum.inr (),price) =
      1-ENNReal.ofReal (MeasureProb (GroverState A j) A) :=
    ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top
    (by simpa only [add_comm] using ht)
  rw [hsub, ENNReal.ofReal_sub 1 (show 0 ≤ MeasureProb (GroverState A j) A from
    Finset.sum_nonneg (fun i _ => bornProb_nonneg _ i)), ENNReal.ofReal_one]

end Qatlib.Concepts.SearchStopping.PaidRestart
