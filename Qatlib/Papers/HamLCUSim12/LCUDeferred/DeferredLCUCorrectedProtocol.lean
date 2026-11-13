/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUCorrectedLists

/-!
# Corrected signed LCU protocol

This module assembles the corrected positive and negative chains into the signed LCU protocol
associated with Theorem 3 of [ChildsWiebe2012]. `cwProtocolCorrected_decompose` expresses the
protocol as a corrected LCU level using the positive chain and the negated negative chain, with
rotation parameter equal to the ratio of their coefficient masses.

The tail-position lemmas show that both chains preserve the final control bit. They support
`cwProtocolCorrected_unitary`, while `cw_prefixes_zero_corner` computes each chain's zero
ancilla amplitude as its weighted matrix sum divided by its coefficient mass.

## Main statements

* `cwControlBit`, `cwPositiveCircuitCorrected`, and `cwNegativeCircuitCorrected` name the final
  control and its two chains.
* `cw_prefixes_unitary` proves both chains unitary for unitary payloads and nonzero
  coefficients.
* `cwProtocolCorrected_unitary` proves the assembled protocol unitary when both coefficient
  signs occur.
- `cw_prefixes_zero_corner` evaluates both chain fibers for arbitrary input vectors.

## References

- [Childs and Wiebe, 2012][ChildsWiebe2012], Theorem 3.
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The final signed-combination control bit, chosen at the positive index-set cardinality
modulo `k + 1`. -/
def cwControlBit (k : ℕ) (c : Fin (k+1)→ℝ) : Fin (k+1) :=
  ⟨(cwPositiveTerms k c).card%(k+1),Nat.mod_lt _ (Nat.succ_pos k)⟩

/-- The corrected chain for positive coefficients, with the corresponding matrices and
ancilla-position offset zero. -/
def cwPositiveCircuitCorrected (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ) :=
  chainCircuitCorrected (k+1) (cwChainList k 0 c U (cwPositiveTerms k c))

/-- The corrected chain for negative coefficients using their absolute values, with
ancilla-position offset equal to the number of positive terms. -/
def cwNegativeCircuitCorrected (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ) :=
  chainCircuitCorrected (k+1) (cwChainList k (cwPositiveTerms k c).card (fun q=>|c q|) U (cwNegativeTerms k c))

/-- Rewrites the corrected signed protocol as a corrected LCU level on `cwControlBit`, combining
the positive chain with the negated negative chain using the positive-to-negative mass
ratio. -/
theorem cwProtocolCorrected_decompose (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ) :
    cwProtocolCorrected k c U=lcuLevelGateCorrected (k+1) (cwControlBit k c)
      (vKappaSource (cwPositiveWeight k c/cwNegativeWeight k c))
      (cwPositiveCircuitCorrected k c U) (-cwNegativeCircuitCorrected k c U) := by
  unfold cwProtocolCorrected cwControlBit cwPositiveCircuitCorrected cwNegativeCircuitCorrected
    cwPositiveWeight cwNegativeWeight cwPositiveTerms cwNegativeTerms
  rw [Finset.sum_filter,Finset.sum_filter]

omit [Fintype I] [DecidableEq I] in

/-- For nonzero coefficients with at least one negative term, no entry of the positive
chain-list tail uses the final signed-combination control bit. -/
theorem cw_positive_tail_fresh (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ)
    (hc : ∀ q,c q≠0) (hn : ∃ q,c q<0) :
    ∀ t∈(cwChainList k 0 c U (cwPositiveTerms k c)).tail,cwControlBit k c≠t.1 := by
  have hcards := cw_sign_cards k c hc
  have hncard := Finset.card_pos.mpr (cw_negative_nonempty k c hn)
  have hap : (cwPositiveTerms k c).card<k+1 := by omega
  have hbound : 0+(cwPositiveTerms k c).card≤k+1 := by omega
  intro t ht
  have hr := cwChainList_bit_range k 0 c U (cwPositiveTerms k c) hbound t (List.mem_of_mem_tail ht)
  intro he
  have hv := congrArg Fin.val he
  simp only [cwControlBit,Nat.mod_eq_of_lt hap] at hv
  omega

omit [Fintype I] [DecidableEq I] in

/-- For nonzero coefficients with at least one negative term, no entry of the negative
chain-list tail uses the final signed-combination control bit. -/
theorem cw_negative_tail_fresh (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ)
    (hc : ∀ q,c q≠0) (hn : ∃ q,c q<0) :
    ∀ t∈(cwChainList k (cwPositiveTerms k c).card (fun q=>|c q|) U (cwNegativeTerms k c)).tail,
      cwControlBit k c≠t.1 := by
  exact cwChainList_tail_fresh k (cwPositiveTerms k c).card _ U (cwNegativeTerms k c)
    (cw_negative_nonempty k c hn) (le_of_eq (cw_sign_cards k c hc))

/-- Both corrected sign chains are unitary when all system matrices are unitary and all
coefficients are nonzero. -/
theorem cw_prefixes_unitary (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ)
    (hU : ∀ q,U q∈Matrix.unitaryGroup I ℂ) (hc : ∀ q,c q≠0) :
    cwPositiveCircuitCorrected k c U∈Matrix.unitaryGroup _ ℂ ∧
    cwNegativeCircuitCorrected k c U∈Matrix.unitaryGroup _ ℂ := by
  have hcards := cw_sign_cards k c hc
  have hpbound : 0+(cwPositiveTerms k c).card≤k+1 := by omega
  constructor
  · exact chainCircuitCorrected_unitary _
      (cwChainList_positive k 0 c U (cwPositiveTerms k c) (fun q hq=>(Finset.mem_filter.mp hq).2))
      (cwChainList_unitaries k 0 c U (cwPositiveTerms k c) hU)
      (cwChainList_bits_pairwise k 0 c U (cwPositiveTerms k c) hpbound)
  · exact chainCircuitCorrected_unitary _
      (cwChainList_positive k (cwPositiveTerms k c).card _ U (cwNegativeTerms k c)
        (fun q hq=>abs_pos.mpr (ne_of_lt (Finset.mem_filter.mp hq).2)))
      (cwChainList_unitaries k (cwPositiveTerms k c).card _ U (cwNegativeTerms k c) hU)
      (cwChainList_bits_pairwise k (cwPositiveTerms k c).card _ U (cwNegativeTerms k c) (le_of_eq hcards))

/-- The corrected signed LCU protocol is unitary when its system matrices are unitary and its
coefficients are nonzero with both signs present. This verifies unitarity of the concrete
corrected construction associated with Theorem 3 in [ChildsWiebe2012]. -/
theorem cwProtocolCorrected_unitary (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ)
    (hU : ∀ q,U q∈Matrix.unitaryGroup I ℂ) (hc : ∀ q,c q≠0)
    (hp : ∃ q,0<c q) (hn : ∃ q,c q<0) : cwProtocolCorrected k c U∈Matrix.unitaryGroup _ ℂ := by
  rw [cwProtocolCorrected_decompose]
  have hu := cw_prefixes_unitary k c U hU hc
  have hneg : -cwNegativeCircuitCorrected k c U∈Matrix.unitaryGroup _ ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    simpa using! Unitary.star_mul_self_of_mem hu.2
  apply lcuLevelGateCorrected_unitary _ _
    (div_nonneg (cw_positive_weight_pos k c hp).le (cw_negative_weight_pos k c hn).le) _ _ hu.1 hneg
  · exact chainCircuitCorrected_preserves _ _ (cw_positive_tail_fresh k c U hc hn)
  · exact preservesLCUBit_neg _ _
      (chainCircuitCorrected_preserves _ _ (cw_negative_tail_fresh k c U hc hn))

/-- When both coefficient signs occur, each corrected sign chain's zero ancilla amplitude is its
weighted matrix sum applied to `ψ`, divided by its own coefficient mass. The identity
requires neither normalized input nor unitary payloads. -/
theorem cw_prefixes_zero_corner (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ)
    (hp : ∃ q,0<c q) (hn : ∃ q,c q<0) (ψ : QState I) (x : I) :
    (cwPositiveCircuitCorrected k c U*ᵥTensorState (Ket (cwZero k)) ψ) (cwZero k,x)=
      ((∑ q∈cwPositiveTerms k c,c q • U q)*ᵥψ) x/(cwPositiveWeight k c:ℂ) ∧
    (cwNegativeCircuitCorrected k c U*ᵥTensorState (Ket (cwZero k)) ψ) (cwZero k,x)=
      ((∑ q∈cwNegativeTerms k c,|c q| • U q)*ᵥψ) x/(cwNegativeWeight k c:ℂ) := by
  constructor
  · have hh := chainCircuitCorrected_zero_corner
      (cwChainList k 0 c U (cwPositiveTerms k c))
      (cwChainList_nonempty k 0 c U _ (cw_positive_nonempty k c hp))
      (cwChainList_positive k 0 c U _ (fun q hq=>(Finset.mem_filter.mp hq).2)) ψ x
    rw [cwChainList_weight,cwChainList_weighted] at hh
    exact hh
  · have hh := chainCircuitCorrected_zero_corner
      (cwChainList k (cwPositiveTerms k c).card (fun q=>|c q|) U (cwNegativeTerms k c))
      (cwChainList_nonempty k _ _ U _ (cw_negative_nonempty k c hn))
      (cwChainList_positive k _ _ U _ (fun q hq=>abs_pos.mpr (ne_of_lt (Finset.mem_filter.mp hq).2))) ψ x
    rw [cwChainList_weight,cwChainList_weighted] at hh
    exact hh

end Qatlib.Papers.HamLCUSim12.LCUDeferred
