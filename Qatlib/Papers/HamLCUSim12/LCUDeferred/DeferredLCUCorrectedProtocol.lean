/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUCorrectedLists
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

def cwControlBit (k : ℕ) (c : Fin (k+1)→ℝ) : Fin (k+1) :=
  ⟨(cwPositiveTerms k c).card%(k+1),Nat.mod_lt _ (Nat.succ_pos k)⟩

def cwPositiveCircuitCorrected (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ) :=
  chainCircuitCorrected (k+1) (cwChainList k 0 c U (cwPositiveTerms k c))

def cwNegativeCircuitCorrected (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ) :=
  chainCircuitCorrected (k+1) (cwChainList k (cwPositiveTerms k c).card (fun q=>|c q|) U (cwNegativeTerms k c))

theorem cwProtocolCorrected_decompose (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ) :
    cwProtocolCorrected k c U=lcuLevelGateCorrected (k+1) (cwControlBit k c)
      (vKappaSource (cwPositiveWeight k c/cwNegativeWeight k c))
      (cwPositiveCircuitCorrected k c U) (-cwNegativeCircuitCorrected k c U) := by
  unfold cwProtocolCorrected cwControlBit cwPositiveCircuitCorrected cwNegativeCircuitCorrected
    cwPositiveWeight cwNegativeWeight cwPositiveTerms cwNegativeTerms
  rw [Finset.sum_filter,Finset.sum_filter]

omit [Fintype I] [DecidableEq I] in

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

theorem cw_negative_tail_fresh (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ)
    (hc : ∀ q,c q≠0) (hn : ∃ q,c q<0) :
    ∀ t∈(cwChainList k (cwPositiveTerms k c).card (fun q=>|c q|) U (cwNegativeTerms k c)).tail,
      cwControlBit k c≠t.1 := by
  exact cwChainList_tail_fresh k (cwPositiveTerms k c).card _ U (cwNegativeTerms k c)
    (cw_negative_nonempty k c hn) (le_of_eq (cw_sign_cards k c hc))

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
