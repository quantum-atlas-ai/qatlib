/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiInvariantProgramCharacterizationStat
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiInvariantExtraction
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.Theorem9SDPCharacterizationTran

/-!
# Polynomial extraction for successful invariant programs

This module proves `tiInvariantProgramCharacterization` by extracting coefficients from
invariant program prefixes. Unitarity gives normalization, translation symmetry gives the
matching equations, and the assumed readout success bounds the final coefficient; the SDP
characterization then supplies matrix feasibility. This connects invariant ordered search
programs with the semidefinite perspective of [ChildsLandahlParrilo2007].

## Main statements

* `tiInvariantProgramCharacterization`: proves the packaged characterization, including resource
  counts and translated prefix states.

## References

* [Childs, Landahl and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

/-- A successful program with translation-commuting unitary gates yields the normalized
polynomial representation, resource counts, and polynomial and SDP feasibility asserted by
`TiInvariantProgramCharacterization`; see [ChildsLandahlParrilo2007]. -/
theorem tiInvariantProgramCharacterization : TiInvariantProgramCharacterization := by
  intro n k _ ε U hU hsuccess
  have hu : ∀ t ∈ Finset.Icc 1 k,U t ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ := fun t ht => (hU t ht).1
  have hc : ∀ t ∈ Finset.Icc 1 k,tiTranslation n*U t=U t*tiTranslation n := fun t ht => (hU t ht).2
  let p := tiInvariantCoefficients n U
  have hp0 : p 0=tiDirichletVec n := by
    funext i
    simp only [p,tiInvariantCoefficients,ite_true]
  have hnorm (t : ℕ) (ht : t ∈ Finset.Icc 0 k) : ∑ i,Complex.normSq (p t i)=1 :=
    ti_invariant_coefficients_normalized n k U hu hc t (Finset.mem_Icc.mp ht).2
  have hm (t : ℕ) (ht : t ∈ Finset.Icc 1 k) (z : ℂ) (hz : z^n=(-1:ℂ)^t) :
      ‖tiPolyEval (p t) z‖=‖tiPolyEval (p (t-1)) z‖ :=
    ti_invariant_coefficients_match n k U hu hc t ht z hz
  have hfin : 1-ε≤Complex.normSq (p k 0) := by
    have he := hsuccess (0 : Fin (2*n))
    rw [ti_invariant_prefix_state n k U hc k le_rfl] at he
    have houtput : ospFun n (0 : Fin (2*n))=0 := by
      apply Fin.val_injective
      simp [ospFun]
    rw [houtput,ti_state_readout] at he
    exact he
  have hpoly : tiPolyConditions n k ε := by
    refine ⟨p,hp0,?_,hnorm 0 (by simp),hfin,hm⟩
    intro t ht
    apply hnorm t
    simp only [Finset.mem_Icc] at ht ⊢
    omega
  obtain ⟨hq,hg⟩ := ti_invariant_word_counts n k U
  refine ⟨ti_invariant_word_unitary n k U hu,hq,hg,?_,hpoly,
    tiPolyConditions_implies_tiSDPFeasible n k ε hpoly⟩
  exact ⟨p,hp0,hnorm,hm,hfin,fun t ht j => ti_invariant_prefix_all n k U hc t
    (Finset.mem_Icc.mp ht).2 j⟩

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
