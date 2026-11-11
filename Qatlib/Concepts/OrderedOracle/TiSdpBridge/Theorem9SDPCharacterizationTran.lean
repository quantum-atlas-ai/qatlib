/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.Theorem9SDPCharacterizationStat

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGramRankOne

/-!
# Proof of the ordered search SDP characterization

This module proves `Theorem9SDPCharacterization`. Polynomial coefficient vectors give feasible
matrices through `gramOuter`; conversely, rank-one Gram representatives with the same
generalized traces yield polynomial witnesses without decreasing the terminal coefficient bound.
This relates the matrix and polynomial descriptions used in semidefinite approaches to ordered
search [ChildsLandahlParrilo2007].

## Main statements

* `tiPolyConditions_implies_tiSDPFeasible`: constructs feasible Gram matrices from polynomial
  data.
* `tiSDPFeasible_implies_tiPolyConditions`: extracts polynomial witnesses from feasible
  matrices.
* `theorem9SDPCharacterization`: combines the two implications.

## References

* [Childs, Landahl and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.OrderedOracle.TiSdpBridge
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

/-- Every entry of the Gram outer product of `tiDirichletVec n` equals the reciprocal of `n`. -/
theorem tiDirichletVec_gram (n : ℕ) : ∀ i j : Fin n,
    gramOuter (tiDirichletVec n) i j = (n : ℂ)⁻¹ := by
  intro i j
  change (starRingEnd ℂ) ((Real.sqrt (n : ℝ) : ℂ)⁻¹) * (Real.sqrt (n : ℝ) : ℂ)⁻¹ = (n : ℂ)⁻¹
  rw [Complex.conj_inv, Complex.conj_ofReal]
  rw [← pow_two, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simp

/-- Polynomial witnesses satisfying `tiPolyConditions n k ε` yield witnesses for `tiSDPFeasible
n k ε`. -/
theorem tiPolyConditions_implies_tiSDPFeasible (n k : ℕ) [NeZero n] (ε : ℝ)
    (h : tiPolyConditions n k ε) : tiSDPFeasible n k ε := by
  classical
  obtain ⟨p, hp0, hnorm, _, hfin, hroot⟩ := h
  apply (lemma11_tiSDPFeasible_iff_rootForm n k ε).mpr
  refine ⟨(fun t => gramOuter (p t)), (fun _ => gramOuter_posSemidef _), ?_, ?_, ?_, ?_⟩
  · intro i j
    change gramOuter (p 0) i j = (n : ℂ)⁻¹
    rw [hp0]
    exact tiDirichletVec_gram n i j
  · intro t ht
    rw [gramOuter_trace, hnorm t ht]
    simp
  · simpa only [gramOuter, Matrix.of_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] using hfin
  · intro t ht z hz
    have hcircle := norm_eq_one_of_twisted_root (Nat.pos_of_ne_zero (NeZero.ne n)) t hz
    rw [matrixLaurent_outer_eq_abs_sq _ hcircle, matrixLaurent_outer_eq_abs_sq _ hcircle]
    simpa only [tiPolyEval] using congrArg (fun r : ℝ => ((r ^ 2 : ℝ) : ℂ)) (hroot t ht z hz)

/-- Feasible translation-invariant SDP matrices yield coefficient vectors satisfying
`tiPolyConditions n k ε`. -/
theorem tiSDPFeasible_implies_tiPolyConditions (n k : ℕ) [NeZero n] (ε : ℝ)
    (h : tiSDPFeasible n k ε) : tiPolyConditions n k ε := by
  classical
  obtain ⟨Q,hps,hQ,htr,hfin,hroot⟩ := (lemma11_tiSDPFeasible_iff_rootForm n k ε).mp h
  have hv : ∀ t : ℕ,t∈Finset.Icc 1 k → ∃ v : Fin n → ℂ,
      (∀ j : ℤ,genTrace (gramOuter v) j=genTrace (Q t) j) ∧ Q t 0 0≤gramOuter v 0 0 := by
    intro t ht
    have hne : Q t≠0 := by
      intro hz
      have hh := htr t ht
      rw [hz,Matrix.trace_zero] at hh
      exact zero_ne_one hh
    obtain ⟨v,_,htrace,hfirst⟩ := exists_outer_gram (Q t) (hps t) hne
    exact ⟨v,htrace,hfirst⟩
  choose v hv using hv
  let p : ℕ → (Fin n → ℂ) := fun t =>
    if t=0 then tiDirichletVec n else if ht : t∈Finset.Icc 1 k then v t ht else 0
  have hzero : gramOuter (p 0)=Q 0 := by
    ext i j
    simp only [p,if_pos rfl,tiDirichletVec_gram,hQ]
  have hfamily (t : ℕ) (ht : t∈Finset.Icc 0 k) :
      (∀ j : ℤ,genTrace (gramOuter (p t)) j=genTrace (Q t) j) ∧ Q t 0 0≤gramOuter (p t) 0 0 := by
    by_cases ht0 : t=0
    · subst t
      simp [hzero]
    · have ht1 : t∈Finset.Icc 1 k := by simp only [Finset.mem_Icc] at ht ⊢; omega
      simpa only [p,if_neg ht0,dif_pos ht1] using hv t ht1
  have htrace (t : ℕ) (ht : t∈Finset.Icc 0 k) : (Q t).trace=1 := by
    by_cases ht0 : t=0
    · subst t
      exact ti_initial_trace n Q hQ
    · apply htr
      simp only [Finset.mem_Icc] at ht ⊢
      omega
  have hnorm (t : ℕ) (ht : t∈Finset.Icc 0 k) : ∑ j : Fin n,Complex.normSq (p t j)=1 := by
    have h := (hfamily t ht).1 0
    rw [genTrace_zero,genTrace_zero,gramOuter_trace,htrace t ht] at h
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_one] using h)
  have hlaurent (t : ℕ) (ht : t∈Finset.Icc 0 k) (z : ℂ) :
      matrixLaurent (gramOuter (p t)) z=matrixLaurent (Q t) z := by
    unfold matrixLaurent
    apply Finset.sum_congr rfl
    intro j _
    rw [(hfamily t ht).1 j]
  refine ⟨p,by simp only [p,if_pos rfl],?_,?_,?_,?_⟩
  · intro t ht
    exact hnorm t (by simp only [Finset.mem_Icc] at ht ⊢; omega)
  · exact hnorm 0 (by simp)
  · have h := (Complex.le_def.mp (hfamily k (by simp)).2).1
    have hfinal : (Q k 0 0).re≤Complex.normSq (p k 0) := by
      simpa only [gramOuter,Matrix.of_apply,Complex.star_def,
        ← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re] using h
    exact hfin.trans hfinal
  · intro t ht z hz
    have ht0 : t∈Finset.Icc 0 k := by simp only [Finset.mem_Icc] at ht ⊢; omega
    have hprev : t-1∈Finset.Icc 0 k := by simp only [Finset.mem_Icc] at ht ⊢; omega
    have hcircle := norm_eq_one_of_twisted_root (Nat.pos_of_ne_zero (NeZero.ne n)) t hz
    have he : matrixLaurent (gramOuter (p t)) z=matrixLaurent (gramOuter (p (t-1))) z := by
      rw [hlaurent t ht0 z,hlaurent (t-1) hprev z]
      exact hroot t ht z hz
    rw [matrixLaurent_outer_eq_abs_sq _ hcircle,matrixLaurent_outer_eq_abs_sq _ hcircle] at he
    have hs := Complex.ofReal_injective he
    change ‖tiPolyEval (p t) z‖^2=‖tiPolyEval (p (t-1)) z‖^2 at hs
    nlinarith [norm_nonneg (tiPolyEval (p t) z),norm_nonneg (tiPolyEval (p (t-1)) z)]

/-- Translation-invariant SDP feasibility and the polynomial conditions are equivalent for every
nonzero search size, query count, and real error parameter, in the ordered search setting of
[ChildsLandahlParrilo2007]. -/
theorem theorem9SDPCharacterization : Theorem9SDPCharacterization := by
  intro n k _ ε
  exact ⟨tiSDPFeasible_implies_tiPolyConditions n k ε,tiPolyConditions_implies_tiSDPFeasible n k ε⟩

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
