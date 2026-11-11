/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ExactLaurentProgramIffSDPStat
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleSpectralFactorTran
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ExactProgramFromSDPTran
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.Theorem9SDPCharacterizationTran

/-!
# Exact Laurent program and SDP equivalence proof

This module proves `ExactLaurentProgramIffSDP` by constructing normalized polynomial factors
from an `exactTIProgram` and combining that construction with the reverse SDP conversion.
`exactLaurentProgram_to_polyConditions` supplies the intermediate zero-error polynomial
conditions in the ordered-search framework of [ChildsLandahlParrilo2007].

## Main statements

* `exactLaurentProgram_to_polyConditions`: conversion of exact Laurent witnesses into zero-error
  polynomial witnesses.
* `exactLaurentProgramIffSDP`: equivalence of `exactTIProgram n k` and `tiSDPFeasible n k 0` for
  nonzero size.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Polynomial Matrix
open scoped Classical BigOperators ComplexOrder

/-- An exact translation-invariant Laurent-program witness for nonzero size yields polynomial
conditions with error parameter zero. -/
theorem exactLaurentProgram_to_polyConditions (n k : ℕ) [NeZero n]
    (h : exactTIProgram n k) : tiPolyConditions n k 0 := by
  obtain ⟨q,hq0,hqk,hmean,hmatch,hnonneg⟩ := h
  have hn : 0<n := NeZero.pos n
  have ha (t : ℕ) (ht : t∈Finset.Icc 0 k) :
      complexLaurentNonnegative (fun i => (q t i : ℂ)) := by
    constructor
    · unfold complexLaurentCoefficient
      split_ifs <;> simp_all
    · intro z hz
      rw [complexLaurentEval_ofReal]
      exact hnonneg t ht z hz
  let spec (t : ℕ) (ht : t∈Finset.Icc 0 k) : Fin n → ℂ :=
    Classical.choose (laurentCircleSpectralFactor n (fun i => (q t i : ℂ)) (ha t ht))
  have hs (t : ℕ) (ht : t∈Finset.Icc 0 k) :=
    Classical.choose_spec (laurentCircleSpectralFactor n (fun i => (q t i : ℂ)) (ha t ht))
  let D : Fin n → ℂ := tiDirichletVec n
  let E : Fin n → ℂ := fun i => if i=0 then 1 else 0
  let p : ℕ → Fin n → ℂ := fun t =>
    if t=0 then D else if t=k then E else if ht : t∈Finset.Icc 0 k then spec t ht else 0
  have hEn : ∑ i : Fin n, Complex.normSq (E i)=1 := by simp [E]
  have hEg (z : ℂ) : tiPolyEval E z=1 := by simp [E,tiPolyEval]
  have hDg : gramOuter D=(n : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin n => (1 : ℂ)) := by
    ext i j
    simp only [Matrix.smul_apply,Matrix.of_apply,smul_eq_mul,mul_one]
    exact tiDirichletVec_gram n i j
  have hDn : ∑ i : Fin n,Complex.normSq (D i)=1 := by
    have ht := ti_initial_trace n (fun _ => gramOuter D) (tiDirichletVec_gram n)
    rw [gramOuter_trace] at ht
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_one] using ht)
  have hlast (z : ℂ) : laurentEval (q k) z=1 := by
    unfold laurentEval
    rw [Finset.sum_eq_single (0 : Fin n)]
    · simp [hqk.1]
    · intro i _ hi
      have hiv : i.val≠0 := by intro h; apply hi; exact Fin.ext (by simpa using h)
      have hip : (0 : Fin n) < i := by change (0 : ℕ) < i.val; omega
      simp [hiv,hqk.2 i hip]
    · simp
  have hcircle (t : ℕ) (ht : t∈Finset.Icc 0 k) (z : ℂ) (hz : ‖z‖=1) :
      laurentEval (q t) z=((‖tiPolyEval (p t) z‖^2 : ℝ) : ℂ) := by
    by_cases ht0 : t=0
    · subst t
      rw [hq0,← matrixLaurent_onesDiv,← hDg,matrixLaurent_outer_eq_abs_sq D hz]
      simp only [p,if_pos rfl,tiPolyEval]
    · by_cases htk : t=k
      · subst t
        rw [hlast]
        simp [p,ht0,E,tiPolyEval]
      · have he := (hs t ht).2.1 z hz
        rw [complexLaurentEval_ofReal,laurentCoefficientPolynomial_eval] at he
        simpa only [p,if_neg ht0,if_neg htk,dif_pos ht,tiPolyEval] using he
  refine ⟨p,by simp [p,D],?_,?_,?_,?_⟩
  · intro t ht
    have ht0 : t≠0 := by have := Finset.mem_Icc.mp ht; omega
    by_cases htk : t=k
    · simpa only [p,if_neg ht0,if_pos htk] using hEn
    · have hti : t∈Finset.Icc 0 k := by have := Finset.mem_Icc.mp ht; exact Finset.mem_Icc.mpr (by omega)
      have he := (hs t hti).2.2.2.2.1
      have hc0 : complexLaurentCoefficient (fun i => (q t i : ℂ)) 0=(q t 0 : ℂ) := by
        simpa using complexLaurentCoefficient_nat (fun i => (q t i : ℂ)) (0 : Fin n)
      have hm : (complexLaurentCoefficient (fun i => (q t i : ℂ)) 0).re=1 := by
        rw [hc0,Complex.ofReal_re,hmean t hti]
      simpa only [p,if_neg ht0,if_neg htk,dif_pos hti] using he.trans hm
  · simpa only [p,if_pos rfl] using hDn
  · by_cases hk0 : k=0
    · have hn1 : n=1 := by
        by_contra hne
        have hn2 : 1<n := by omega
        let j : Fin n := ⟨1,hn2⟩
        have hj : (0 : Fin n)<j := by simp [j,Fin.lt_def]
        have he := hqk.2 j hj
        rw [hk0,hq0] at he
        dsimp only [fejerCoeffs,j] at he
        simp only [Nat.cast_one] at he
        have hnr : (1 : ℝ)<n := by exact_mod_cast hn2
        have hp : 0<((n : ℝ)-1)/(n : ℝ) := div_pos (by linarith) (by positivity)
        linarith
      simp [p,hk0,D,tiDirichletVec,hn1]
    · simp [p,hk0,E]
  · intro t ht z hz
    have hti : t∈Finset.Icc 0 k := by
      have := Finset.mem_Icc.mp ht; exact Finset.mem_Icc.mpr (by omega)
    have hprev : t-1∈Finset.Icc 0 k := by
      have := Finset.mem_Icc.mp ht; exact Finset.mem_Icc.mpr (by omega)
    have hcz : ‖z‖=1 := norm_eq_one_of_twisted_root hn t hz
    have he : ((‖tiPolyEval (p t) z‖^2 : ℝ) : ℂ)=((‖tiPolyEval (p (t-1)) z‖^2 : ℝ) : ℂ) :=
      (hcircle t hti z hcz).symm.trans ((hmatch t ht z hz).trans (hcircle (t-1) hprev z hcz))
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (Complex.ofReal_injective he)

/-- Proves that the exact translation-invariant Laurent program is equivalent to zero-error
translation-invariant SDP feasibility for every nonzero size. -/
theorem exactLaurentProgramIffSDP : ExactLaurentProgramIffSDP := by
  intro n k _
  exact ⟨fun h => tiPolyConditions_implies_tiSDPFeasible n k 0
    (exactLaurentProgram_to_polyConditions n k h), exactProgramFromSDP n k⟩

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
