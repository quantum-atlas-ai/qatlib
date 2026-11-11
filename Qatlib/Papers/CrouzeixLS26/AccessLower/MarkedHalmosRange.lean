/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.MarkedHalmosOracle
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRange
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.SlackPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TranslatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.AnswerTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TruncatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.ExpectedCost
import Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.MarkedColumns
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.BudgetTruncation
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.InputHybrid
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputReadout
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.PreparedRepeat
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.SourceWordTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRangeConvex

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CopyEvolution.Discriminate
/-! Exact true numerical-range geometry for the constructed Jordan/Halmos
matrix, using actual Euclidean Rayleigh quotients and explicit unit vectors.
The maximum and directional support are derived; no enclosure or extremum
certificate is supplied. This is a mathematical geometry theorem, not an
algorithm for learning the hidden matrix parameters from its oracle. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.MarkedHalmos
open Qatlib Matrix
open scoped BigOperators Classical ComplexOrder Matrix.Norms.L2Operator

/-- The actual Euclidean Rayleigh quotient of the same encoded matrix. -/
theorem target_rayleigh {N : ℕ} (w : Fin N) (z : ℂ) (x : EuclideanSpace ℂ (System N)) :
    inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) (target w z) x)=
      2*star (x (.inl false))*x (.inl true)+2*z*star (x (.inr w))*x (.inr w) := by
  simp [PiLp.inner_apply,Matrix.ofLp_toEuclideanCLM,target,compressedTarget,
    Matrix.mulVec,dotProduct,RCLike.inner_apply,Fintype.sum_sum_type,
    Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower.jordan,Matrix.diagonal_apply,mul_comm,mul_left_comm]
  ring

/-- The restricted-access construction satisfies `target_unit_mass` under the complete displayed premises. -/
theorem target_unit_mass {N : ℕ} (x : EuclideanSpace ℂ (System N)) (hx : ‖x‖=1) :
    ‖x (.inl false)‖^2+‖x (.inl true)‖^2+(∑ j : Fin N,‖x (.inr j)‖^2)=1 := by
  have hh := EuclideanSpace.norm_sq_eq x
  simpa [hx,Fintype.sum_sum_type,add_comm,add_left_comm] using hh.symm

/-- The restricted-access construction satisfies `target_rayleigh_norm_bound` under the complete displayed premises. -/
theorem target_rayleigh_norm_bound {N : ℕ} (w : Fin N) (z : ℂ)
    (x : EuclideanSpace ℂ (System N)) (hx : ‖x‖=1) :
    ‖inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) (target w z) x)‖ ≤ max 1 (2*‖z‖) := by
  have hm := target_unit_mass x hx
  have hw : ‖x (.inr w)‖^2 ≤ ∑ j : Fin N,‖x (.inr j)‖^2 :=
    Finset.single_le_sum (fun (j : Fin N) _ => sq_nonneg ‖x (.inr j)‖) (Finset.mem_univ w)
  have htotal : ‖x (.inl false)‖^2+‖x (.inl true)‖^2+‖x (.inr w)‖^2 ≤ 1 := by linarith
  have h1 : (1 : ℝ) ≤ max 1 (2*‖z‖) := le_max_left _ _
  have h2 : 2*‖z‖ ≤ max 1 (2*‖z‖) := le_max_right _ _
  rw [target_rayleigh]
  calc
    _  ≤  ‖2*star (x (.inl false))*x (.inl true)‖+‖2*z*star (x (.inr w))*x (.inr w)‖ := norm_add_le _ _
    _ = 2*‖x (.inl false)‖*‖x (.inl true)‖+2*‖z‖*‖x (.inr w)‖^2 := by
      simp only [norm_mul,norm_star]
      norm_num; ring
    _  ≤  (‖x (.inl false)‖^2+‖x (.inl true)‖^2)+2*‖z‖*‖x (.inr w)‖^2 := by
      nlinarith [sq_nonneg (‖x (.inl false)‖-‖x (.inl true)‖)]
    _  ≤  max 1 (2*‖z‖)*(‖x (.inl false)‖^2+‖x (.inl true)‖^2+‖x (.inr w)‖^2) := by
      have ha := mul_le_mul_of_nonneg_right h1 (add_nonneg (sq_nonneg ‖x (.inl false)‖) (sq_nonneg ‖x (.inl true)‖))
      have hb := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖x (.inr w)‖)
      nlinarith
    _  ≤  max 1 (2*‖z‖)*1 := mul_le_mul_of_nonneg_left htotal (by linarith)
    _ = _ := mul_one _

/-- Construction for mark Vector in the marked halmos range model. -/
def markVector {N : ℕ} (w : Fin N) : EuclideanSpace ℂ (System N) :=
  toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket (.inr w))

/-- The restricted-access construction satisfies `markVector_norm` under the complete displayed premises. -/
theorem markVector_norm {N : ℕ} (w : Fin N) : ‖markVector w‖=1 :=
  (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _)

/-- The restricted-access construction satisfies `markVector_rayleigh` under the complete displayed premises. -/
theorem markVector_rayleigh {N : ℕ} (w : Fin N) (z : ℂ) :
    inner ℂ (markVector w) (Matrix.toEuclideanCLM (𝕜 := ℂ) (target w z) (markVector w))=2*z := by
  rw [target_rayleigh]
  simp [markVector,toEuclidean_fromVec,Qatlib.Foundations.PureStateMath.Ket]

/-- Construction for core Vector in the marked halmos range model. -/
def coreVector {N : ℕ} (u : ℂ) : EuclideanSpace ℂ (System N) :=
  WithLp.toLp 2 (fun s => match s with
    | .inl b => if b then u*((Real.sqrt 2/2 : ℝ) : ℂ) else ((Real.sqrt 2/2 : ℝ) : ℂ)
    | .inr _ => 0)

/-- The restricted-access construction satisfies `coreVector_norm` under the complete displayed premises. -/
theorem coreVector_norm {N : ℕ} (u : ℂ) (hu : ‖u‖=1) : ‖coreVector (N := N) u‖=1 := by
  have he : ‖coreVector (N := N) u‖^2=1 := by
    simp [EuclideanSpace.norm_sq_eq,coreVector,Fintype.sum_sum_type,
      hu,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg 2)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [norm_nonneg (coreVector (N := N) u)]

/-- The restricted-access construction satisfies `coreVector_rayleigh` under the complete displayed premises. -/
theorem coreVector_rayleigh {N : ℕ} (w : Fin N) (z u : ℂ) :
    inner ℂ (coreVector u) (Matrix.toEuclideanCLM (𝕜 := ℂ) (target w z) (coreVector u))=u := by
  rw [target_rayleigh]
  simp [coreVector]
  have hh : ((Real.sqrt 2 : ℝ) : ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  linear_combination (u/2)*hh

/-- The restricted-access construction satisfies `target_mark_point` under the complete displayed premises. -/
theorem target_mark_point {N : ℕ} (w : Fin N) (z : ℂ) : 2*z∈Qatlib.Foundations.OpCalculus.ContourCalc.matrixNumericalRange (target w z) :=
  ⟨markVector w,markVector_norm w,markVector_rayleigh w z⟩

/-- The restricted-access construction satisfies `target_unit_point` under the complete displayed premises. -/
theorem target_unit_point {N : ℕ} (w : Fin N) (z u : ℂ) (hu : ‖u‖=1) : u∈Qatlib.Foundations.OpCalculus.ContourCalc.matrixNumericalRange (target w z) :=
  ⟨coreVector u,coreVector_norm u hu,coreVector_rayleigh w z u⟩

/-- The restricted-access construction satisfies `target_actual_maximum` under the complete displayed premises. -/
theorem target_actual_maximum {N : ℕ} (w : Fin N) (z : ℂ) :
    IsGreatest ((fun a : ℂ => ‖a‖) '' Qatlib.Foundations.OpCalculus.ContourCalc.matrixNumericalRange (target w z)) (max 1 (2*‖z‖)) := by
  refine ⟨?_,?_⟩
  · by_cases hz : 1 ≤ 2*‖z‖
    · refine ⟨2*z,target_mark_point w z,?_⟩
      simp [max_eq_right hz]
    · refine ⟨1,target_unit_point w z 1 (by norm_num),?_⟩
      simp [max_eq_left (le_of_lt (lt_of_not_ge hz))]
  · rintro y ⟨a,ha,rfl⟩
    obtain ⟨x,hx,rfl⟩ := ha
    exact target_rayleigh_norm_bound w z x hx


/-- The restricted-access construction satisfies `target_rayleigh_support_bound` under the complete displayed premises. -/
theorem target_rayleigh_support_bound {N : ℕ} (w : Fin N) (z u : ℂ) (hu : ‖u‖=1)
    (x : EuclideanSpace ℂ (System N)) (hx : ‖x‖=1) :
    (star u*inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) (target w z) x)).re ≤
      max 1 (star u*(2*z)).re := by
  have hm := target_unit_mass x hx
  have hw : ‖x (.inr w)‖^2 ≤ ∑ j : Fin N,‖x (.inr j)‖^2 :=
    Finset.single_le_sum (fun (j : Fin N) _ => sq_nonneg ‖x (.inr j)‖) (Finset.mem_univ w)
  have htotal : ‖x (.inl false)‖^2+‖x (.inl true)‖^2+‖x (.inr w)‖^2 ≤ 1 := by linarith
  have hcore : (star u*(2*star (x (.inl false))*x (.inl true))).re ≤
      ‖x (.inl false)‖^2+‖x (.inl true)‖^2 := by
    apply (Complex.re_le_norm _).trans
    simp only [norm_mul,norm_star,hu]
    norm_num
    nlinarith [sq_nonneg (‖x (.inl false)‖-‖x (.inl true)‖)]
  have hs : star (x (.inr w))*x (.inr w)=((‖x (.inr w)‖^2 : ℝ) : ℂ) := by
    change (starRingEnd ℂ) (x (.inr w))*x (.inr w)=_
    rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  have hmark : (star u*(2*z*star (x (.inr w))*x (.inr w))).re=
      (star u*(2*z)).re*‖x (.inr w)‖^2 := by
    have he : star u*(2*z*star (x (.inr w))*x (.inr w))=
        (star u*(2*z))*(star (x (.inr w))*x (.inr w)) := by ring
    rw [he,hs]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have h1 : (1 : ℝ) ≤ max 1 (star u*(2*z)).re := le_max_left _ _
  have h2 : (star u*(2*z)).re ≤ max 1 (star u*(2*z)).re := le_max_right _ _
  rw [target_rayleigh,mul_add,Complex.add_re,hmark]
  calc
    _ ≤ (‖x (.inl false)‖^2+‖x (.inl true)‖^2)+(star u*(2*z)).re*‖x (.inr w)‖^2 :=
      add_le_add hcore le_rfl
    _ ≤ max 1 (star u*(2*z)).re*(‖x (.inl false)‖^2+‖x (.inl true)‖^2+‖x (.inr w)‖^2) := by
      have ha := mul_le_mul_of_nonneg_right h1 (add_nonneg (sq_nonneg ‖x (.inl false)‖) (sq_nonneg ‖x (.inl true)‖))
      have hb := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖x (.inr w)‖)
      nlinarith
    _ ≤ max 1 (star u*(2*z)).re*1 := mul_le_mul_of_nonneg_left htotal (by linarith)
    _ = _ := mul_one _

/-- The restricted-access construction satisfies `target_actual_support` under the complete displayed premises. -/
theorem target_actual_support {N : ℕ} (w : Fin N) (z u : ℂ) (hu : ‖u‖=1) :
    IsGreatest ((fun a : ℂ => (star u*a).re) '' Qatlib.Foundations.OpCalculus.ContourCalc.matrixNumericalRange (target w z))
      (max 1 (star u*(2*z)).re) := by
  refine ⟨?_,?_⟩
  · by_cases hc : 1 ≤ (star u*(2*z)).re
    · exact ⟨2*z,target_mark_point w z,by rw [max_eq_right hc]⟩
    · refine ⟨u,target_unit_point w z u hu,?_⟩
      have hunit : star u*u=1 := by
        change (starRingEnd ℂ) u*u=(1 : ℂ)
        rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hu]
        norm_num
      change (star u*u).re=max 1 (star u*(2*z)).re
      rw [hunit,max_eq_left (le_of_lt (lt_of_not_ge hc))]
      norm_num
  · rintro y ⟨a,ha,rfl⟩
    obtain ⟨x,hx,rfl⟩ := ha
    exact target_rayleigh_support_bound w z u hu x hx
end Qatlib.Papers.CrouzeixLS26.AccessLower.MarkedHalmos
