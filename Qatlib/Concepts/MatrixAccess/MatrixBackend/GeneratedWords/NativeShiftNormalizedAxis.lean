/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeShiftRotationWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CopyEvolution.Discriminate
/-! The same comparison word prepares the normalized actual rounded-root
axis. Prefix-ratio identities and seven stage transitions retain the source
order, and the error conclusion consumes the actual generated vLogical.
This is not yet the probability/coefficient precision theorem. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `cayley_prefix_ratios` under the displayed hypotheses. -/
private theorem cayley_prefix_ratios (a r R : ℝ) (hr : 0<r) (hR : 0<R)
    (hsq : R^2=r^2+a^2) :
    (1-(a/(R+r))^2)/(1+(a/(R+r))^2)=r/R ∧
    (2*(a/(R+r)))/(1+(a/(R+r))^2)=a/R := by
  have hd : R+r≠0 := ne_of_gt (add_pos hR hr)
  constructor
  · field_simp [hd,ne_of_gt hR]
    linear_combination (R+r)*hsq
  · field_simp [hd,ne_of_gt hR]
    linear_combination a*hsq

/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `shiftPairGate_mulVec` under the displayed hypotheses. -/
theorem shiftPairGate_mulVec (i : Fin 7) (c s : ℝ) (v : Fin 8 → ℂ) (a : Fin 8) :
    (shiftPairGate i c s *ᵥ v) a=
      if a=0 then (c : ℂ)*v 0-(s : ℂ)*v i.succ else
      if a=i.succ then (s : ℂ)*v 0+(c : ℂ)*v i.succ else v a := by
  have he := congrFun (applyGate_relabelGate (finSuccEquiv 7).symm (weightTwoLevel i c s)
    (relabelState (finSuccEquiv 7) v)) a
  simp only [relabelState,Function.comp_apply,Equiv.symm_symm] at he
  change (shiftPairGate i c s *ᵥ v) a= _ at he
  rw [he]
  rw [ApplyGate,weightTwoLevel_mulVec]
  simp only [Function.comp_apply,finSuccEquiv_eq_none,finSuccEquiv_eq_some,finSuccEquiv_symm_none,
    finSuccEquiv_symm_some,Equiv.symm_apply_apply]


/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `prefix_square_succ` under the displayed hypotheses. -/
private theorem prefix_square_succ (a : Fin 8 → ℚ) (i : Fin 7) :
    (∑ j : Fin 8,if j.val ≤ i.succ.val then a j^2 else 0)=
      (∑ j : Fin 8,if j.val ≤ i.castSucc.val then a j^2 else 0)+a i.succ^2 := by
  have he (j : Fin 8) :
      (if j.val ≤ i.succ.val then a j^2 else 0)=
        (if j.val ≤ i.castSucc.val then a j^2 else 0)+
          (if j=i.succ then a j^2 else 0) := by
    by_cases hji : j=i.succ
    · subst j
      simp
    · have hv : j.val≠i.val+1 := by
        intro h
        exact hji (Fin.ext h)
      by_cases hj : j.val ≤ i.val
      · simp [hj,show j.val ≤ i.val+1 by omega,hji]
      · simp [hj,show ¬j.val ≤ i.val+1 by omega,hji]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

/-- Construction for shift Radius in the native shift normalized axis model. -/
def shiftRadius (α B x y : ℚ) (p : ℕ) (i : Fin 8) : ℝ :=
  Real.sqrt (shiftPrefix α B x y p i : ℝ)

/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `shiftRadius_pos` under the displayed hypotheses. -/
theorem shiftRadius_pos (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 8) :
    0<shiftRadius α B x y p i := by
  apply Real.sqrt_pos.mpr
  have hh : (1 : ℝ) ≤ shiftPrefix α B x y p i := by
    exact_mod_cast shiftPrefix_ge_one α B x y p hα hB hz i
  linarith

/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `shiftRadius_sq` under the displayed hypotheses. -/
theorem shiftRadius_sq (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 8) :
    (shiftRadius α B x y p i)^2=(shiftPrefix α B x y p i : ℝ) := by
  apply Real.sq_sqrt
  have hh := shiftPrefix_ge_one α B x y p hα hB hz i
  exact_mod_cast (show 0 ≤ shiftPrefix α B x y p i by linarith)

/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `shiftRadius_step` under the displayed hypotheses. -/
theorem shiftRadius_step (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 7) :
    (shiftRadius α B x y p i.succ)^2=(shiftRadius α B x y p i.castSucc)^2+
      (shiftAxis α B x y p i.succ : ℝ)^2 := by
  rw [shiftRadius_sq α B x y p hα hB hz,shiftRadius_sq α B x y p hα hB hz]
  exact_mod_cast prefix_square_succ (shiftAxis α B x y p) i

/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `shiftComparisonGate_ratios` under the displayed hypotheses. -/
theorem shiftComparisonGate_ratios (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 7) :
    shiftComparisonGate α B x y p i=shiftPairGate i
      (shiftRadius α B x y p i.castSucc/shiftRadius α B x y p i.succ)
      ((shiftAxis α B x y p i.succ : ℝ)/shiftRadius α B x y p i.succ) := by
  have hc := cayley_prefix_ratios (shiftAxis α B x y p i.succ : ℝ)
    (shiftRadius α B x y p i.castSucc) (shiftRadius α B x y p i.succ)
    (shiftRadius_pos α B x y p hα hB hz i.castSucc)
    (shiftRadius_pos α B x y p hα hB hz i.succ)
    (shiftRadius_step α B x y p hα hB hz i)
  dsimp only [shiftComparisonGate,shiftIdealCircleValue,shiftIdealHalf]
  change shiftPairGate i
    ((1-((shiftAxis α B x y p i.succ : ℝ)/
      (shiftRadius α B x y p i.succ+shiftRadius α B x y p i.castSucc))^2)/
      (1+((shiftAxis α B x y p i.succ : ℝ)/
      (shiftRadius α B x y p i.succ+shiftRadius α B x y p i.castSucc))^2))
    (2*((shiftAxis α B x y p i.succ : ℝ)/
      (shiftRadius α B x y p i.succ+shiftRadius α B x y p i.castSucc))/
      (1+((shiftAxis α B x y p i.succ : ℝ)/
      (shiftRadius α B x y p i.succ+shiftRadius α B x y p i.castSucc))^2))=_
  rw [hc.1,hc.2]


/-- Construction for prefix Stage in the native shift normalized axis model. -/
private def prefixStage (a R : Fin 8 → ℝ) (k : Fin 8) : Fin 8 → ℂ := fun j =>
  if j=0 then (R k/R 7 : ℝ) else if k.val<j.val then (a j/R 7 : ℝ) else 0

/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `prefixStage_step` under the displayed hypotheses. -/
private theorem prefixStage_step (a R : Fin 8 → ℝ) (i : Fin 7) (hRi : R i.succ≠0) :
    shiftPairGate i (R i.castSucc/R i.succ) (a i.succ/R i.succ) *ᵥ
      prefixStage a R i.succ=prefixStage a R i.castSucc := by
  funext j
  rw [shiftPairGate_mulVec]
  have hne : i.succ≠0 := Fin.succ_ne_zero i
  have hRiC : (R i.succ : ℂ)≠0 := by exact_mod_cast hRi
  by_cases hj : j=0
  · subst j
    simp only [prefixStage,Fin.succ_ne_zero,ite_false,lt_self_iff_false,
      mul_zero,sub_zero]
    push_cast
    field_simp [hRiC]
  · by_cases hij : j=i.succ
    · subst j
      simp only [prefixStage,ite_eq_right hne,lt_self_iff_false,ite_false,
        Fin.val_castSucc,Fin.val_succ,Nat.lt_add_one,mul_zero,add_zero]
      push_cast
      field_simp [hRiC]
    · have hlt : i.succ.val<j.val ↔ i.castSucc.val<j.val := by
        have hn : j.val≠i.val+1 := by intro h; exact hij (Fin.ext h)
        simp only [Fin.val_succ,Fin.val_castSucc]
        omega
      simp only [hj,hij,ite_false,prefixStage,hlt]

/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `prefixStage_start` under the displayed hypotheses. -/
private theorem prefixStage_start (a R : Fin 8 → ℝ) (hR : R 7≠0) :
    prefixStage a R 7=Qatlib.Foundations.PureStateMath.Ket 0 := by
  funext j
  by_cases hj : j=0
  · subst j
    simp [prefixStage,Qatlib.Foundations.PureStateMath.Ket,hR]
  · have hlt : ¬7<j.val := by have hh := j.isLt; omega
    simp [prefixStage,Qatlib.Foundations.PureStateMath.Ket,hj,hlt]

/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `prefixStage_finish` under the displayed hypotheses. -/
private theorem prefixStage_finish (a R : Fin 8 → ℝ) (hR0 : R 0=a 0) :
    prefixStage a R 0=(fun j => (a j/R 7 : ℂ)) := by
  funext j
  by_cases hj : j=0
  · subst j
    simp [prefixStage,hR0]
  · simp [prefixStage,hj,Complex.ofReal_div]


/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `shiftRadius_zero` under the displayed hypotheses. -/
theorem shiftRadius_zero (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    shiftRadius α B x y p 0=(shiftAxis α B x y p 0 : ℝ) := by
  have hp : shiftPrefix α B x y p 0=(shiftAxis α B x y p 0)^2 := by
    simp [shiftPrefix]
  have ha : (0 : ℝ) ≤ shiftAxis α B x y p 0 := by
    exact_mod_cast (shiftAxis_bounds α B x y p hα hB hz).2.1 0
  simp only [shiftRadius,hp,Rat.cast_pow,Real.sqrt_sq ha]

/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `shiftComparisonLogical_axis` under the displayed hypotheses. -/
theorem shiftComparisonLogical_axis (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    shiftComparisonLogical α B x y p *ᵥ Qatlib.Foundations.PureStateMath.Ket 0=
      fun j => (shiftAxis α B x y p j : ℂ)/(shiftRadius α B x y p 7 : ℂ) := by
  let a : Fin 8 → ℝ := fun j => shiftAxis α B x y p j
  let R := shiftRadius α B x y p
  have hs (i : Fin 7) :
      shiftComparisonGate α B x y p i *ᵥ prefixStage a R i.succ=
        prefixStage a R i.castSucc := by
    rw [shiftComparisonGate_ratios α B x y p hα hB hz]
    exact prefixStage_step a R i (ne_of_gt (shiftRadius_pos α B x y p hα hB hz i.succ))
  have hstart := prefixStage_start a R (ne_of_gt (shiftRadius_pos α B x y p hα hB hz 7))
  have hfinish := prefixStage_finish a R (shiftRadius_zero α B x y p hα hB hz)
  have hlist : (List.finRange 7).reverse=[6,5,4,3,2,1,0] := rfl
  rw [shiftComparisonLogical,hlist]
  simp only [shiftComparisonProduct,Matrix.one_mul,←Matrix.mulVec_mulVec]
  have h6 : shiftComparisonGate α B x y p 6 *ᵥ prefixStage a R 7=prefixStage a R 6 := by
    simpa using hs (6 : Fin 7)
  have h5 : shiftComparisonGate α B x y p 5 *ᵥ prefixStage a R 6=prefixStage a R 5 := by
    simpa using hs (5 : Fin 7)
  have h4 : shiftComparisonGate α B x y p 4 *ᵥ prefixStage a R 5=prefixStage a R 4 := by
    simpa using hs (4 : Fin 7)
  have h3 : shiftComparisonGate α B x y p 3 *ᵥ prefixStage a R 4=prefixStage a R 3 := by
    simpa using hs (3 : Fin 7)
  have h2 : shiftComparisonGate α B x y p 2 *ᵥ prefixStage a R 3=prefixStage a R 2 := by
    simpa using hs (2 : Fin 7)
  have h1 : shiftComparisonGate α B x y p 1 *ᵥ prefixStage a R 2=prefixStage a R 1 := by
    simpa using hs (1 : Fin 7)
  have h0 : shiftComparisonGate α B x y p 0 *ᵥ prefixStage a R 1=prefixStage a R 0 := by
    simpa using hs (0 : Fin 7)
  rw [←hstart,h6,h5,h4,h3,h2,h1,h0]
  exact hfinish


/-- The generated word's first column approximates the normalized actual
rounded-root axis, not a free ideal preparation parameter. -/
theorem nativeShiftAxis_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    ‖toEuclidean_fromVec (fun j =>
      Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.vLogical (nativeShiftCircles α B x y p) j 0-
        (shiftAxis α B x y p j : ℂ)/(shiftRadius α B x y p 7 : ℂ))‖ ≤
      7/(2 : ℝ)^(p+12) := by
  let V := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.vLogical (nativeShiftCircles α B x y p)
  let W := shiftComparisonLogical α B x y p
  have he := Qatlib.Concepts.ReferenceError.RefTraceError.l2_norm_mulVec_fromVec_le (V-W) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8))
  have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8))‖=1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _)
  rw [hk,mul_one] at he
  have hw := shiftComparisonLogical_axis α B x y p hα hB hz
  have hcol : (V-W)*ᵥKet 0=(fun j =>
      V j 0-(shiftAxis α B x y p j : ℂ)/(shiftRadius α B x y p 7 : ℂ)) := by
    rw [Matrix.sub_mulVec,hw]
    funext j
    simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]
  rw [hcol] at he
  exact he.trans (nativeShiftLogical_error α B x y p hα hB hz)


/-- The finite construction in `NativeShiftNormalizedAxis` satisfies `shiftRadius_total_norm` under the displayed hypotheses. -/
theorem shiftRadius_total_norm (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    shiftRadius α B x y p 7=
      ‖toEuclidean_fromVec (fun j => (shiftAxis α B x y p j : ℂ))‖ := by
  have hp : shiftPrefix α B x y p 7=∑ j : Fin 8,shiftAxis α B x y p j^2 := by
    apply Finset.sum_congr rfl
    intro j _
    have hj : j.val ≤ (7 : Fin 8).val := by have hh := j.isLt; change j.val ≤ 7; omega
    exact ite_eq_left hj
  have he := shiftRadius_sq α B x y p hα hB hz (7 : Fin 8)
  rw [hp,Rat.cast_sum] at he
  have hn := norm_toEuclidean_fromVec_sq (fun j => (shiftAxis α B x y p j : ℂ))
  have hs (j : Fin 8) : ‖(shiftAxis α B x y p j : ℂ)‖^2=((shiftAxis α B x y p j)^2 : ℚ) := by
    rw [←Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs,sq_abs,Rat.cast_pow]
  simp_rw [hs] at hn
  nlinarith [norm_nonneg (toEuclidean_fromVec (fun j => (shiftAxis α B x y p j : ℂ))),
    shiftRadius_pos α B x y p hα hB hz 7]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
