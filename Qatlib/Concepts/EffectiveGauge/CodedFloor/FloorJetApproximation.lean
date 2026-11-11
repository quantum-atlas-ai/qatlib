/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorJetSyntax
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorFlatApproximation
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorProgramAmplitude
import Qatlib.Concepts.EffectiveGauge.RationalFlow.CisApproximation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Jet Approximation

Coded Floor constructions for Effective Gauge.
Defines `floorRationalBumpArgument`, `floorJetApproximation`.
Proves `floorProgramAmplitude_abs_le_one`, `floorRationalBumpArgument_cast`, `floorJetProduct_error`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of floor Rational Bump Argument in the Coded Floor construction. -/
def floorRationalBumpArgument (X : Fin 3 → ℚ) : ℚ :=
  1-∑ i : Fin 3, (X i-3)^2

/-- Definition of floor Jet Approximation in the Coded Floor construction. -/
def floorJetApproximation (c : Nat.Partrec.Code) (X : Fin 3 → ℚ) : FloorJetExpr → ℚ → ℚ
  | .integer z,_ => z
  | .coordinate i,_ => X i
  | .parameter,t => floorProgramAmplitudeApprox c (arctanFuel t)
  | .flat n,t => floorFlatApproximation n (floorRationalBumpArgument X) t
  | .add f g,t => floorJetApproximation c X f (t/2)+floorJetApproximation c X g (t/2)
  | .neg f,t => -floorJetApproximation c X f t
  | .mul f g,t =>
    let s := t/(2*((floorJetBound f : ℚ)+floorJetBound g+1))
    floorJetApproximation c X f s*floorJetApproximation c X g s
  | .sin f,t => (rationalCis (floorJetApproximation c X f (t/2)) (t/2)).value.2
  | .cos f,t => (rationalCis (floorJetApproximation c X f (t/2)) (t/2)).value.1

noncomputable section

/-- Original `floorProgramAmplitude_abs_le_one` guarantee for the `FloorJetApproximation` construction; the complete source hypotheses are retained. -/
theorem floorProgramAmplitude_abs_le_one (c : Nat.Partrec.Code) :
    |(floorProgramAmplitude c : ℝ)| ≤ 1 := by
  have hp : (0 : ℝ) ≤ floorProgramAmplitude c := by exact_mod_cast (floorProgramAmplitude_spec c).1
  rw [abs_of_nonneg hp]
  have h : (floorProgramAmplitude c : ℝ) ≤ ((1/16 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (floorProgramAmplitude_spec c).2.1
  norm_num at h
  linarith

/-- Original `floorRationalBumpArgument_cast` guarantee for the `FloorJetApproximation` construction; the complete source hypotheses are retained. -/
theorem floorRationalBumpArgument_cast (X : Fin 3 → ℚ) :
    (floorRationalBumpArgument X : ℝ)=floorBumpArgument (rationalSpatialPoint X) := by
  simp [floorRationalBumpArgument,floorBumpArgument,rationalSpatialPoint]

/-- Original `floorJetProduct_error` guarantee for the `FloorJetApproximation` construction; the complete source hypotheses are retained. -/
theorem floorJetProduct_error (f0 g0 f g F G t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hF : |f| ≤ F) (hG : |g| ≤ G)
    (hf : |f0-f| ≤ t) (hg : |g0-g| ≤ t) :
    |f0*g0-f*g| ≤ t*(F+G+1) := by
  have hF0 : 0 ≤ F := (abs_nonneg _).trans hF
  have hG0 : 0 ≤ G := (abs_nonneg _).trans hG
  have hf0 : |f0| ≤ F+t := by
    calc
      _ = |(f0-f)+f| := by ring_nf
      _ ≤ |f0-f|+|f| := abs_add_le _ _
      _ ≤ t+F := add_le_add hf hF
      _ = _ := by ring
  calc
    _ = |f0*(g0-g)+(f0-f)*g| := by congr 1; ring
    _ ≤ |f0*(g0-g)|+|(f0-f)*g| := abs_add_le _ _
    _ ≤ (F+t)*t+t*G := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul hf0 hg (abs_nonneg _) (by positivity))
        (mul_le_mul hf hG (abs_nonneg _) ht)
    _ ≤ t*(F+G+1) := by nlinarith

/-- Original `floorCis_components_error` guarantee for the `FloorJetApproximation` construction; the complete source hypotheses are retained. -/
theorem floorCis_components_error (x t : ℚ) (ht : 0<t) (ht1 : t ≤ 1) :
    |((rationalCis x t).value.1 : ℝ)-Real.cos (x : ℝ)| ≤ (t : ℝ) ∧
    |((rationalCis x t).value.2 : ℝ)-Real.sin (x : ℝ)| ≤ (t : ℝ) := by
  have hr := rationalCis_spec x t ht ht1
  have hb := hr.1.trans (by exact_mod_cast hr.2.2.1 :
    ((rationalCis x t).error : ℝ) ≤ (t : ℝ))
  exact ⟨by simpa [rationalCircleCast,complexPhase] using
      (Complex.abs_re_le_norm _).trans hb,
    by simpa [rationalCircleCast,complexPhase] using (Complex.abs_im_le_norm _).trans hb⟩

/-- Original `floorJetApproximation_error` guarantee for the `FloorJetApproximation` construction; the complete source hypotheses are retained. -/
theorem floorJetApproximation_error (e : FloorJetExpr) (c : Nat.Partrec.Code)
    (X : Fin 3 → ℚ) (hX : InFundamentalCube (rationalSpatialPoint X))
    (t : ℚ) (ht : 0<t) (ht1 : t ≤ 1) :
    |(floorJetApproximation c X e t : ℝ)-floorJetEval (floorProgramAmplitude c : ℝ)
      (rationalSpatialPoint X) e| ≤ (t : ℝ) := by
  induction e generalizing t with
  | integer z => simp [floorJetApproximation,floorJetEval,ht.le]
  | coordinate i => simp [floorJetApproximation,floorJetEval,rationalSpatialPoint,ht.le]
  | parameter =>
    have h := floorProgramAmplitudeApprox_error c (arctanFuel t)
    have hb : |((floorProgramAmplitudeApprox c (arctanFuel t)-floorProgramAmplitude c : ℚ) : ℝ)| ≤
        ((1/(2 : ℚ)^arctanFuel t : ℚ) : ℝ) := by exact_mod_cast h
    have hbudget : (1/(2 : ℚ)^arctanFuel t) ≤ t := by
      simpa only [one_div] using arctanFuel_budget t ht
    have hb' := hb.trans (Rat.cast_le.mpr hbudget)
    simpa only [floorJetApproximation,floorJetEval,Rat.cast_sub] using hb'
  | flat n =>
    simpa only [floorJetApproximation,floorJetEval,floorRationalBumpArgument_cast] using
      floorFlatApproximation_error n (floorRationalBumpArgument X) t ht
  | add f g hf hg =>
    have h0 : 0<t/2 := by positivity
    have h1 : t/2 ≤ 1 := by linarith
    have h := add_le_add (hf (t/2) h0 h1) (hg (t/2) h0 h1)
    calc
      _ = |((floorJetApproximation c X f (t/2) : ℝ)-floorJetEval (floorProgramAmplitude c : ℝ) (rationalSpatialPoint X) f)+
        ((floorJetApproximation c X g (t/2) : ℝ)-floorJetEval (floorProgramAmplitude c : ℝ) (rationalSpatialPoint X) g)| := by
          simp only [floorJetApproximation,floorJetEval,Rat.cast_add]; congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans h
      _ = _ := by push_cast; ring
  | neg f hf =>
    simp only [floorJetApproximation,floorJetEval,Rat.cast_neg,neg_sub_neg,abs_sub_comm]
    exact hf t ht ht1
  | mul f g hf hg =>
    let s : ℚ := t/(2*((floorJetBound f : ℚ)+floorJetBound g+1))
    have hs : 0<s := by dsimp [s]; positivity
    have hs1 : s ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℚ)<2*((floorJetBound f : ℚ)+floorJetBound g+1))).mpr
      have hf0 : (0 : ℚ) ≤ floorJetBound f := by positivity
      have hg0 : (0 : ℚ) ≤ floorJetBound g := by positivity
      linarith
    have hm := floorJetProduct_error _ _ _ _ (floorJetBound f) (floorJetBound g) (s : ℝ)
      (Rat.cast_nonneg.mpr hs.le) (by exact_mod_cast hs1)
      (floorJetBound_correct f _ (floorProgramAmplitude_abs_le_one c) _ hX)
      (floorJetBound_correct g _ (floorProgramAmplitude_abs_le_one c) _ hX)
      (hf s hs hs1) (hg s hs hs1)
    have hb : (s : ℝ)*((floorJetBound f : ℝ)+floorJetBound g+1) ≤ (t : ℝ) := by
      have he : s*((floorJetBound f : ℚ)+floorJetBound g+1)=t/2 := by dsimp [s]; field_simp
      have heR := congrArg (fun q : ℚ => (q : ℝ)) he
      push_cast at heR
      rw [heR]
      have htR : (0 : ℝ)<t := Rat.cast_pos.mpr ht
      linarith
    simpa only [floorJetApproximation,floorJetEval,Rat.cast_mul,s] using hm.trans hb
  | sin f hf =>
    have h0 : 0<t/2 := by positivity
    have h1 : t/2 ≤ 1 := by linarith
    have hc := (floorCis_components_error (floorJetApproximation c X f (t/2)) (t/2) h0 h1).2
    have hs := (Real.abs_sin_sub_sin_le _ _).trans (hf (t/2) h0 h1)
    have hh := (abs_sub_le _ _ _).trans (add_le_add hc hs)
    simpa only [floorJetApproximation,floorJetEval,Rat.cast_div,Rat.cast_ofNat,add_halves] using hh
  | cos f hf =>
    have h0 : 0<t/2 := by positivity
    have h1 : t/2 ≤ 1 := by linarith
    have hc := (floorCis_components_error (floorJetApproximation c X f (t/2)) (t/2) h0 h1).1
    have hs := (Real.abs_cos_sub_cos_le _ _).trans (hf (t/2) h0 h1)
    have hh := (abs_sub_le _ _ _).trans (add_le_add hc hs)
    simpa only [floorJetApproximation,floorJetEval,Rat.cast_div,Rat.cast_ofNat,add_halves] using hh

end
end Qatlib.Concepts.EffectiveGauge.CodedFloor
