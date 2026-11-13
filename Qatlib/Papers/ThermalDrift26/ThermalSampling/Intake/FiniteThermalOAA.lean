/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.FiniteThermalRotationWord
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-!
# Thermal Amplification Error Identities

This module supplies algebraic identities and error estimates for the finite thermal preparation
used in [JiangEtAl2026]. `thermalOAA_polynomial` works in an arbitrary ring, and the real
coefficient lemmas analyze the amplification factor `(3 - (c^2 + s^2))/2`.

`thermalWord_full_error_identity` expresses the full state error through its two clean
amplitudes. The subsequent results turn coordinate under-approximation bounds into a bound for
`cleanWordErrorSq` and then into a joint classical and quantum source error.

## Main statements

- `thermalOAA_polynomial` expands the reflected amplification word inside an idempotent corner.
* `thermalAmplified_error_bound` bounds the amplified coefficient and leakage expression by
  `6*e^2`.
- `thermalWord_hclean_of_coefficients` proves a full preparation error bound for a legal word.
* `thermalWord_source_cq_of_coefficients` adds the index-distribution error to the preparation
  error.

## References

* [Jiang et al., 2026][JiangEtAl2026], *Thermal-Drift Sampling: Generating Thermal Ensembles for
  Learning Many-Body Systems*.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix
open scoped BigOperators

/-- In any ring, mutually inverse `U,V` and an idempotent `P` satisfy
`P*(-(U*(1-2*P)*V*(1-2*P)*U))*P = 3*(P*U*P) - 4*(P*U*P*V*P*U*P)`. -/
theorem thermalOAA_polynomial {R : Type*} [Ring R] (U V P : R)
    (hUV : U*V=1) (hVU : V*U=1) (hP : P*P=P) :
    P * (-(U*(1-2*P)*V*(1-2*P)*U)) * P =
      3*(P*U*P)-4*(P*U*P*V*P*U*P) := by
  have hUVU : U*V*U=U := by rw [hUV,one_mul]
  calc
    _ = -(P*(U*V*U)*P)+2*(P*U*P*(V*U)*P)+
        2*(P*(U*V)*P*U*P)-4*(P*U*P*V*P*U*P) := by noncomm_ring
    _ = _ := by
      rw [hUVU,hUV,hVU]
      simp only [mul_one]
      simp only [mul_assoc,hP]
      noncomm_ring

/-- An intertwining relation `U*G = G*u` implies `V*G = G*v` when `V*U = 1` and `u*v = 1`, even
if the two matrix spaces have different dimensions. -/
theorem thermalInverse_intertwine {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (U V : Matrix I I ℂ) (u v : Matrix J J ℂ)
    (G : Matrix I J ℂ) (hVU : V*U=1) (huv : u*v=1) (hUG : U*G=G*u) :
    V*G=G*v := by
  calc
    V*G=V*(G*(u*v)) := by rw [huv,Matrix.mul_one]
    _=V*((G*u)*v) := by rw [Matrix.mul_assoc]
    _=V*((U*G)*v) := by rw [hUG]
    _=(V*U)*G*v := by simp only [Matrix.mul_assoc]
    _=G*v := by rw [hVU,Matrix.one_mul]

/-- For `k = c^2 + s^2` and `gamma = (3-k)/2`, the identity `gamma^2*k + (1-k)^2*(4-k)/4 = 1`
separates the amplified coefficient mass from its complementary term. -/
theorem thermalAmplified_coefficients (c s : ℝ) :
    let k := c^2+s^2
    let gamma := (3-k)/2
    gamma^2*k+(1-k)^2*(4-k)/4=1 := by
  dsimp
  ring

/-- For a unit target `(C,S)`, the amplified coefficient error plus `(1-k)^2*(4-k)/4` equals
`2*r^2 + q - r*q`, where `k = c^2+s^2`, `r = C*(C-c)+S*(S-s)`, and `q = (C-c)^2+(S-s)^2`. -/
theorem thermalAmplified_full_error (C S c s : ℝ) (hunit : C^2+S^2=1) :
    let k := c^2+s^2
    let gamma := (3-k)/2
    (gamma*c-C)^2+(gamma*s-S)^2+(1-k)^2*(4-k)/4=
      2*(C*(C-c)+S*(S-s))^2+
        ((C-c)^2+(S-s)^2)-(C*(C-c)+S*(S-s))*((C-c)^2+(S-s)^2) := by
  dsimp
  linear_combination (C*c+S*s+c^2+s^2-C^2-S^2-1)*hunit

/-- If `(C,S)` is a nonnegative unit vector and both coordinate deficits `C-c` and `S-s` lie
between zero and `e`, the amplified coefficient error plus `(1-k)^2*(4-k)/4` is at most
`6*e^2`, with `k = c^2+s^2`. -/
theorem thermalAmplified_error_bound (C S c s e : ℝ) (hunit : C^2+S^2=1)
    (hC : 0≤C) (hS : 0≤S) (hc : 0≤C-c) (hs : 0≤S-s)
    (hcE : C-c≤e) (hsE : S-s≤e) :
    let k := c^2+s^2
    let gamma := (3-k)/2
    (gamma*c-C)^2+(gamma*s-S)^2+(1-k)^2*(4-k)/4≤6*e^2 := by
  dsimp
  rw [thermalAmplified_full_error C S c s hunit]
  have he : 0≤e := hc.trans hcE
  have hr : 0≤C*(C-c)+S*(S-s) := add_nonneg (mul_nonneg hC hc) (mul_nonneg hS hs)
  have hq : 0≤(C-c)^2+(S-s)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hid : (C*(C-c)+S*(S-s))^2+(C*(S-s)-S*(C-c))^2=
      (C^2+S^2)*((C-c)^2+(S-s)^2) := by ring
  rw [hunit,one_mul] at hid
  have hcs : (C*(C-c)+S*(S-s))^2≤(C-c)^2+(S-s)^2 := by nlinarith [sq_nonneg (C*(S-s)-S*(C-c))]
  have hce : (C-c)^2≤e^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcE) (add_nonneg he hc)]
  have hse : (S-s)^2≤e^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsE) (add_nonneg he hs)]
  nlinarith [mul_nonneg hr hq]

/-- For a legal word whose clean signal amplitudes are the real numbers `p,q`, the full squared
vector error against `targetWordState w a` is `2 - 2*(p*directCos a + q*directSin a)`. -/
theorem thermalWord_full_error_identity (w : ℕ) (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode)
    (hlegal : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal (w+1) gs=true) (a p q : ℝ)
    (h0 : splitWordState w gs (0,fun _ => false)=(p:ℂ))
    (h1 : splitWordState w gs (1,fun _ => false)=(q:ℂ)) :
    cleanWordErrorSq w gs a=2-2*(p*directCos a+q*directSin a) := by
  have hu : (∑ x,Complex.normSq (splitWordState w gs x))=1 := by
    simpa only [Complex.normSq_eq_norm_sq,Qatlib.Foundations.PureStateMath.Normalized] using
        splitWordState_normalized w gs hlegal
  have hv : (∑ x,Complex.normSq (targetWordState w a x))=1 := by
    simp [targetWordState,Qatlib.Foundations.PureStateMath.TensorState,rotationVector,Qatlib.Foundations.PureStateMath.Ket,
      Fintype.sum_prod_type,Fin.sum_univ_two,Complex.normSq_eq_norm_sq,
      Complex.norm_real,Real.norm_eq_abs,sq_abs,direct_rotation_normalized,apply_ite]
  have hc : (∑ x, (splitWordState w gs x * starRingEnd ℂ (targetWordState w a x)).re)=
      p*directCos a+q*directSin a := by
    simp [targetWordState,Qatlib.Foundations.PureStateMath.TensorState,rotationVector,Qatlib.Foundations.PureStateMath.Ket,
      Fintype.sum_prod_type,Fin.sum_univ_two,h0,h1,apply_ite]
  unfold cleanWordErrorSq
  simp only [Complex.normSq_sub]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hu,hv,hc]
  ring

/-- A legal word with clean amplitudes `gamma*c,gamma*s`, where `gamma = (3-(c^2+s^2))/2`, has
squared full-state error at most `epsilon^2` when `a >= 0`, the two target-coordinate
deficits lie in `[0,e]`, and `6*e^2 <= epsilon^2`. -/
theorem thermalWord_hclean_of_coefficients (w : ℕ) (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode)
    (hlegal : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal (w+1) gs=true) (a c s e epsilon : ℝ) (ha : 0≤a)
    (hc : 0≤directCos a-c) (hs : 0≤directSin a-s)
    (hcE : directCos a-c≤e) (hsE : directSin a-s≤e)
    (h0 : splitWordState w gs (0,fun _ => false)=(((3-(c^2+s^2))/2*c:ℝ):ℂ))
    (h1 : splitWordState w gs (1,fun _ => false)=(((3-(c^2+s^2))/2*s:ℝ):ℂ))
    (heps : 6*e^2≤epsilon^2) : cleanWordErrorSq w gs a≤epsilon^2 := by
  have hC : 0≤directCos a := by unfold directCos; positivity
  have hS : 0≤directSin a := mul_nonneg ha hC
  have hb := thermalAmplified_error_bound (directCos a) (directSin a) c s e
    (direct_rotation_normalized a) hC hS hc hs hcE hsE
  dsimp at hb
  have hn := thermalAmplified_coefficients c s
  dsimp at hn
  have htarget := direct_rotation_normalized a
  rw [thermalWord_full_error_identity w gs hlegal a _ _ h0 h1]
  have hid : (((3-(c^2+s^2))/2)*c-directCos a)^2+
      (((3-(c^2+s^2))/2)*s-directSin a)^2+
      (1-(c^2+s^2))^2*(4-(c^2+s^2))/4=
      2-2*(((3-(c^2+s^2))/2*c)*directCos a+
        ((3-(c^2+s^2))/2*s)*directSin a) := by
    linear_combination hn+htarget
  rw [hid] at hb
  exact hb.trans heps

/-- Under the stated legality and amplified-coordinate hypotheses, with `a >= 0`, `epsilon >=
0`, `6*e^2 <= epsilon^2`, and index total variation at most `delta`, the joint prepared
readout differs from the ideal one by at most `epsilon + delta` in half trace norm. -/
theorem thermalWord_source_cq_of_coefficients {L d : ℕ} (F : ReflectionFamily L d)
    (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (w : ℕ) (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode)
    (hlegal : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal (w+1) gs=true) (a c s e epsilon delta : ℝ) (ha : 0≤a)
    (hc : 0≤directCos a-c) (hs : 0≤directSin a-s)
    (hcE : directCos a-c≤e) (hsE : directSin a-s≤e)
    (h0 : splitWordState w gs (0,fun _ => false)=(((3-(c^2+s^2))/2*c:ℝ):ℂ))
    (h1 : splitWordState w gs (1,fun _ => false)=(((3-(c^2+s^2))/2*s:ℝ):ℂ))
    (heps : 6*e^2≤epsilon^2) (heps0 : 0≤epsilon)
    (hindex : (1/2:ℝ)*(∑ j : Fin L,|q.prob j-p.prob j|)≤delta) :
    (1/2:ℝ)*Matrix.traceNorm
      (jointPreparedReadout F q rho (wordPreparationState w gs hlegal).val-
        idealJointReadoutMatrix F p a rho)≤epsilon+delta :=
  finiteWord_source_cq_budget F p q rho w gs hlegal a epsilon delta heps0
    (thermalWord_hclean_of_coefficients w gs hlegal a c s e epsilon ha hc hs hcE hsE h0 h1 heps) hindex

end Qatlib.Papers.ThermalDrift26.ThermalSampling
