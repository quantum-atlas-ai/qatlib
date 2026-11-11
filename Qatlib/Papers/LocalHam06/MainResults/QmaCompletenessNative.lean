/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessGates
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeOutput
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeLocality
import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessEnergy

/-!
# Semantics of native gate coefficients

The interpretation `taggedValue` connects symbolic gate entries to their complex matrix values.
The module identifies rounded integer coefficients with rounded gates and proves that
`propagationTerm_value` is the flattened physical propagation operator. See
[KempeKitaevRegev2006].

## Main statements

* `rawTag_sound`: Interpreting `rawTag` gives the matrix entry specified by the finite gate
  code.
* `rawCoeff_interpret`: The dyadic interpretation of `rawCoeff` equals the corresponding entry
  of `qmaRoundedGate`.
* `propagationTerm_value`: The value of a propagation term at width `b + 1` is the physical
  propagation matrix reindexed by the flattening equivalence.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

set_option autoImplicit false
open scoped Classical

namespace Qatlib.Papers.LocalHam06.MainResults
open Qatlib
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The complex value of a symbolic tag, obtained by interpreting its real and imaginary atoms. -/
noncomputable def taggedValue (p : Tag) : ℂ := cartesian p.1 p.2

/-- The zero tag has complex value zero. -/
theorem zeroTag_sound : taggedValue zeroTag = 0 := by
  simp [taggedValue, zeroTag, cartesian, atomVal]

/-- The unit tag has complex value one. -/
theorem oneTag_sound : taggedValue oneTag = 1 := by
  simp [taggedValue, oneTag, cartesian, atomVal]

/-- The identity tag evaluates to the corresponding entry of the identity matrix. -/
theorem identityTag_sound {n : ℕ} (x y : Reg n) :
    taggedValue (identityTag x y) = (1 : Matrix (Reg n) (Reg n) ℂ) x y := by
  by_cases h : x = y
  · rw [identityTag, if_pos ((regEq_true_iff x y).mpr h), oneTag_sound]
    exact (Matrix.one_apply_eq _).symm.trans (by subst y; rfl)
  · have hb : ¬ regEq x y = true := fun hh => h ((regEq_true_iff x y).mp hh)
    simp [identityTag, hb, h, zeroTag_sound]

/-- A symbolic Hadamard cell evaluates to the corresponding Hadamard matrix entry. -/
theorem hCell_sound (a c : Bool) : taggedValue (hCell a c) = Hadamard a c := by
  cases a <;> cases c <;>
    simp [taggedValue, hCell, cartesian, atomVal, Hadamard]

/-- A symbolic Pauli X cell evaluates to the corresponding Pauli X matrix entry. -/
theorem xCell_sound (a c : Bool) : taggedValue (xCell a c) = PauliX a c := by
  cases a <;> cases c <;>
    simp [taggedValue, xCell, oneTag, zeroTag, cartesian, atomVal, PauliX, permMatrix]

/-- The real number `sqrt 2 / 2` equals the reciprocal of `sqrt 2`. -/
theorem sqrt_two_div_two_eq_inv : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  apply mul_right_cancel₀ hs
  rw [inv_mul_cancel₀ hs]
  have hh := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/-- A symbolic T cell evaluates to the corresponding entry of `tGate`. -/
theorem tCell_sound (a c : Bool) : taggedValue (tCell a c) = tGate a c := by
  cases a <;> cases c <;>
    simp [taggedValue, tCell, oneTag, zeroTag, cartesian, atomVal, tGate, Rz]
  apply Complex.ext
  · simpa using! exp_pi_div_four_re_im.1.symm
  · simpa using! exp_pi_div_four_re_im.2.symm

/-- A symbolic adjoint T cell evaluates to the corresponding entry of `tGateAdj`. -/
theorem tdgCell_sound (a c : Bool) : taggedValue (tdgCell a c) = tGateAdj a c := by
  cases a <;> cases c <;>
    simp [taggedValue, tdgCell, oneTag, zeroTag, cartesian, atomVal, tGateAdj, Rz]
  apply Complex.ext
  · simpa using! exp_neg_pi_div_four_re_im.1.symm
  · simpa [sqrt_two_div_two_eq_inv] using! exp_neg_pi_div_four_re_im.2.symm

/-- Interpreting a one-wire tag gives the entry of the embedded gate when the wire is in range,
and the identity entry otherwise. -/
theorem oneWireTag_sound (n w : ℕ) (cell : Bool → Bool → Tag)
    (U : Matrix Bool Bool ℂ)
    (hc : ∀ a c : Bool, taggedValue (cell a c) = U a c) (x y : Reg n) :
    taggedValue (oneWireTag n w cell x y) =
      (if hw : w < n then wireGate n ⟨w, hw⟩ U else 1) x y := by
  by_cases hw : w < n
  · simp only [oneWireTag, dif_pos hw]
    rw [wireGate_apply]
    by_cases hs : ∀ j : Fin n, j ≠ ⟨w, hw⟩ → x j = y j
    · have hb := (outsideEq_true_iff ⟨w, hw⟩ x y).mpr hs
      rw [if_pos hb, if_pos hs]
      exact hc _ _
    · have hb : ¬ outsideEq ⟨w, hw⟩ x y = true :=
        fun hh => hs ((outsideEq_true_iff ⟨w, hw⟩ x y).mp hh)
      rw [if_neg hb, if_neg hs]
      exact zeroTag_sound
  · simp only [oneWireTag, dif_neg hw]
    exact identityTag_sound x y

/-- Interpreting `rawTag` gives the matrix entry specified by the finite gate code. -/
theorem rawTag_sound (n : ℕ) (g : FiniteGateCode) (x y : Reg n) :
    taggedValue (rawTag n g x y) = finiteCodeMatrix n g x y := by
  cases g with
  | h w =>
      exact oneWireTag_sound n w hCell Hadamard hCell_sound x y
  | x w =>
      exact oneWireTag_sound n w xCell PauliX xCell_sound x y
  | t w =>
      exact oneWireTag_sound n w tCell tGate tCell_sound x y
  | tdg w =>
      exact oneWireTag_sound n w tdgCell tGateAdj tdgCell_sound x y
  | cx c t =>
      by_cases h : c < n ∧ t < n ∧ c ≠ t
      · simp only [rawTag, finiteCodeMatrix, dif_pos h,
          cnotGate, permMatrix, Matrix.of_apply]
        by_cases he : x = Function.update y ⟨t, h.2.1⟩
            (y ⟨t, h.2.1⟩ ^^ y ⟨c, h.1⟩)
        · have hb := (regEq_true_iff x _).mpr he
          rw [if_pos hb, if_pos he]
          exact oneTag_sound
        · have hb : ¬ regEq x (Function.update y ⟨t, h.2.1⟩
              (y ⟨t, h.2.1⟩ ^^ y ⟨c, h.1⟩)) = true :=
            fun hh => he ((regEq_true_iff x _).mp hh)
          rw [if_neg hb, if_neg he]
          exact zeroTag_sound
      · simp only [rawTag, finiteCodeMatrix, dif_neg h]
        exact identityTag_sound x y

/-- Rounding the complex value of two atoms gives the dyadic value of their integer numerators. -/
theorem round_atoms (b : ℕ) (a c : Atom) :
    qmaRoundC b (cartesian a c) =
      dyadicValue b (atomNumerator b a) (atomNumerator b c) := by
  have hr : ⌊(cartesian a c).re * (2 : ℝ)^b + (1 : ℝ)/2⌋ =
      atomNumerator b a := by simpa [cartesian] using! floor_atom b a
  have hi : ⌊(cartesian a c).im * (2 : ℝ)^b + (1 : ℝ)/2⌋ =
      atomNumerator b c := by simpa [cartesian] using! floor_atom b c
  simp only [qmaRoundC, dyadicValue, hr, hi]

/-- The dyadic interpretation of `rawCoeff` equals the corresponding entry of `qmaRoundedGate`. -/
theorem rawCoeff_interpret (n b : ℕ) (g : FiniteGateCode) (x y : Reg n) :
    dyadicValue b (rawCoeff n b g x y).1 (rawCoeff n b g x y).2 =
      qmaRoundedGate n b g x y := by
  change dyadicValue b (atomNumerator b (rawTag n g x y).1)
    (atomNumerator b (rawTag n g x y).2) = qmaRoundC b (finiteCodeMatrix n g x y)
  rw [← round_atoms]
  exact congrArg (qmaRoundC b) (rawTag_sound n g x y)

end Qatlib.Papers.LocalHam06.MainResults

namespace Qatlib.Papers.LocalHam06.MainResults.NativeOutput
open Qatlib  Matrix
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped Classical

/-- At width `b + 1`, the dyadic propagation coefficients evaluate to the physical propagation
matrix entries for the rounded gate. -/
theorem propagationCoeff_interpret {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode)
    (p q : Clock m×Reg n) :
    dyadicValue (b+1) (propagationCoeff n b i g p q).1
      (propagationCoeff n b i g p q).2=
      physicalPropagation i (qmaRoundedGate n b g) p q := by
  let d : ℤ := if regEq p.1 q.1 && regEq p.2 q.2 then
    (if postBool i p.1 then (2:ℤ)^b else 0)+
    (if preBool i p.1 then (2:ℤ)^b else 0) else 0
  let f : ℤ×ℤ:=if hopBool i p.1 q.1 then rawCoeff n b g p.2 q.2 else (0,0)
  let r : ℤ×ℤ:=if hopBool i q.1 p.1 then rawCoeff n b g q.2 p.2 else (0,0)
  have hf : dyadicValue b f.1 f.2=
      hop i p.1 q.1*qmaRoundedGate n b g p.2 q.2 := by
    by_cases h : hopBool i p.1 q.1=true
    · simp only [f,if_pos h,rawCoeff_interpret,hop,
        if_pos ((hopBool_iff i p.1 q.1).mp h),one_mul]
    · have hn : ¬(Post i p.1 ∧ Pre i q.1 ∧ Outside i p.1 q.1) :=
        fun hh => h ((hopBool_iff i p.1 q.1).mpr hh)
      simp only [f,if_neg h,dyadic_zero,hop,if_neg hn,zero_mul]
  have hr : dyadicValue b r.1 r.2=
      hop i q.1 p.1*qmaRoundedGate n b g q.2 p.2 := by
    by_cases h : hopBool i q.1 p.1=true
    · simp only [r,if_pos h,rawCoeff_interpret,hop,
        if_pos ((hopBool_iff i q.1 p.1).mp h),one_mul]
    · have hn : ¬(Post i q.1 ∧ Pre i p.1 ∧ Outside i q.1 p.1) :=
        fun hh => h ((hopBool_iff i q.1 p.1).mpr hh)
      simp only [r,if_neg h,dyadic_zero,hop,if_neg hn,zero_mul]
  have hd : dyadicValue b d 0=
      postProjector i p.1 q.1*(1:Matrix (Reg n) (Reg n) ℂ) p.2 q.2+
      preProjector i p.1 q.1*(1:Matrix (Reg n) (Reg n) ℂ) p.2 q.2 := by
    simp only [d,postProjector,preProjector,clockIndicator,Matrix.diagonal_apply,Matrix.one_apply]
    by_cases hc : p.1=q.1 <;> by_cases hw : p.2=q.2 <;>
      by_cases hp : Post i p.1 <;> by_cases he : Pre i p.1
    all_goals
      simp_all [Qatlib.Concepts.QueryComplexity.DegreeMethod.regEq_true_iff,dyadicValue,postBool_iff,preBool_iff,add_div]
  change dyadicValue (b+1) (d-f.1-r.1) (-f.2+r.2)=_
  rw [dyadic_half,hf,hr,hd]
  rcases p with ⟨c,x⟩
  rcases q with ⟨d,y⟩
  simp only [physicalPropagation,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,
    Matrix.add_apply,tensorGate_apply,Matrix.conjTranspose_apply,star_mul,Complex.star_def]
  ring

/-- The value of a propagation term at width `b + 1` is the physical propagation matrix
reindexed by the flattening equivalence. -/
theorem propagationTerm_value {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode) :
    value (b+1) (propagationTerm n b i g)=
      Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
        (physicalPropagation i (qmaRoundedGate n b g)) := by
  ext x y
  rw [value,partitionLift_apply]
  change (if outside (propSites n i g) x=outside (propSites n i g) y then
    dyadicValue (b+1)
      (propagationCoeff n b i g
        (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) x)))
        (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) y)))).1
      (propagationCoeff n b i g
        (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) x)))
        (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) y)))).2
    else 0)=physicalPropagation i (qmaRoundedGate n b g)
      (flattenEquiv m n x) (flattenEquiv m n y)
  have h:=propagationCoeff_strong n b i g x y
  have he:=congrArg (fun p : ℤ×ℤ => dyadicValue (b+1) p.1 p.2) h

  rw [propagationCoeff_interpret] at he
  by_cases ho : outside (propSites n i g) x=outside (propSites n i g) y
  · rw [if_pos ho] at he ⊢
    exact he.symm
  · rw [if_neg ho] at he ⊢
    rw [dyadic_zero] at he
    exact he.symm

end Qatlib.Papers.LocalHam06.MainResults.NativeOutput
