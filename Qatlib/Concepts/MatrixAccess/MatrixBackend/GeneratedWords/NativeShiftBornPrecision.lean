/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeShiftNormalizedAxis
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CopyEvolution.Discriminate
/-! The actual generated Householder column and all eight Born probabilities.
The comparison simplex is the emitted rounded-radius weight vector. Root,
normalization, seven-QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation and reflection errors belong to the same
parameters; no final error or generated certificate is a premise. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The finite construction in `NativeShiftBornPrecision` satisfies `vec_coordinate_le` under the displayed hypotheses. -/
private theorem vec_coordinate_le (v : Fin 8 → ℂ) (i : Fin 8) :
    ‖v i‖ ≤ ‖toEuclidean_fromVec v‖ := by
  have hs := Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 8 => ‖v j‖^2)
    (a := i) (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
  rw [←norm_toEuclidean_fromVec_sq] at hs
  nlinarith [norm_nonneg (v i),norm_nonneg (toEuclidean_fromVec v)]

/-- The finite construction in `NativeShiftBornPrecision` satisfies `vec_sqrt_norm` under the displayed hypotheses. -/
private theorem vec_sqrt_norm (v : Fin 8 → ℂ) :
    Real.sqrt (∑ i : Fin 8,‖v i‖^2)=‖toEuclidean_fromVec v‖ := by
  rw [←norm_toEuclidean_fromVec_sq,Real.sqrt_sq (norm_nonneg _)]

/-- The estimate `born_l1_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem born_l1_error (u v : Fin 8 → ℂ)
    (hu : ‖toEuclidean_fromVec u‖=1) (hv : ‖toEuclidean_fromVec v‖=1) :
    (∑ i : Fin 8,|‖u i‖^2-‖v i‖^2|) ≤ 2*‖toEuclidean_fromVec (u-v)‖ := by
  have hi (i : Fin 8) : |‖u i‖^2-‖v i‖^2| ≤
      ‖(u-v) i‖*‖u i‖+‖(u-v) i‖*‖v i‖ := by
    calc
      _ = |‖u i‖-‖v i‖| *(‖u i‖+‖v i‖) := by
        rw [←abs_of_nonneg (add_nonneg (norm_nonneg (u i)) (norm_nonneg (v i))),←abs_mul]
        congr 1
        ring
      _ ≤ ‖(u-v) i‖*(‖u i‖+‖v i‖) :=
        mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le (u i) (v i)) (by positivity)
      _ = _ := by ring
  have hu' := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 8))
    (fun i => ‖(u-v) i‖) (fun i => ‖u i‖)
  have hv' := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 8))
    (fun i => ‖(u-v) i‖) (fun i => ‖v i‖)
  simp only [vec_sqrt_norm,hu,hv,mul_one] at hu' hv'
  calc
    _ ≤ ∑ i : Fin 8,(‖(u-v) i‖*‖u i‖+‖(u-v) i‖*‖v i‖) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = (∑ i : Fin 8,‖(u-v) i‖*‖u i‖)+(∑ i : Fin 8,‖(u-v) i‖*‖v i‖) :=
      Finset.sum_add_distrib
    _ ≤ _ := by linarith

/-- The estimate `normalization_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem normalization_error (u v : EuclideanSpace ℂ (Fin 8))
    (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    ‖(‖u‖⁻¹ : ℝ) • u-(‖v‖⁻¹ : ℝ) • v‖ ≤ 2*‖u-v‖ := by
  have hu0 : 0<‖u‖ := by linarith
  have hv0 : 0<‖v‖ := by linarith
  have hid : (‖u‖⁻¹ : ℝ) • u-(‖v‖⁻¹ : ℝ) • v=
      (‖u‖⁻¹ : ℝ) • (u-v)+(‖u‖⁻¹-‖v‖⁻¹ : ℝ) • v := by module
  have he : |‖u‖⁻¹-‖v‖⁻¹| *‖v‖=|‖u‖-‖v‖| /‖u‖ := by
    rw [inv_sub_inv (ne_of_gt hu0) (ne_of_gt hv0),abs_div,
      abs_mul,abs_of_pos hu0,abs_of_pos hv0,abs_sub_comm]
    field_simp
  rw [hid]
  calc
    _ ≤ ‖(‖u‖⁻¹ : ℝ) • (u-v)‖+‖(‖u‖⁻¹-‖v‖⁻¹ : ℝ) • v‖ := norm_add_le _ _
    _ = ‖u-v‖/‖u‖+|‖u‖-‖v‖| /‖u‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hu0),he]
      ring
    _ ≤ ‖u-v‖/‖u‖+‖u-v‖/‖u‖ :=
      add_le_add le_rfl (div_le_div_of_nonneg_right (abs_norm_sub_norm_le u v) hu0.le)
    _ ≤ _ := by
      have hh : ‖u-v‖/‖u‖ ≤ ‖u-v‖ :=
        (div_le_iff₀ hu0).mpr (by nlinarith [norm_nonneg (u-v)])
      linarith

/-- Construction for reflected Column in the native shift born precision model. -/
private def reflectedColumn (v : Fin 8 → ℂ) : Fin 8 → ℂ :=
  fun i => 2*v i*star (v 0)-(if i=0 then 1 else 0)

/-- The estimate `reflection_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem reflection_error (u v : Fin 8 → ℂ)
    (hu : ‖toEuclidean_fromVec u‖=1) (hv : ‖toEuclidean_fromVec v‖=1) :
    ‖toEuclidean_fromVec (reflectedColumn u-reflectedColumn v)‖ ≤
      4*‖toEuclidean_fromVec (u-v)‖ := by
  have hid : reflectedColumn u-reflectedColumn v=
      (2*star (u 0)) • (u-v)+(2*(star (u 0)-star (v 0))) • v := by
    funext i
    simp only [reflectedColumn,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hu0 : ‖u 0‖ ≤ 1 := (vec_coordinate_le u 0).trans_eq hu
  have hd0 : ‖u 0-v 0‖ ≤ ‖toEuclidean_fromVec (u-v)‖ := vec_coordinate_le (u-v) 0
  have hn : toEuclidean_fromVec (reflectedColumn u-reflectedColumn v)=
      (2*star (u 0)) • toEuclidean_fromVec (u-v)+
        (2*(star (u 0)-star (v 0))) • toEuclidean_fromVec v := by
    rw [hid]
    simp only [toEuclidean_fromVec,WithLp.toLp_add,WithLp.toLp_smul]
  rw [hn]
  calc
    _ ≤ ‖(2*star (u 0)) • toEuclidean_fromVec (u-v)‖+
      ‖(2*(star (u 0)-star (v 0))) • toEuclidean_fromVec v‖ := norm_add_le _ _
    _ = (2*‖u 0‖)*‖toEuclidean_fromVec (u-v)‖+2*‖u 0-v 0‖ := by
      simp only [norm_smul,norm_mul,norm_star,←star_sub,show ‖(2 : ℂ)‖=2 by norm_num,hv,mul_one]
    _ ≤ _ := by nlinarith [norm_nonneg (toEuclidean_fromVec (u-v))]


/-- Construction for normalized State in the native shift born precision model. -/
private def normalizedState (v : Fin 8 → ℂ) : Fin 8 → ℂ :=
  fun i => v i/(‖toEuclidean_fromVec v‖ : ℂ)

/-- The finite construction in `NativeShiftBornPrecision` satisfies `normalizedState_lp` under the displayed hypotheses. -/
private theorem normalizedState_lp (v : Fin 8 → ℂ) :
    toEuclidean_fromVec (normalizedState v)=
      (‖toEuclidean_fromVec v‖⁻¹ : ℝ) • toEuclidean_fromVec v := by
  ext i
  simp [normalizedState,toEuclidean_fromVec,div_eq_mul_inv,mul_comm]

/-- The finite construction in `NativeShiftBornPrecision` satisfies `normalizedState_norm` under the displayed hypotheses. -/
private theorem normalizedState_norm (v : Fin 8 → ℂ) (hv : 0<‖toEuclidean_fromVec v‖) :
    ‖toEuclidean_fromVec (normalizedState v)‖=1 := by
  rw [normalizedState_lp,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv)]
  exact inv_mul_cancel₀ (ne_of_gt hv)

/-- The estimate `normalizedState_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem normalizedState_error (u v : Fin 8 → ℂ)
    (hu : 1 ≤ ‖toEuclidean_fromVec u‖) (hv : 1 ≤ ‖toEuclidean_fromVec v‖) :
    ‖toEuclidean_fromVec (normalizedState u-normalizedState v)‖ ≤
      2*‖toEuclidean_fromVec (u-v)‖ := by
  have he : toEuclidean_fromVec (normalizedState u-normalizedState v)=
      toEuclidean_fromVec (normalizedState u)-toEuclidean_fromVec (normalizedState v) := by
    simp only [toEuclidean_fromVec,WithLp.toLp_sub]
  rw [he,normalizedState_lp,normalizedState_lp]
  exact normalization_error (toEuclidean_fromVec u) (toEuclidean_fromVec v) hu hv

/-- The finite construction in `NativeShiftBornPrecision` satisfies `vec_norm_le_eight` under the displayed hypotheses. -/
private theorem vec_norm_le_eight (v : Fin 8 → ℂ) (h : ℝ) (hh : 0 ≤ h)
    (he : ∀ i,‖v i‖ ≤ h) : ‖toEuclidean_fromVec v‖ ≤ 8*h := by
  have hs : (∑ i : Fin 8,‖v i‖^2) ≤ 8*h^2 := by
    calc
      _ ≤ ∑ _i : Fin 8,h^2 := Finset.sum_le_sum (fun i _ => by
        nlinarith [norm_nonneg (v i),he i])
      _ = _ := by simp
  rw [←norm_toEuclidean_fromVec_sq] at hs
  nlinarith [norm_nonneg (toEuclidean_fromVec v)]

/-- Construction for simplex Axis in the native shift born precision model. -/
private def simplexAxis (s : Fin 8 → ℝ) : Fin 8 → ℂ :=
  fun i => ((s i+if i=0 then 1 else 0 : ℝ) : ℂ)

/-- The finite construction in `NativeShiftBornPrecision` satisfies `simplexAxis_norm_sq` under the displayed hypotheses. -/
private theorem simplexAxis_norm_sq (s : Fin 8 → ℝ) (hs : (∑ i : Fin 8,s i^2)=1) :
    ‖toEuclidean_fromVec (simplexAxis s)‖^2=2+2*s 0 := by
  rw [norm_toEuclidean_fromVec_sq]
  simp only [simplexAxis,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have he (i : Fin 8) : (s i+if i=0 then 1 else 0)^2=
      s i^2+(if i=0 then 2*s 0+1 else 0) := by
    by_cases hi : i=0
    · subst i
      simp
      ring
    · simp [hi]
  simp_rw [he]
  rw [Finset.sum_add_distrib,hs]
  simp
  ring

/-- The finite construction in `NativeShiftBornPrecision` satisfies `simplexAxis_norm_ge_one` under the displayed hypotheses. -/
private theorem simplexAxis_norm_ge_one (s : Fin 8 → ℝ) (hs : 0 ≤ s 0) :
    1 ≤ ‖toEuclidean_fromVec (simplexAxis s)‖ := by
  have hc := vec_coordinate_le (simplexAxis s) 0
  have h0 : ‖simplexAxis s 0‖=s 0+1 := by
    change ‖((s 0+1 : ℝ) : ℂ)‖=s 0+1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  rw [h0] at hc
  linarith

/-- The finite construction in `NativeShiftBornPrecision` satisfies `simplexAxis_reflected` under the displayed hypotheses. -/
private theorem simplexAxis_reflected (s : Fin 8 → ℝ)
    (hs : (∑ i : Fin 8,s i^2)=1) (hs0 : 0 ≤ s 0) :
    reflectedColumn (normalizedState (simplexAxis s))=(fun i => (s i : ℂ)) := by
  have hn := simplexAxis_norm_sq s hs
  have hpos : 0<‖toEuclidean_fromVec (simplexAxis s)‖ :=
    lt_of_lt_of_le zero_lt_one (simplexAxis_norm_ge_one s hs0)
  have hnC : (‖toEuclidean_fromVec (simplexAxis s)‖ : ℂ)^2=2+2*(s 0 : ℂ) := by
    exact_mod_cast hn
  have hd : (‖toEuclidean_fromVec (simplexAxis s)‖ : ℂ)≠0 := by exact_mod_cast ne_of_gt hpos
  funext i
  simp only [reflectedColumn,normalizedState,simplexAxis,ite_true,star_div₀,
    Complex.star_def,Complex.conj_ofReal]
  by_cases hi : i=0
  · subst i
    simp only [ite_true,Complex.ofReal_add,Complex.ofReal_one]
    field_simp [hd]
    linear_combination -(s 0+1 : ℂ)*hnC
  · simp only [ite_eq_right hi,add_zero,Complex.ofReal_add,Complex.ofReal_one]
    field_simp [hd]
    linear_combination -(s i : ℂ)*hnC


/-- Construction for shift Simplex Root in the native shift born precision model. -/
private def shiftSimplexRoot (α B x y : ℚ) (p : ℕ) (i : Fin 8) : ℝ :=
  Real.sqrt (shiftWeights α B x y p i : ℝ)

/-- The finite construction in `NativeShiftBornPrecision` satisfies `shiftSimplexRoot_sq` under the displayed hypotheses. -/
private theorem shiftSimplexRoot_sq (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 8) :
    (shiftSimplexRoot α B x y p i)^2=(shiftWeights α B x y p i : ℝ) := by
  apply Real.sq_sqrt
  exact_mod_cast (shiftWeights_simplex α B x y p hα hB hz).1 i

/-- The finite construction in `NativeShiftBornPrecision` satisfies `shiftSimplexRoot_sum` under the displayed hypotheses. -/
private theorem shiftSimplexRoot_sum (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    (∑ i : Fin 8,(shiftSimplexRoot α B x y p i)^2)=1 := by
  simp_rw [shiftSimplexRoot_sq α B x y p hα hB hz]
  rw [←Rat.cast_sum,(shiftWeights_simplex α B x y p hα hB hz).2]
  norm_num

/-- The finite construction in `NativeShiftBornPrecision` satisfies `shiftSimplexRoot_norm` under the displayed hypotheses. -/
private theorem shiftSimplexRoot_norm (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    ‖toEuclidean_fromVec (fun i => (shiftSimplexRoot α B x y p i : ℂ))‖=1 := by
  apply (normalized_iff_norm_toEuclidean_fromVec _).mp
  simp only [Normalized,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact shiftSimplexRoot_sum α B x y p hα hB hz

/-- The estimate `shiftRootAxis_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem shiftRootAxis_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    ‖toEuclidean_fromVec ((fun i => (shiftAxis α B x y p i : ℂ))-
      simplexAxis (shiftSimplexRoot α B x y p))‖ ≤ 8/(2 : ℝ)^(p+12) := by
  have hh : (0 : ℝ) ≤ 1/(2 : ℝ)^(p+12) := by positivity
  have he (i : Fin 8) :
      ‖((fun j => (shiftAxis α B x y p j : ℂ))-
        simplexAxis (shiftSimplexRoot α B x y p)) i‖ ≤ 1/(2 : ℝ)^(p+12) := by
    have hi := (nativeSqrtInterval_real (shiftWeights α B x y p i) (p+12)
      ((shiftWeights_simplex α B x y p hα hB hz).1 i)).2.2.1
    have hid : ((fun j => (shiftAxis α B x y p j : ℂ))-
        simplexAxis (shiftSimplexRoot α B x y p)) i=
        (((shiftRoots α B x y p i : ℝ)-shiftSimplexRoot α B x y p i : ℝ) : ℂ) := by
      by_cases hi0 : i=0
      · subst i
        simp [shiftAxis,simplexAxis]
      · simp [shiftAxis,simplexAxis,hi0]
    rw [hid,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
    exact hi
  have hx := vec_norm_le_eight _ _ hh he
  simpa only [mul_one_div] using hx

/-- The finite construction in `NativeShiftBornPrecision` satisfies `shiftRoundedAxis_norm_ge_one` under the displayed hypotheses. -/
private theorem shiftRoundedAxis_norm_ge_one (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    1 ≤ ‖toEuclidean_fromVec (fun i => (shiftAxis α B x y p i : ℂ))‖ := by
  rw [←shiftRadius_total_norm α B x y p hα hB hz]
  have hsq := shiftRadius_sq α B x y p hα hB hz (7 : Fin 8)
  have hh : (1 : ℝ) ≤ shiftPrefix α B x y p 7 := by
    exact_mod_cast shiftPrefix_ge_one α B x y p hα hB hz (7 : Fin 8)
  nlinarith [shiftRadius_pos α B x y p hα hB hz 7]

/-- The finite construction in `NativeShiftBornPrecision` satisfies `nativeVColumn_norm` under the displayed hypotheses. -/
private theorem nativeVColumn_norm (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    ‖toEuclidean_fromVec (fun i => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.vLogical ps i 0)‖=1 := by
  have he : (fun i => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.vLogical ps i 0)=ApplyGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.vLogical ps) (Qatlib.Foundations.PureStateMath.Ket 0) := by
    funext i
    simp [ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]
  rw [he]
  exact (normalized_iff_norm_toEuclidean_fromVec _).mp
    (normalized_applyGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.pairProduct_unitary _ ps) (normalized_ket _))

/-- The finite construction in `NativeShiftBornPrecision` satisfies `nativePrepared_norm` under the displayed hypotheses. -/
private theorem nativePrepared_norm (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    ‖toEuclidean_fromVec (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps)‖=1 := by
  have he : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps=ApplyGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepLogical ps) (Qatlib.Foundations.PureStateMath.Ket 0) := by
    funext i
    simp [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis,ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]
  rw [he]
  exact (normalized_iff_norm_toEuclidean_fromVec _).mp
    (normalized_applyGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepLogical_unitary ps) (normalized_ket _))

/-- The estimate `nativeShiftSimplexAxis_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem nativeShiftSimplexAxis_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    ‖toEuclidean_fromVec ((fun i => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.vLogical (nativeShiftCircles α B x y p) i 0)-
      normalizedState (simplexAxis (shiftSimplexRoot α B x y p)))‖ ≤
      23/(2 : ℝ)^(p+12) := by
  let V : Fin 8 → ℂ := fun i => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.vLogical (nativeShiftCircles α B x y p) i 0
  let X : Fin 8 → ℂ := fun i => shiftAxis α B x y p i
  let Y := simplexAxis (shiftSimplexRoot α B x y p)
  have hX : 1 ≤ ‖toEuclidean_fromVec X‖ := shiftRoundedAxis_norm_ge_one α B x y p hα hB hz
  have hY : 1 ≤ ‖toEuclidean_fromVec Y‖ :=
    simplexAxis_norm_ge_one _ (Real.sqrt_nonneg _)
  have hXY := normalizedState_error X Y hX hY
  have hroot := shiftRootAxis_error α B x y p hα hB hz
  have hV := nativeShiftAxis_error α B x y p hα hB hz
  rw [shiftRadius_total_norm α B x y p hα hB hz] at hV
  change ‖toEuclidean_fromVec (V-normalizedState X)‖ ≤ _ at hV
  have htri : ‖toEuclidean_fromVec (V-normalizedState Y)‖ ≤
      ‖toEuclidean_fromVec (V-normalizedState X)‖+
        ‖toEuclidean_fromVec (normalizedState X-normalizedState Y)‖ := by
    simpa only [dist_eq_norm,toEuclidean_fromVec,WithLp.toLp_sub] using
      dist_triangle (toEuclidean_fromVec V) (toEuclidean_fromVec (normalizedState X))
        (toEuclidean_fromVec (normalizedState Y))
  change ‖toEuclidean_fromVec (X-Y)‖ ≤ _ at hroot
  change ‖toEuclidean_fromVec (V-normalizedState Y)‖ ≤ _
  calc
    _ ≤ _ := htri
    _ ≤ 7/(2 : ℝ)^(p+12)+2*(8/(2 : ℝ)^(p+12)) :=
      add_le_add hV (hXY.trans (mul_le_mul_of_nonneg_left hroot (by norm_num)))
    _ = _ := by ring

/-- Uniform error of the actual generated Householder column against the
square roots of its actual emitted weight simplex, without a certificate premise. -/
theorem nativeShiftPreparedColumn_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    ‖toEuclidean_fromVec (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis (nativeShiftCircles α B x y p)-
      (fun i => ((Real.sqrt (shiftWeights α B x y p i : ℝ)) : ℂ)))‖ ≤
      92/(2 : ℝ)^(p+12) := by
  let ps := nativeShiftCircles α B x y p
  let V : Fin 8 → ℂ := fun i => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.vLogical ps i 0
  let Y := simplexAxis (shiftSimplexRoot α B x y p)
  have hYn : 0<‖toEuclidean_fromVec Y‖ :=
    lt_of_lt_of_le zero_lt_one (simplexAxis_norm_ge_one _ (Real.sqrt_nonneg _))
  have he := reflection_error V (normalizedState Y) (nativeVColumn_norm ps) (normalizedState_norm Y hYn)
  have href : reflectedColumn V=Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps := by
    funext i
    exact (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis_entries ps i).symm
  have htarget := simplexAxis_reflected (shiftSimplexRoot α B x y p)
    (shiftSimplexRoot_sum α B x y p hα hB hz) (Real.sqrt_nonneg _)
  rw [href,htarget] at he
  have hV := nativeShiftSimplexAxis_error α B x y p hα hB hz
  change ‖toEuclidean_fromVec (V-normalizedState Y)‖ ≤ _ at hV
  change ‖toEuclidean_fromVec (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps-
    (fun i => (shiftSimplexRoot α B x y p i : ℂ)))‖ ≤ _
  exact he.trans ((mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring))

/-- All eight Born probabilities of the same generated preparation, compared
with the actual rounded-radius weights. Both coefficient groups use this once. -/
theorem nativeShiftBorn_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    (∑ i : Fin 8,|‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis (nativeShiftCircles α B x y p) i‖^2-
      (shiftWeights α B x y p i : ℝ)|) ≤ 184/(2 : ℝ)^(p+12) := by
  have he := born_l1_error (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis (nativeShiftCircles α B x y p))
    (fun i => (shiftSimplexRoot α B x y p i : ℂ)) (nativePrepared_norm _)
    (shiftSimplexRoot_norm α B x y p hα hB hz)
  have hc := nativeShiftPreparedColumn_error α B x y p hα hB hz
  have hi (i : Fin 8) : ‖(shiftSimplexRoot α B x y p i : ℂ)‖^2=
      (shiftWeights α B x y p i : ℝ) := by
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact shiftSimplexRoot_sq α B x y p hα hB hz i
  simp_rw [hi] at he
  change ‖toEuclidean_fromVec (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis (nativeShiftCircles α B x y p)-
    (fun i => (shiftSimplexRoot α B x y p i : ℂ)))‖ ≤ _ at hc
  exact he.trans ((mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
