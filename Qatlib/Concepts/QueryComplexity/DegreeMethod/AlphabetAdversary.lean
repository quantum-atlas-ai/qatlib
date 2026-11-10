/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvWitness
import Mathlib.Data.ZMod.Basic
import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxRecDepth 4096
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def alphabetShift {W : Type} {n a : ℕ} (input : Fin n → ZMod a) :
    Equiv.Perm ((Fin n×ZMod a)×W) where
  toFun p := ((p.1.1,p.1.2+input p.1.1),p.2)
  invFun p := ((p.1.1,p.1.2-input p.1.1),p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

noncomputable def alphabetOracle {W : Type} [Fintype W] [DecidableEq W] {n a : ℕ}
    [NeZero a] (input : Fin n → ZMod a) :
    Matrix ((Fin n×ZMod a)×W) ((Fin n×ZMod a)×W) ℂ := permMatrix (alphabetShift input)

noncomputable def alphabetFilter {X : Type} {n a : ℕ} (input : X→Fin n→ZMod a)
    (Gamma : Matrix X X ℂ) (i : Fin n) : Matrix X X ℂ :=
  fun x y => if input x i≠input y i then Gamma x y else 0

noncomputable def alphabetCubeGamma (n a : ℕ) [NeZero a] :
    Matrix (Fin n→ZMod a) (Fin n→ZMod a) ℂ :=
  fun x y => if (Finset.univ.filter (fun i => x i≠y i)).card=1 then 1 else 0

theorem alphabet_oracle_actual_unitarity_and_filter
    (W : Type) [Fintype W] [DecidableEq W] (n a : ℕ) [NeZero a]
    (input : Fin n → ZMod a) :
    alphabetOracle (W:=W) input ∈ Matrix.unitaryGroup ((Fin n × ZMod a) × W) ℂ :=
  permMatrix_unitary_of_injective (alphabetShift input).injective

noncomputable def multiCorrect {X H Y : Type} [DecidableEq Y]
    (f : X → Y) (label : H → Y) (v : QState (X × H)) : QState (X × H) :=
  fun p => if label p.2 = f p.1 then v p else 0

noncomputable def multiError {X H Y : Type} [DecidableEq Y]
    (f : X → Y) (label : H → Y) (v : QState (X × H)) : QState (X × H) :=
  fun p => if label p.2 = f p.1 then 0 else v p

private theorem multi_correct_add_error {X H Y : Type} [DecidableEq Y]
    (f : X → Y) (label : H → Y) (v : QState (X × H)) :
    multiCorrect f label v + multiError f label v = v := by
  ext p
  by_cases hp : label p.2 = f p.1 <;> simp [multiCorrect, multiError, hp]

private theorem multi_correct_zero {X H Y : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [DecidableEq Y]
    (Gamma : Matrix X X ℂ) (f : X → Y) (label : H → Y) (v : QState (X × H))
    (hz : ∀ x y, f x = f y → Gamma x y = 0) :
    Qatlib.Foundations.PureStateMath.Inner (multiCorrect f label v) (TensorGate Gamma (1 : Matrix H H ℂ) *ᵥ multiCorrect f label v) = 0 := by
  simp only [inner_apply, Fintype.sum_prod_type, advTensor_mulVec, Finset.mul_sum]
  apply Finset.sum_eq_zero; intro x _
  apply Finset.sum_eq_zero; intro h _
  apply Finset.sum_eq_zero; intro y _
  by_cases hx : label h = f x <;> by_cases hy : label h = f y
  · simp [hz x y (hx.symm.trans hy)]
  · simp only [multiCorrect, if_pos hx, if_neg hy]; simp
  · simp only [multiCorrect, if_neg hx, if_pos hy]; simp
  · simp only [multiCorrect, if_neg hx, if_neg hy]; simp

private theorem multi_output_energy {X H Y : Type} [Fintype X] [Fintype H]
    [DecidableEq Y] (f : X → Y) (label : H → Y) (v : QState (X × H)) :
    ‖toEuclidean_fromVec (multiCorrect f label v)‖ ^ 2 +
      ‖toEuclidean_fromVec (multiError f label v)‖ ^ 2 = ‖toEuclidean_fromVec v‖ ^ 2 := by
  simp only [norm_toEuclidean_fromVec_sq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : label p.2 = f p.1 <;> simp [multiCorrect, multiError, hp]

private theorem multi_correct_mass {X H Y : Type} [Fintype X] [Fintype H]
    [DecidableEq Y] (f : X → Y) (label : H → Y) (weight : QState X)
    (states : X → QState H) :
    ‖toEuclidean_fromVec (multiCorrect f label (advStack weight states))‖ ^ 2 =
      ∑ x, ‖weight x‖ ^ 2 * MeasureProb (states x) (Finset.univ.filter (fun h => label h = f x)) := by
  rw [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp only [multiCorrect, advStack, MeasureProb, BornProb, Finset.mul_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : label h = f x <;> simp [hh, mul_pow]

theorem multioutput_adversary_actual_final_progress
    (X H Y : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    [Fintype Y] [DecidableEq Y] (Gamma : Matrix X X ℂ) (weight : QState X)
    (states : X → QState H) (f : X → Y) (label : H → Y) (eps : ℝ)
    (_hG : Gamma.IsHermitian) (hw : Normalized weight) (hs : ∀ x, Normalized (states x))
    (hz : ∀ x y, f x = f y → Gamma x y = 0) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hsuccess : ∀ x, 1 - eps ≤ MeasureProb (states x) (Finset.univ.filter (fun h => label h = f x))) :
    |advProgress Gamma weight states| ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Gamma‖ := by
  classical
  let v := advStack weight states
  let c := multiCorrect f label v
  let b := multiError f label v
  let A : Matrix (X × H) (X × H) ℂ := TensorGate Gamma 1
  have hv : ‖toEuclidean_fromVec v‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (advStack_normalized _ _ hw hs)
  have hcb : c + b = v := multi_correct_add_error _ _ _
  have hcc := multi_correct_zero Gamma f label v hz
  have hform : Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v) = (Qatlib.Foundations.PureStateMath.Inner c (A *ᵥ b) + Qatlib.Foundations.PureStateMath.Inner b (A *ᵥ c)) + Qatlib.Foundations.PureStateMath.Inner b (A *ᵥ b) := by
    rw [← hcb, Matrix.mulVec_add]
    simp only [Qatlib.Foundations.PureStateMath.Inner, star_add, add_dotProduct,
        dotProduct_add] at *
    rw [hcc]
    ring
  have hA : ‖A‖ ≤ ‖Gamma‖ := by
    dsimp [A]
    rw [l2_norm_tensorGate]
    exact (mul_le_mul_of_nonneg_left l2_norm_one_le (norm_nonneg _)).trans_eq (mul_one _)
  have henergy : ‖toEuclidean_fromVec c‖ ^ 2 + ‖toEuclidean_fromVec b‖ ^ 2 = 1 := by
    simpa only [hv, one_pow] using! multi_output_energy f label v
  have hcmass : 1 - eps ≤ ‖toEuclidean_fromVec c‖ ^ 2 := by
    rw [multi_correct_mass]
    calc 1 - eps = ∑ x, ‖weight x‖ ^ 2 * (1 - eps) := by
          rw [← Finset.sum_mul, show ∑ x, ‖weight x‖ ^ 2 = 1 from hw, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (hsuccess x) (sq_nonneg _)
  have hbmass : ‖toEuclidean_fromVec b‖ ^ 2 ≤ eps := by linarith
  have hprod : ‖toEuclidean_fromVec c‖ * ‖toEuclidean_fromVec b‖ ≤
      Real.sqrt (eps * (1 - eps)) := by
    have hnon : 0 ≤ eps * (1 - eps) := mul_nonneg he0 (by linarith)
    have haux := mul_nonneg (sub_nonneg.mpr hbmass)
      (show 0 ≤ 1 - eps - ‖toEuclidean_fromVec b‖ ^ 2 by linarith)
    have hsqrt := Real.sq_sqrt hnon
    have hpos := Real.sqrt_nonneg (eps * (1 - eps))
    nlinarith [sq_nonneg (‖toEuclidean_fromVec c‖ * ‖toEuclidean_fromVec b‖ -
      Real.sqrt (eps * (1 - eps))), norm_nonneg (toEuclidean_fromVec c),
      norm_nonneg (toEuclidean_fromVec b)]
  have hcross : ‖Qatlib.Foundations.PureStateMath.Inner c (A *ᵥ b) + Qatlib.Foundations.PureStateMath.Inner b (A *ᵥ c)‖ ≤
      2 * Real.sqrt (eps * (1 - eps)) * ‖Gamma‖ := by
    calc _ ≤ ‖Qatlib.Foundations.PureStateMath.Inner c (A *ᵥ b)‖ + ‖Qatlib.Foundations.PureStateMath.Inner b (A *ᵥ c)‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖toEuclidean_fromVec c‖ * ‖toEuclidean_fromVec b‖ +
          ‖A‖ * ‖toEuclidean_fromVec b‖ * ‖toEuclidean_fromVec c‖ :=
        add_le_add (adv_inner_matrix_bound _ _ _) (adv_inner_matrix_bound _ _ _)
      _ = 2 * (‖toEuclidean_fromVec c‖ * ‖toEuclidean_fromVec b‖) * ‖A‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hprod (by norm_num)) hA
        (norm_nonneg _) (by positivity)
  have herror : ‖Qatlib.Foundations.PureStateMath.Inner b (A *ᵥ b)‖ ≤ eps * ‖Gamma‖ := by
    calc _ ≤ ‖A‖ * ‖toEuclidean_fromVec b‖ * ‖toEuclidean_fromVec b‖ := adv_inner_matrix_bound _ _ _
      _ = ‖A‖ * ‖toEuclidean_fromVec b‖ ^ 2 := by ring
      _ ≤ ‖Gamma‖ * eps := mul_le_mul hA hbmass (sq_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  rw [advProgress_stack]
  calc |(Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)).re| ≤ ‖Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)‖ := Complex.abs_re_le_norm _
    _ ≤ 2 * Real.sqrt (eps * (1 - eps)) * ‖Gamma‖ + eps * ‖Gamma‖ := by
      rw [hform]
      exact (norm_add_le _ _).trans (add_le_add hcross herror)
    _ ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Gamma‖ := by
      nlinarith [norm_nonneg Gamma]

theorem alphabetOracle_mulVec {W : Type} [Fintype W] [DecidableEq W] {n a : ℕ}
    [NeZero a] (input : Fin n → ZMod a) (ψ : QState ((Fin n × ZMod a) × W))
    (p : (Fin n × ZMod a) × W) :
    (alphabetOracle input *ᵥ ψ) p = ψ ((p.1.1, p.1.2 - input p.1.1), p.2) := by
  classical
  change (permMatrix (alphabetShift input) *ᵥ ψ) p = ψ ((alphabetShift input).symm p)
  simp only [Matrix.mulVec, dotProduct, permMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single ((alphabetShift input).symm p)]
  · simp
  · intro q _ hq
    have hp : p ≠ alphabetShift input q := by
      intro h
      exact hq (by simpa using! congrArg (alphabetShift input).symm h.symm)
    simp [hp]
  · simp

private theorem alphabet_form_expand {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] (Gamma : Matrix X X ℂ) (v : QState (X × H)) :
    Qatlib.Foundations.PureStateMath.Inner v (TensorGate Gamma (1 : Matrix H H ℂ) *ᵥ v) =
      ∑ x, ∑ y, Gamma x y * Qatlib.Foundations.PureStateMath.Inner (fun h => v (x, h)) (fun h => v (y, h)) := by
  simp only [inner_apply, Fintype.sum_prod_type, advTensor_mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.sum_congr rfl fun h _ => by ring

private noncomputable def alphabetPull {X W : Type} {a : ℕ} (f : X → ZMod a)
    (v : QState (X × (ZMod a × W))) : QState (X × (ZMod a × W)) :=
  fun p => v (p.1, (p.2.1 - f p.1, p.2.2))

private def alphabetSectorPerm {W : Type} {a : ℕ} (z : ZMod a) : Equiv.Perm (ZMod a × W) where
  toFun p := (p.1 - z, p.2)
  invFun p := (p.1 + z, p.2)
  left_inv p := by simp
  right_inv p := by simp

private theorem alphabetPull_inner {X W : Type} [Fintype W] {a : ℕ} [NeZero a]
    (f : X → ZMod a) (v : QState (X × (ZMod a × W))) (x y : X) (hxy : f x = f y) :
    Qatlib.Foundations.PureStateMath.Inner (fun h => alphabetPull f v (x,h)) (fun h => alphabetPull f v (y,h)) =
      Qatlib.Foundations.PureStateMath.Inner (fun h => v (x,h)) (fun h => v (y,h)) := by
  simp only [inner_apply, alphabetPull, hxy]
  exact Equiv.sum_comp (alphabetSectorPerm (W:=W) (f y))
    (fun h => star (v (x,h)) * v (y,h))

private theorem alphabetPull_norm {X W : Type} [Fintype X] [Fintype W] {a : ℕ} [NeZero a]
    (f : X → ZMod a) (v : QState (X × (ZMod a × W))) :
    ‖toEuclidean_fromVec (alphabetPull f v)‖ = ‖toEuclidean_fromVec v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [Fintype.sum_prod_type, alphabetSectorPerm, Equiv.coe_fn_mk, alphabetPull] using!
    Equiv.sum_comp (alphabetSectorPerm (W:=W) (f x)) (fun h => ‖v (x,h)‖ ^ 2)

private theorem alphabetPull_filter_difference {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] {a : ℕ} [NeZero a] (f : X → ZMod a) (Gamma : Matrix X X ℂ)
    (v : QState (X × (ZMod a × W))) :
    Qatlib.Foundations.PureStateMath.Inner (alphabetPull f v) (TensorGate Gamma 1 *ᵥ alphabetPull f v) - Qatlib.Foundations.PureStateMath.Inner v (TensorGate Gamma 1 *ᵥ v) =
      Qatlib.Foundations.PureStateMath.Inner (alphabetPull f v) (TensorGate (fun x y => if f x ≠ f y then Gamma x y else 0) 1 *ᵥ alphabetPull f v) -
        Qatlib.Foundations.PureStateMath.Inner v (TensorGate (fun x y => if f x ≠ f y then Gamma x y else 0) 1 *ᵥ v) := by
  simp only [alphabet_form_expand, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hf : f x = f y
  · simp only [hf, ne_eq, not_true_eq_false, if_false, zero_mul,
      alphabetPull_inner f v x y hf, sub_self]
  · simp [hf]

private theorem alphabetPull_progress_bound {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] {a : ℕ} [NeZero a] (f : X → ZMod a) (Gamma : Matrix X X ℂ)
    (v : QState (X × (ZMod a × W))) :
    |(Qatlib.Foundations.PureStateMath.Inner (alphabetPull f v) (TensorGate Gamma 1 *ᵥ alphabetPull f v) -
      Qatlib.Foundations.PureStateMath.Inner v (TensorGate Gamma 1 *ᵥ v)).re| ≤
      let G : Matrix X X ℂ := fun x y => if f x ≠ f y then Gamma x y else 0
      2 * ‖G‖ * ‖toEuclidean_fromVec v‖ ^ 2 := by
  let G : Matrix X X ℂ := fun x y => if f x ≠ f y then Gamma x y else 0
  let A : Matrix (X × (ZMod a × W)) (X × (ZMod a × W)) ℂ := TensorGate G 1
  have hA : ‖A‖ ≤ ‖G‖ := by
    dsimp [A]
    rw [l2_norm_tensorGate]
    exact (mul_le_mul_of_nonneg_left l2_norm_one_le (norm_nonneg _)).trans_eq (mul_one _)
  rw [alphabetPull_filter_difference]
  calc _ ≤ ‖Qatlib.Foundations.PureStateMath.Inner (alphabetPull f v) (A *ᵥ alphabetPull f v) - Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖Qatlib.Foundations.PureStateMath.Inner (alphabetPull f v) (A *ᵥ alphabetPull f v)‖ + ‖Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖toEuclidean_fromVec (alphabetPull f v)‖ * ‖toEuclidean_fromVec (alphabetPull f v)‖ +
        ‖A‖ * ‖toEuclidean_fromVec v‖ * ‖toEuclidean_fromVec v‖ :=
      add_le_add (adv_inner_matrix_bound _ _ _) (adv_inner_matrix_bound _ _ _)
    _ = 2 * ‖A‖ * ‖toEuclidean_fromVec v‖ ^ 2 := by rw [alphabetPull_norm]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num)) (sq_nonneg _)

noncomputable def alphabetSlice {X W : Type} {n a : ℕ} [NeZero a] (weight : QState X)
    (states : X → QState ((Fin n × ZMod a) × W)) (i : Fin n) : QState (X × (ZMod a × W)) :=
  fun p => weight p.1 * states p.1 ((i, p.2.1), p.2.2)

private theorem alphabetProgress_slices {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] {n a : ℕ} [NeZero a] (Gamma : Matrix X X ℂ) (weight : QState X)
    (states : X → QState ((Fin n × ZMod a) × W)) :
    advProgress Gamma weight states =
      (∑ i, Qatlib.Foundations.PureStateMath.Inner (alphabetSlice weight states i)
        (TensorGate Gamma (1 : Matrix (ZMod a × W) (ZMod a × W) ℂ) *ᵥ alphabetSlice weight states i)).re := by
  unfold advProgress
  congr 1
  simp_rw [alphabet_form_expand]
  simp only [inner_apply, Fintype.sum_prod_type, alphabetSlice, map_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_congr rfl fun w _ => by simp only [RCLike.star_def]; ring

private theorem alphabetSlice_query {X W : Type} [Fintype W] [DecidableEq W]
    {n a : ℕ} [NeZero a] (input : X → Fin n → ZMod a) (weight : QState X)
    (states : X → QState ((Fin n × ZMod a) × W)) (i : Fin n) :
    alphabetSlice weight (fun x => alphabetOracle (W := W) (input x) *ᵥ states x) i =
      alphabetPull (fun x => input x i) (alphabetSlice weight states i) := by
  ext p
  simp only [alphabetSlice, alphabetPull]
  rw [alphabetOracle_mulVec]

private theorem alphabetSlice_energy {X W : Type} [Fintype X] [Fintype W] {n a : ℕ} [NeZero a]
    (weight : QState X) (states : X → QState ((Fin n × ZMod a) × W))
    (hw : Normalized weight) (hs : ∀ x, Normalized (states x)) :
    ∑ i, ‖toEuclidean_fromVec (alphabetSlice weight states i)‖ ^ 2 = 1 := by
  simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type, alphabetSlice, norm_mul,
    mul_pow, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hsn : ∀ x, (∑ i, ∑ b, ∑ w, ‖states x ((i, b), w)‖ ^ 2) = 1 := by
    intro x
    simpa only [Normalized, Fintype.sum_prod_type] using! hs x
  simp only [hsn, mul_one]
  exact hw

theorem alphabet_adversary_same_query_progress
    (X W : Type) [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W] (n a : ℕ) [NeZero a]
    (input : X → Fin n → ZMod a) (Gamma : Matrix X X ℂ) (weight : QState X)
    (states : X → QState ((Fin n × ZMod a) × W)) (B : ℝ) (_hG : Gamma.IsHermitian)
    (hw : Normalized weight) (hs : ∀ x, Normalized (states x)) (_hB : 0 ≤ B)
    (hfilter : ∀ i, ‖alphabetFilter input Gamma i‖ ≤ B) :
    |advProgress Gamma weight (fun x => alphabetOracle (W := W) (input x) *ᵥ states x) -
      advProgress Gamma weight states| ≤ 2 * B := by
  rw [alphabetProgress_slices, alphabetProgress_slices, ← Complex.sub_re, ← Finset.sum_sub_distrib]
  simp only [alphabetSlice_query, Complex.re_sum]
  calc _ ≤ ∑ i, |(Qatlib.Foundations.PureStateMath.Inner (alphabetPull (fun x => input x i) (alphabetSlice weight states i))
        (TensorGate Gamma 1 *ᵥ alphabetPull (fun x => input x i) (alphabetSlice weight states i)) -
          Qatlib.Foundations.PureStateMath.Inner (alphabetSlice weight states i) (TensorGate Gamma 1 *ᵥ alphabetSlice weight states i)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * ‖alphabetFilter input Gamma i‖ * ‖toEuclidean_fromVec (alphabetSlice weight states i)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => alphabetPull_progress_bound _ _ _
    _ ≤ ∑ i, 2 * B * ‖toEuclidean_fromVec (alphabetSlice weight states i)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hfilter i) (by norm_num)) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, alphabetSlice_energy weight states hw hs, mul_one]

theorem alphabetProgress_run_bound
    (X W : Type) [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W] (n a : ℕ) [NeZero a]
    (input : X → Fin n → ZMod a) (Gamma : Matrix X X ℂ) (weight : QState X) (B : ℝ) (hB : 0 ≤ B)
    (hfilter : ∀ i, ‖alphabetFilter input Gamma i‖ ≤ B)
    (C : Circuit ((Fin n × ZMod a) × W)) (hG : Gamma.IsHermitian) (hw : Normalized weight)
    (hC : IsUnitaryCircuit C) (states : X → QState ((Fin n × ZMod a) × W))
    (hs : ∀ x, Normalized (states x)) :
    |advProgress Gamma weight (fun x => Run (alphabetOracle (W := W) (input x)) C (states x)) -
      advProgress Gamma weight states| ≤ 2 * (QueryCount C) * B := by
  induction C generalizing states with
  | nil => simp [Run, QueryCount]
  | cons s C ih =>
    cases s with
    | gate U =>
      obtain ⟨hU, ht⟩ := isUnitaryCircuit_gate U C |>.mp hC
      have hh := ih ht (fun x => U *ᵥ states x) (fun x => normalized_applyGate hU (hs x))
      simpa only [Run, QueryCount,
        negative_adversary_same_gate_progress_invariant X _ Gamma weight states U hU] using! hh
    | query =>
      have ht := isUnitaryCircuit_query C |>.mp hC
      let next := fun x => alphabetOracle (W := W) (input x) *ᵥ states x
      have hh :=
          ih ht next (fun x => normalized_applyGate (alphabet_oracle_actual_unitarity_and_filter W n a _) (hs x))
      have hstep :=
          alphabet_adversary_same_query_progress X W n a input Gamma weight states B hG hw hs hB hfilter
      have htri := abs_sub_le
        (advProgress Gamma weight (fun x => Run (alphabetOracle (W := W) (input x)) C (next x)))
        (advProgress Gamma weight next) (advProgress Gamma weight states)
      simp only [Run, ApplyGate, QueryCount, Nat.cast_add, Nat.cast_one]
      dsimp [next] at *
      linarith

theorem multioutput_adversary_actual_circuit_lower_bound
    (X W Y : Type) [Fintype X] [DecidableEq X] [Nonempty X] [Fintype W] [DecidableEq W]
    [Fintype Y] [DecidableEq Y]
    (n a : ℕ) [NeZero a] (input : X → Fin n → ZMod a) (Gamma : Matrix X X ℂ) (f : X → Y)
    (label : ((Fin n × ZMod a) × W) → Y)
    (C : Circuit ((Fin n × ZMod a) × W)) (psi : QState ((Fin n × ZMod a) × W))
    (eps B : ℝ) (hG : Gamma.IsHermitian)
    (hz : ∀ x y, f x = f y → Gamma x y = 0) (hC : IsUnitaryCircuit C)
    (hpsi : Normalized psi) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2) (hB : 0 ≤ B) (hfilter : ∀ i, ‖alphabetFilter input Gamma i‖ ≤ B)
    (hsuccess : ∀ x, 1 - eps ≤ MeasureProb
      (Run (alphabetOracle (W := W) (input x)) C psi) (Finset.univ.filter (fun h => label h = f x))) :
    (1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) * ‖Gamma‖ ≤
      2 * (QueryCount C) * B := by
  obtain ⟨weight, lam, hw, hlam, _, hstart⟩ :=
    negative_adversary_extreme_eigenvector_and_start X _ Gamma psi hG hpsi
  have hrun := alphabetProgress_run_bound X W n a input Gamma weight B hB hfilter C hG hw hC
    (fun _ => psi) (fun _ => hpsi)
  rw [hstart] at hrun
  have hout := multioutput_adversary_actual_final_progress X _ Y Gamma weight
    (fun x => Run (alphabetOracle (W := W) (input x)) C psi) f label eps hG hw
    (fun x => hC.normalized_run (alphabet_oracle_actual_unitarity_and_filter W n a _) hpsi) hz he0 he1 hsuccess
  have htri := abs_sub_le lam
    (advProgress Gamma weight (fun x => Run (alphabetOracle (W := W) (input x)) C psi)) 0
  rw [sub_zero, sub_zero, abs_sub_comm lam] at htri
  rw [hlam] at htri
  nlinarith

end Qatlib.Concepts.QueryComplexity.DegreeMethod
