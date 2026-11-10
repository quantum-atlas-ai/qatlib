/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Mathlib.Analysis.Matrix.Spectrum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 4096
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.QueryWordCore.QueryMachinery
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

noncomputable def advFilter {X : Type} {n : ℕ} (input : X  → Fin n  → Bool)
    (Gamma : Matrix X X ℂ) (i : Fin n) : Matrix X X ℂ :=
  fun x y => if input x i ≠ input y i then Gamma x y else 0

noncomputable def advFilterBound {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X  → Fin n  → Bool) (Gamma : Matrix X X ℂ) : ℝ :=
  (List.ofFn (fun i : Fin n => ‖advFilter input Gamma i‖)).foldl max 0

noncomputable def advProgress {X H : Type} [Fintype X] [Fintype H]
    (Gamma : Matrix X X ℂ) (weight : QState X) (states : X  → QState H) : ℝ :=
  (∑ x : X,∑ y : X,star (weight x)*Gamma x y*weight y*Qatlib.Foundations.PureStateMath.Inner (states x) (states y)).re

theorem advProgress_start {X H : Type} [Fintype X] [Fintype H]
    (Gamma : Matrix X X ℂ) (weight : QState X) (psi : QState H)
    (hpsi : Normalized psi) :
    advProgress Gamma weight (fun _ => psi) = (Qatlib.Foundations.PureStateMath.Inner weight (Gamma *ᵥ weight)).re := by
  rw [advProgress, (normalized_iff_inner_self _).mp hpsi]
  congr 1
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Matrix.mulVec, Pi.star_apply,
      Finset.mul_sum, mul_one]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem negative_adversary_extreme_eigenvector_and_start
    (X H : Type) [Fintype X] [DecidableEq X] [Nonempty X] [Fintype H]
    (Gamma : Matrix X X ℂ) (psi : QState H) (hG : Gamma.IsHermitian)
    (hpsi : Normalized psi) :
    ∃ (weight : QState X) (lam : ℝ), Normalized weight ∧ |lam| = ‖Gamma‖ ∧
      Gamma *ᵥ weight = (lam : ℂ) • weight ∧
      advProgress Gamma weight (fun _ => psi) = lam := by
  classical
  let ev : X → ℂ := fun i => (hG.eigenvalues i : ℂ)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖ev i‖)
    Finset.univ_nonempty
  have hn : ‖ev‖ = |hG.eigenvalues i| := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      intro j
      simpa [ev, Complex.norm_real] using hi j (Finset.mem_univ j)
    · simpa [ev, Complex.norm_real] using norm_le_pi_norm ev i
  have hnorm : ‖Gamma‖ = ‖ev‖ := by
    conv_lhs => rw [hG.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    change ‖(hG.eigenvectorUnitary : Matrix X X ℂ) * Matrix.diagonal ev *
      (star hG.eigenvectorUnitary : unitary (Matrix X X ℂ))‖ = ‖ev‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
  let weight : QState X := ⇑(hG.eigenvectorBasis i)
  have hw : Normalized weight := (normalized_iff_norm_toEuclidean_fromVec _).mpr
    (hG.eigenvectorBasis.orthonormal.1 i)
  have he : Gamma *ᵥ weight = (hG.eigenvalues i : ℂ) • weight := by
    simpa only [RCLike.real_smul_eq_coe_smul] using! hG.mulVec_eigenvectorBasis i
  refine ⟨weight, hG.eigenvalues i, hw, (hnorm.trans hn).symm, he, ?_⟩
  rw [advProgress_start _ _ _ hpsi, he]
  rw [Qatlib.Foundations.PureStateMath.Inner, dotProduct_smul]
  change ((hG.eigenvalues i : ℂ) * Qatlib.Foundations.PureStateMath.Inner weight weight).re = _
  rw [(normalized_iff_inner_self _).mp hw, mul_one, Complex.ofReal_re]

theorem negative_adversary_same_gate_progress_invariant
    (X H : Type) [Fintype X] [Fintype H] [DecidableEq H]
    (Gamma : Matrix X X ℂ) (weight : QState X) (states : X → QState H)
    (U : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    advProgress Gamma weight (fun x => U *ᵥ states x) =
      advProgress Gamma weight states := by
  unfold advProgress
  simp only [show ∀ x y, Qatlib.Foundations.PureStateMath.Inner (U *ᵥ states x) (U *ᵥ states y) =
    Qatlib.Foundations.PureStateMath.Inner (states x) (states y) from fun x y => inner_applyGate hU _ _]

noncomputable def advStack {X H : Type} (weight : QState X) (states : X → QState H) :
    QState (X × H) := fun p => weight p.1 * states p.1 p.2

theorem advTensor_mulVec {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] (Gamma : Matrix X X ℂ) (v : QState (X × H))
    (x : X) (h : H) :
    (TensorGate Gamma (1 : Matrix H H ℂ) *ᵥ v) (x, h) =
      ∑ y, Gamma x y * v (y, h) := by
  simp only [TensorGate, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single h]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem advProgress_stack {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] (Gamma : Matrix X X ℂ) (weight : QState X)
    (states : X → QState H) :
    advProgress Gamma weight states =
      (Qatlib.Foundations.PureStateMath.Inner (advStack weight states)
        (TensorGate Gamma (1 : Matrix H H ℂ) *ᵥ advStack weight states)).re := by
  unfold advProgress
  congr 1
  simp only [inner_apply, Fintype.sum_prod_type, advTensor_mulVec, advStack,
    map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Finset.sum_congr rfl fun h _ => by simp only [RCLike.star_def]; ring

theorem advStack_normalized {X H : Type} [Fintype X] [Fintype H]
    (weight : QState X) (states : X → QState H) (hw : Normalized weight)
    (hs : ∀ x, Normalized (states x)) : Normalized (advStack weight states) := by
  unfold Normalized at *
  simp only [advStack, Fintype.sum_prod_type, norm_mul, mul_pow,
    ← Finset.mul_sum, hs, mul_one, hw]

theorem adv_inner_matrix_bound {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I J ℂ) (u : QState I) (v : QState J) :
    ‖Qatlib.Foundations.PureStateMath.Inner u (A *ᵥ v)‖ ≤ ‖A‖ * ‖toEuclidean_fromVec u‖ * ‖toEuclidean_fromVec v‖ := by
  rw [← inner_euclidean_fromVec]
  calc _ ≤ ‖toEuclidean_fromVec u‖ * ‖toEuclidean_fromVec (A *ᵥ v)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖toEuclidean_fromVec u‖ * (‖A‖ * ‖toEuclidean_fromVec v‖) :=
      mul_le_mul_of_nonneg_left (l2_norm_mulVec_fromVec_le A v) (norm_nonneg _)
    _ = _ := by ring

noncomputable def advCorrect {X H : Type} [Fintype H] [DecidableEq H] (f : X → Bool)
    (E : Finset H) (v : QState (X × H)) : QState (X × H) :=
  fun p => if p.2 ∈ (if f p.1 then E else Eᶜ) then v p else 0

noncomputable def advError {X H : Type} [Fintype H] [DecidableEq H] (f : X → Bool)
    (E : Finset H) (v : QState (X × H)) : QState (X × H) :=
  fun p => if p.2 ∈ (if f p.1 then E else Eᶜ) then 0 else v p

private theorem adv_correct_add_error {X H : Type} [Fintype H] [DecidableEq H]
    (f : X → Bool) (E : Finset H) (v : QState (X × H)) :
    advCorrect f E v + advError f E v = v := by
  ext p
  simp only [Pi.add_apply, advCorrect, advError]
  by_cases hp : p.2 ∈ (if f p.1 then E else Eᶜ) <;> simp [hp]

private theorem adv_output_diagonal_zero {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] (Gamma : Matrix X X ℂ) (f : X → Bool)
    (E : Finset H) (v : QState (X × H))
    (hz : ∀ x y, f x = f y → Gamma x y = 0) :
    Qatlib.Foundations.PureStateMath.Inner (advCorrect f E v) (TensorGate Gamma (1 : Matrix H H ℂ) *ᵥ advCorrect f E v) = 0 ∧
    Qatlib.Foundations.PureStateMath.Inner (advError f E v) (TensorGate Gamma (1 : Matrix H H ℂ) *ᵥ advError f E v) = 0 := by
  constructor <;>
    simp only [inner_apply, Fintype.sum_prod_type, advTensor_mulVec, Finset.mul_sum] <;>
    apply Finset.sum_eq_zero <;> intro x _ <;>
    apply Finset.sum_eq_zero <;> intro h _ <;>
    apply Finset.sum_eq_zero <;> intro y _
  · by_cases hf : f x = f y
    · simp [hz x y hf]
    · cases hx : f x <;> cases hy : f y <;> try { exact (hf (hx.trans hy.symm)).elim }
      all_goals by_cases hh : h ∈ E <;> simp [advCorrect, hx, hy, hh]
  · by_cases hf : f x = f y
    · simp [hz x y hf]
    · cases hx : f x <;> cases hy : f y <;> try { exact (hf (hx.trans hy.symm)).elim }
      all_goals by_cases hh : h ∈ E <;> simp [advError, hx, hy, hh]

private theorem adv_output_energy {X H : Type} [Fintype X] [Fintype H]
    [DecidableEq H] (f : X → Bool) (E : Finset H) (v : QState (X × H)) :
    ‖toEuclidean_fromVec (advCorrect f E v)‖ ^ 2 +
      ‖toEuclidean_fromVec (advError f E v)‖ ^ 2 = ‖toEuclidean_fromVec v‖ ^ 2 := by
  simp only [norm_toEuclidean_fromVec_sq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [advCorrect, advError]
  by_cases hp : p.2 ∈ (if f p.1 then E else Eᶜ) <;> simp [hp]

private theorem adv_correct_mass {X H : Type} [Fintype X] [Fintype H]
    [DecidableEq H] (f : X → Bool) (E : Finset H) (weight : QState X)
    (states : X → QState H) :
    ‖toEuclidean_fromVec (advCorrect f E (advStack weight states))‖ ^ 2 =
      ∑ x, ‖weight x‖ ^ 2 * MeasureProb (states x) (if f x then E else Eᶜ) := by
  rw [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp only [advCorrect, advStack, MeasureProb, BornProb, Finset.mul_sum]
  simp only [apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr (by ext h; simp)
  intro h hh
  simp only [norm_mul, mul_pow]

theorem negative_adversary_boolean_actual_output_progress
    (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    (Gamma : Matrix X X ℂ) (weight : QState X) (states : X → QState H)
    (f : X → Bool) (E : Finset H) (eps : ℝ) (_hG : Gamma.IsHermitian)
    (hw : Normalized weight) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2) (hs : ∀ x, Normalized (states x))
    (hsuccess : ∀ x, 1 - eps ≤ MeasureProb (states x) (if f x then E else Eᶜ)) :
    |advProgress Gamma weight states| ≤ 2 * Real.sqrt (eps * (1 - eps)) * ‖Gamma‖ := by
  classical
  let v := advStack weight states
  let c := advCorrect f E v
  let b := advError f E v
  let A : Matrix (X × H) (X × H) ℂ := TensorGate Gamma 1
  have hv : ‖toEuclidean_fromVec v‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (advStack_normalized _ _ hw hs)
  have hcb : c + b = v := adv_correct_add_error _ _ _
  obtain ⟨hcc, hbb⟩ := adv_output_diagonal_zero Gamma f E v hz
  have hform : Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v) = Qatlib.Foundations.PureStateMath.Inner c (A *ᵥ b) + Qatlib.Foundations.PureStateMath.Inner b (A *ᵥ c) := by
    rw [← hcb, Matrix.mulVec_add]
    simp only [Qatlib.Foundations.PureStateMath.Inner, star_add, add_dotProduct,
        dotProduct_add] at *
    rw [hcc, hbb]
    ring
  have hA : ‖A‖ ≤ ‖Gamma‖ := by
    dsimp [A]
    rw [l2_norm_tensorGate]
    exact (mul_le_mul_of_nonneg_left l2_norm_one_le (norm_nonneg _)).trans_eq (mul_one _)
  have henergy : ‖toEuclidean_fromVec c‖ ^ 2 + ‖toEuclidean_fromVec b‖ ^ 2 = 1 := by
    simpa only [hv, one_pow] using adv_output_energy f E v
  have hcmass : 1 - eps ≤ ‖toEuclidean_fromVec c‖ ^ 2 := by
    rw [adv_correct_mass]
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
  rw [advProgress_stack]
  calc |(Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)).re| ≤ ‖Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖Qatlib.Foundations.PureStateMath.Inner c (A *ᵥ b)‖ + ‖Qatlib.Foundations.PureStateMath.Inner b (A *ᵥ c)‖ := by rw [hform]; exact norm_add_le _ _
    _ ≤ ‖A‖ * ‖toEuclidean_fromVec c‖ * ‖toEuclidean_fromVec b‖ +
        ‖A‖ * ‖toEuclidean_fromVec b‖ * ‖toEuclidean_fromVec c‖ :=
      add_le_add (adv_inner_matrix_bound _ _ _) (adv_inner_matrix_bound _ _ _)
    _ = 2 * (‖toEuclidean_fromVec c‖ * ‖toEuclidean_fromVec b‖) * ‖A‖ := by ring
    _ ≤ 2 * Real.sqrt (eps * (1 - eps)) * ‖Gamma‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprod (by norm_num)) hA
        (norm_nonneg _) (by positivity)

private theorem adv_form_expand {X H : Type} [Fintype X] [DecidableEq X]
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

private noncomputable def advFlip {X W : Type} (f : X → Bool)
    (v : QState (X × (Bool × W))) : QState (X × (Bool × W)) :=
  fun p => v (p.1, (p.2.1 ^^ f p.1, p.2.2))

private theorem advFlip_inner {X W : Type} [Fintype W] (f : X → Bool)
    (v : QState (X × (Bool × W))) (x y : X) (hxy : f x = f y) :
    Qatlib.Foundations.PureStateMath.Inner (fun h => advFlip f v (x, h)) (fun h => advFlip f v (y, h)) =
      Qatlib.Foundations.PureStateMath.Inner (fun h => v (x, h)) (fun h => v (y, h)) := by
  simp only [inner_apply, Fintype.sum_prod_type, Fintype.sum_bool, advFlip, hxy]
  cases f y <;> simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true]
  all_goals first | rfl | exact add_comm _ _

private theorem advFlip_norm {X W : Type} [Fintype X] [Fintype W]
    (f : X → Bool) (v : QState (X × (Bool × W))) :
    ‖toEuclidean_fromVec (advFlip f v)‖ = ‖toEuclidean_fromVec v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type, Fintype.sum_bool, advFlip]
  apply Finset.sum_congr rfl
  intro x _
  cases f x <;> simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true]
  all_goals first | rfl | exact add_comm _ _

private theorem advFlip_filter_difference {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] (f : X → Bool) (Gamma : Matrix X X ℂ)
    (v : QState (X × (Bool × W))) :
    Qatlib.Foundations.PureStateMath.Inner (advFlip f v) (TensorGate Gamma 1 *ᵥ advFlip f v) - Qatlib.Foundations.PureStateMath.Inner v (TensorGate Gamma 1 *ᵥ v) =
      Qatlib.Foundations.PureStateMath.Inner (advFlip f v) (TensorGate (fun x y => if f x ≠ f y then Gamma x y else 0) 1 *ᵥ advFlip f v) -
        Qatlib.Foundations.PureStateMath.Inner v (TensorGate (fun x y => if f x ≠ f y then Gamma x y else 0) 1 *ᵥ v) := by
  simp only [adv_form_expand, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hf : f x = f y
  · simp only [hf, ne_eq, not_true_eq_false, if_false, zero_mul,
      advFlip_inner f v x y hf, sub_self]
  · simp [hf]

private theorem advFlip_progress_bound {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] (f : X → Bool) (Gamma : Matrix X X ℂ)
    (v : QState (X × (Bool × W))) :
    |(Qatlib.Foundations.PureStateMath.Inner (advFlip f v) (TensorGate Gamma 1 *ᵥ advFlip f v) -
      Qatlib.Foundations.PureStateMath.Inner v (TensorGate Gamma 1 *ᵥ v)).re| ≤
      let G : Matrix X X ℂ := fun x y => if f x ≠ f y then Gamma x y else 0
      2 * ‖G‖ * ‖toEuclidean_fromVec v‖ ^ 2 := by
  let G : Matrix X X ℂ := fun x y => if f x ≠ f y then Gamma x y else 0
  let A : Matrix (X × (Bool × W)) (X × (Bool × W)) ℂ := TensorGate G 1
  have hA : ‖A‖ ≤ ‖G‖ := by
    dsimp [A]
    rw [l2_norm_tensorGate]
    exact (mul_le_mul_of_nonneg_left l2_norm_one_le (norm_nonneg _)).trans_eq (mul_one _)
  rw [advFlip_filter_difference]
  calc _ ≤ ‖Qatlib.Foundations.PureStateMath.Inner (advFlip f v) (A *ᵥ advFlip f v) - Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖Qatlib.Foundations.PureStateMath.Inner (advFlip f v) (A *ᵥ advFlip f v)‖ + ‖Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖toEuclidean_fromVec (advFlip f v)‖ * ‖toEuclidean_fromVec (advFlip f v)‖ +
        ‖A‖ * ‖toEuclidean_fromVec v‖ * ‖toEuclidean_fromVec v‖ :=
      add_le_add (adv_inner_matrix_bound _ _ _) (adv_inner_matrix_bound _ _ _)
    _ = 2 * ‖A‖ * ‖toEuclidean_fromVec v‖ ^ 2 := by rw [advFlip_norm]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num)) (sq_nonneg _)

noncomputable def advSlice {X W : Type} {n : ℕ} (weight : QState X)
    (states : X → QState ((Fin n × Bool) × W)) (i : Fin n) : QState (X × (Bool × W)) :=
  fun p => weight p.1 * states p.1 ((i, p.2.1), p.2.2)

private theorem advProgress_slices {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] {n : ℕ} (Gamma : Matrix X X ℂ) (weight : QState X)
    (states : X → QState ((Fin n × Bool) × W)) :
    advProgress Gamma weight states =
      (∑ i, Qatlib.Foundations.PureStateMath.Inner (advSlice weight states i)
        (TensorGate Gamma (1 : Matrix (Bool × W) (Bool × W) ℂ) *ᵥ advSlice weight states i)).re := by
  unfold advProgress
  congr 1
  simp_rw [adv_form_expand]
  simp only [inner_apply, Fintype.sum_prod_type, advSlice, map_mul, Finset.mul_sum]
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

private theorem advSlice_query {X W : Type} [Fintype W] [DecidableEq W]
    {n : ℕ} (input : X → Fin n → Bool) (weight : QState X)
    (states : X → QState ((Fin n × Bool) × W)) (i : Fin n) :
    advSlice weight (fun x => workspaceBitOracle (W := W) (input x) *ᵥ states x) i =
      advFlip (fun x => input x i) (advSlice weight states i) := by
  ext p
  simp only [advSlice, advFlip]
  rw [show (workspaceBitOracle (W := W) (input p.1) *ᵥ states p.1) ((i, p.2.1), p.2.2) =
    states p.1 ((i, p.2.1 ^^ input p.1 i), p.2.2) from
      applyGate_workspaceBitOracle_mk _ _ _ _ _]

private theorem advSlice_energy {X W : Type} [Fintype X] [Fintype W] {n : ℕ}
    (weight : QState X) (states : X → QState ((Fin n × Bool) × W))
    (hw : Normalized weight) (hs : ∀ x, Normalized (states x)) :
    ∑ i, ‖toEuclidean_fromVec (advSlice weight states i)‖ ^ 2 = 1 := by
  simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type, advSlice, norm_mul,
    mul_pow, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hsn : ∀ x, (∑ i, ∑ b, ∑ w, ‖states x ((i, b), w)‖ ^ 2) = 1 := by
    intro x
    simpa only [Normalized, Fintype.sum_prod_type] using hs x
  simp only [hsn, mul_one]
  exact hw

private theorem advFilter_le_bound {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (Gamma : Matrix X X ℂ) (i : Fin n) :
    ‖advFilter input Gamma i‖ ≤ advFilterBound input Gamma := by
  unfold advFilterBound
  have hmem : ‖advFilter input Gamma i‖ ∈ List.ofFn (fun j : Fin n => ‖advFilter input Gamma j‖) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have helper : ∀ (l : List ℝ) (a z : ℝ), a ∈ l → a ≤ l.foldl max z := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      intro a z ha
      rcases List.mem_cons.mp ha with rfl | ha
      · have hm : ∀ (l : List ℝ) (z : ℝ), z ≤ l.foldl max z := by
          intro l
          induction l with
          | nil => intro z; exact le_rfl
          | cons b l ih => intro z; exact (le_max_left _ _).trans (ih _)
        exact (le_max_right z a).trans (hm l _)
      · exact ih a (max z b) ha
  exact helper _ _ _ hmem

theorem negative_adversary_actual_workspace_bit_query_step
    (X W : Type) [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W] (n : ℕ)
    (input : X → Fin n → Bool) (Gamma : Matrix X X ℂ) (weight : QState X)
    (states : X → QState ((Fin n × Bool) × W)) (_hG : Gamma.IsHermitian)
    (hw : Normalized weight) (hs : ∀ x, Normalized (states x)) :
    |advProgress Gamma weight (fun x => workspaceBitOracle (W := W) (input x) *ᵥ states x) -
      advProgress Gamma weight states| ≤ 2 * advFilterBound input Gamma := by
  rw [advProgress_slices, advProgress_slices, ← Complex.sub_re, ← Finset.sum_sub_distrib]
  simp only [advSlice_query, Complex.re_sum]
  calc _ ≤ ∑ i, |(Qatlib.Foundations.PureStateMath.Inner (advFlip (fun x => input x i) (advSlice weight states i))
        (TensorGate Gamma 1 *ᵥ advFlip (fun x => input x i) (advSlice weight states i)) -
          Qatlib.Foundations.PureStateMath.Inner (advSlice weight states i) (TensorGate Gamma 1 *ᵥ advSlice weight states i)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * ‖advFilter input Gamma i‖ * ‖toEuclidean_fromVec (advSlice weight states i)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => advFlip_progress_bound _ _ _
    _ ≤ ∑ i, 2 * advFilterBound input Gamma * ‖toEuclidean_fromVec (advSlice weight states i)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (advFilter_le_bound input Gamma i) (by norm_num)) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, advSlice_energy weight states hw hs, mul_one]

theorem advProgress_run_bound
    (X W : Type) [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W] (n : ℕ)
    (input : X → Fin n → Bool) (Gamma : Matrix X X ℂ) (weight : QState X)
    (C : Circuit ((Fin n × Bool) × W)) (hG : Gamma.IsHermitian) (hw : Normalized weight)
    (hC : IsUnitaryCircuit C) (states : X → QState ((Fin n × Bool) × W))
    (hs : ∀ x, Normalized (states x)) :
    |advProgress Gamma weight (fun x => Run (workspaceBitOracle (W := W) (input x)) C (states x)) -
      advProgress Gamma weight states| ≤ 2 * (QueryCount C) * advFilterBound input Gamma := by
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
      let next := fun x => workspaceBitOracle (W := W) (input x) *ᵥ states x
      have hh := ih ht next (fun x => normalized_applyGate (workspaceBitOracle_unitary _) (hs x))
      have hstep :=
          negative_adversary_actual_workspace_bit_query_step X W n input Gamma weight states hG hw hs
      have htri := abs_sub_le
        (advProgress Gamma weight (fun x => Run (workspaceBitOracle (W := W) (input x)) C (next x)))
        (advProgress Gamma weight next) (advProgress Gamma weight states)
      simp only [Run, ApplyGate, QueryCount, Nat.cast_add, Nat.cast_one]
      dsimp [next] at *
      linarith

theorem negative_adversary_actual_bounded_error_circuit_lower_bound
    (X W : Type) [Fintype X] [DecidableEq X] [Nonempty X] [Fintype W] [DecidableEq W]
    (n : ℕ) (input : X → Fin n → Bool) (Gamma : Matrix X X ℂ) (f : X → Bool)
    (C : Circuit ((Fin n × Bool) × W)) (psi : QState ((Fin n × Bool) × W))
    (E : Finset ((Fin n × Bool) × W)) (eps : ℝ) (hG : Gamma.IsHermitian)
    (hz : ∀ x y, f x = f y → Gamma x y = 0) (hC : IsUnitaryCircuit C)
    (hpsi : Normalized psi) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hsuccess : ∀ x, 1 - eps ≤ MeasureProb
      (Run (workspaceBitOracle (W := W) (input x)) C psi) (if f x then E else Eᶜ)) :
    (1 - 2 * Real.sqrt (eps * (1 - eps))) * ‖Gamma‖ ≤
      2 * (QueryCount C) * advFilterBound input Gamma := by
  obtain ⟨weight, lam, hw, hlam, _, hstart⟩ :=
    negative_adversary_extreme_eigenvector_and_start X _ Gamma psi hG hpsi
  have hrun := advProgress_run_bound X W n input Gamma weight C hG hw hC
    (fun _ => psi) (fun _ => hpsi)
  rw [hstart] at hrun
  have hout := negative_adversary_boolean_actual_output_progress X _ Gamma weight
    (fun x => Run (workspaceBitOracle (W := W) (input x)) C psi) f E eps hG hw hz he0 he1
    (fun x => hC.normalized_run (workspaceBitOracle_unitary _) hpsi) hsuccess
  have htri := abs_sub_le lam
    (advProgress Gamma weight (fun x => Run (workspaceBitOracle (W := W) (input x)) C psi)) 0
  rw [sub_zero, sub_zero, abs_sub_comm lam] at htri
  rw [hlam] at htri
  nlinarith

end Qatlib.Concepts.QueryWordCore.QueryMachinery
