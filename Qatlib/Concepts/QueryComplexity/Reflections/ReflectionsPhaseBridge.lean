/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.BipartiteEffectiveGapCorrectedRefl
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Qatlib.Concepts.QueryComplexity.Reflections.TwoReflectionConstructionRefl
import Qatlib.Concepts.WalkSearch.Spectral.CompleteCSDecomposition
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped Classical BigOperators

variable {H : Type} [Fintype H] [DecidableEq H]

theorem reflections_projected_residual (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) :
    P * (1 - ReflectionAbout P * ReflectionAbout Q) = (2 : ℂ) • (P * (1 - Q)) := by
  have hPP : P * P = P := hP.1
  have hPR : P * ReflectionAbout P = P := by
    simp only [ReflectionAbout, mul_sub, mul_smul_comm, hPP, mul_one]
    module
  rw [mul_sub, mul_one, ← Matrix.mul_assoc, hPR]
  simp only [ReflectionAbout, mul_sub, mul_smul_comm, mul_one]
  module

theorem reflections_product_unitary (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) :
    ReflectionAbout P * ReflectionAbout Q ∈ Matrix.unitaryGroup H ℂ :=
  (Matrix.unitaryGroup H ℂ).mul_mem (reflectionAbout_unitary hP) (reflectionAbout_unitary hQ)

theorem reflections_common_fixed (P Q : Matrix H H ℂ) (ψ : QState H)
    (hp : P *ᵥ ψ = ψ) (hq : Q *ᵥ ψ = ψ) :
    (ReflectionAbout P * ReflectionAbout Q) *ᵥ ψ = ψ := by
  rw [← Matrix.mulVec_mulVec]
  rw [show ReflectionAbout Q *ᵥ ψ = ψ from applyGate_reflectionAbout_of_fixed hq]
  exact applyGate_reflectionAbout_of_fixed hp

variable {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}

theorem reflections_positive_unmarked_kernel
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ)
    (W : ℝ) (x : X) (hψ : sourceMarkedBiadj input f v W x *ᵥ
      sourcePositiveWitness input f v W x = 0) :
    adjacency input f v W *ᵥ Sum.elim (0 : QState (Fin0 X f)) (sourcePositiveWitness input f v W x) = 0 := by
  apply source_block_kernel
  funext r
  have hr := congrFun hψ (Sum.inl r)
  simpa only [sourceMarkedBiadj, biadj, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.fromRows_apply_inl,
    Matrix.of_apply, Pi.zero_apply] using hr

theorem reflections_positive_input_fixed
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ)
    (W : ℝ) (x : X) :
    pixProj input f x *ᵥ Sum.elim (0 : QState (Fin0 X f)) (sourcePositiveWitness input f v W x) =
      Sum.elim (0 : QState (Fin0 X f)) (sourcePositiveWitness input f v W x) := by
  funext z
  rw [pixProj, Matrix.mulVec_diagonal]
  rcases z with r | z
  · simp
  · rcases z with u | ⟨j, b, k⟩
    · simp [complementMark]
    · cases hb : input x j <;> cases b <;>
        simp [complementMark, sourcePositiveWitness, hb]

theorem reflections_true_zero_witness
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ)
    (W : ℝ) (hd : SourceDualFeasible input f v W) (hW : 1 ≤ W)
    (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ)
    (hΔ : ∀ z, adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z)
    (x : X) (hx : f x = true) :
    ∃ ψ : QState (Vertex X f n m), ψ ≠ 0 ∧
      twoReflectionUnitary input f x Δ *ᵥ ψ = ψ ∧
      (9 / 10 : ℝ) * (∑ z, ‖ψ z‖ ^ 2) ≤ ‖ψ (Sum.inr (Sum.inl ()))‖ ^ 2 := by
  have hk := (kernelWitnessCorrected X n m input f v W hd hW).1 x hx
  let ψ : QState (Vertex X f n m) :=
      Sum.elim (0 : QState (Fin0 X f)) (sourcePositiveWitness input f v W x)
  have hp : pixProj input f x *ᵥ ψ = ψ := reflections_positive_input_fixed input f v W x
  have hz : adjacency input f v W *ᵥ ψ = 0 :=
    reflections_positive_unmarked_kernel input f v W x hk.2.1
  refine ⟨ψ, ?_, reflections_common_fixed _ _ ψ hp ((hΔ ψ).mp hz), ?_⟩
  · intro hzero
    apply hk.1
    funext z
    exact congrFun hzero (Sum.inr z)
  · simpa only [ψ, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
      zero_add] using hk.2.2

theorem reflections_kernel_annihilates (B Δ : Matrix H H ℂ)
    (hB : B.IsHermitian) (hΔ : IsOrthogonalProjector Δ)
    (hk : ∀ z, B *ᵥ z = 0 ↔ Δ *ᵥ z = z) : B * Δ = 0 ∧ Δ * B = 0 := by
  have hBΔ : B * Δ = 0 := by
    ext i j
    have hid : Δ *ᵥ (Δ *ᵥ Qatlib.Foundations.PureStateMath.Ket j) = Δ *ᵥ Qatlib.Foundations.PureStateMath.Ket j := by
      rw [Matrix.mulVec_mulVec, show Δ * Δ = Δ from hΔ.1]
    have hz := (hk (Δ *ᵥ Qatlib.Foundations.PureStateMath.Ket j)).mpr hid
    have he := congrFun hz i
    rw [Matrix.mulVec_mulVec, mulVec_ket_apply] at he
    exact he
  refine ⟨hBΔ, ?_⟩
  have hs := congrArg Matrix.conjTranspose hBΔ
  simpa only [Matrix.conjTranspose_mul, hB.eq,
    show Δᴴ = Δ from hΔ.2, Matrix.conjTranspose_zero] using hs

def reflectionsFalseRow (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) : QState (Vertex X f n m)
  | .inl _ => 0
  | .inr (.inl _) => ((1 / (3 * Real.sqrt W) : ℝ) : ℂ)
  | .inr (.inr (j, b, k)) => if b = !(input x j) then v x j k else 0

theorem reflectionsFalseRow_image (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) (hx : f x = false) :
    adjacency input f v W *ᵥ Qatlib.Foundations.PureStateMath.Ket (Sum.inl ⟨x, hx⟩) =
      reflectionsFalseRow input f v W x := by
  funext z
  rw [mulVec_ket_apply]
  rcases z with r | z
  · rfl
  · rcases z with u | ⟨j, b, k⟩
    · simp [adjacency, blockAdjacency, biadj, tvec, reflectionsFalseRow]
    · by_cases hb : b = !(input x j) <;>
        simp [adjacency, blockAdjacency, biadj, bigA, reflectionsFalseRow, hb,
          RCLike.star_def]

theorem reflectionsFalseRow_input_projection (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    pixProj input f x *ᵥ reflectionsFalseRow input f v W x =
      (((1 / (3 * Real.sqrt W) : ℝ) : ℂ)) • Qatlib.Foundations.PureStateMath.Ket (Sum.inr (Sum.inl ())) := by
  funext z
  rw [pixProj, Matrix.mulVec_diagonal]
  rcases z with r | z
  · simp [reflectionsFalseRow, Qatlib.Foundations.PureStateMath.Ket]
  · rcases z with u | ⟨j, b, k⟩
    · cases u
      simp [reflectionsFalseRow, complementMark, Qatlib.Foundations.PureStateMath.Ket]
    · cases hi : input x j <;> cases b <;>
        simp [reflectionsFalseRow, complementMark, hi, Qatlib.Foundations.PureStateMath.Ket]

theorem reflections_false_resolvent (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ)
    (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ)
    (hΔ : IsOrthogonalProjector Δ)
    (hk : ∀ z, adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z)
    (x : X) (hx : f x = false) :
    (1 - twoReflectionUnitary input f x Δ) *ᵥ reflectionsFalseRow input f v W x =
      (2 * ((1 / (3 * Real.sqrt W) : ℝ) : ℂ)) • Qatlib.Foundations.PureStateMath.Ket (Sum.inr (Sum.inl ())) := by
  have hA := (twoReflectionConstruction X n m input f v W).1
  have hΔA := (reflections_kernel_annihilates (adjacency input f v W) Δ hA hΔ hk).2
  have hzero : Δ *ᵥ reflectionsFalseRow input f v W x = 0 := by
    rw [← reflectionsFalseRow_image input f v W x hx, Matrix.mulVec_mulVec, hΔA,
      Matrix.zero_mulVec]
  have hp := reflectionsFalseRow_input_projection input f v W x
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, twoReflectionUnitary,
    ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hzero, smul_zero, zero_sub, Matrix.mulVec_neg, hp, smul_smul]
  module

omit [DecidableEq X] in

theorem reflectionsFalseRow_norm (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    (∑ z, ‖reflectionsFalseRow input f v W x z‖ ^ 2) =
      (1 / (3 * Real.sqrt W)) ^ 2 + ∑ j, ∑ k, ‖v x j k‖ ^ 2 := by
  simp only [Fintype.sum_sum_type, reflectionsFalseRow, norm_zero,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_add, Fintype.sum_unique]
  rw [source_fiber_norm n m (fun j => !(input x j)) (v x),
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem reflections_false_root_inverse (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (hd : SourceDualFeasible input f v W)
    (hW : 1 ≤ W) (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ)
    (hΔ : IsOrthogonalProjector Δ)
    (hk : ∀ z, adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z)
    (x : X) (hx : f x = false) :
    ∃ η : QState (Vertex X f n m),
      (1 - twoReflectionUnitary input f x Δ) *ᵥ η = Qatlib.Foundations.PureStateMath.Ket (Sum.inr (Sum.inl ())) ∧
      (∑ z, ‖η z‖ ^ 2) ≤ (5 / 2 : ℝ) * W ^ 2 := by
  let s := Real.sqrt W
  have hw : 0 < W := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr hw
  have hs2 : s ^ 2 = W := Real.sq_sqrt hw.le
  let η := (((3 * s / 2 : ℝ) : ℂ)) • reflectionsFalseRow input f v W x
  refine ⟨η, ?_, ?_⟩
  · dsimp only [η]
    rw [Matrix.mulVec_smul, reflections_false_resolvent input f v W Δ hΔ hk x hx,
      smul_smul]
    have hc : ((3 * s / 2 : ℝ) : ℂ) *
        (2 * ((1 / (3 * Real.sqrt W) : ℝ) : ℂ)) = 1 := by
      change ((3 * s / 2 : ℝ) : ℂ) * (2 * ((1 / (3 * s) : ℝ) : ℂ)) = 1
      push_cast
      field_simp [ne_of_gt hs]
    rw [hc, one_smul]
  · have ht : (1 / (3 * s)) ^ 2 = 1 / (9 * W) := by
      rw [div_pow, mul_pow, hs2]
      norm_num
    have he : (∑ z, ‖η z‖ ^ 2) = (1 + 9 * W * (∑ j, ∑ k, ‖v x j k‖ ^ 2)) / 4 := by
      simp only [η, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, sq_abs, ← Finset.mul_sum]
      rw [reflectionsFalseRow_norm]
      change (3 * s / 2) ^ 2 * ((1 / (3 * s)) ^ 2 + _) = _
      rw [ht]
      field_simp
      nlinarith only [hs2]
    rw [he]
    have hb := mul_le_mul_of_nonneg_left (hd.1 x) hw.le
    have h1 : 1 ≤ W ^ 2 := by nlinarith
    nlinarith

section PowerMean
variable {J : Type} [Fintype J] [DecidableEq J]

def reflectionsPowerMean (τ : ℕ) (U : Matrix J J ℂ) (r : QState J) : ℝ :=
  (4 * (τ : ℝ))⁻¹ * ∑ t : Fin τ,
    ‖toEuclidean_fromVec (r + U ^ (t.val + 1) *ᵥ r)‖ ^ 2

theorem reflections_inverse_power_sum (U : Matrix J J ℂ) (η r : QState J)
    (hη : (1 - U) *ᵥ η = r) (τ : ℕ) :
    (∑ t : Fin τ, U ^ (t.val + 1) *ᵥ r) = U *ᵥ η - U ^ (τ + 1) *ᵥ η := by
  have hsum : (∑ t : Fin τ, U ^ (t.val + 1)) =
      U * (∑ k ∈ Finset.range τ, U ^ k) := by
    simp only [pow_succ', Finset.mul_sum]
    exact Fin.sum_univ_eq_sum_range (fun k => U * U ^ k) τ
  have happly : (∑ t : Fin τ, U ^ (t.val + 1) *ᵥ r) =
      (∑ t : Fin τ, U ^ (t.val + 1)) *ᵥ r := by
    funext z
    simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [happly, hsum, ← hη, Matrix.mulVec_mulVec, Matrix.mul_assoc, geom_sum_mul_neg,
    mul_sub, mul_one, ← pow_succ', Matrix.sub_mulVec]

theorem reflections_inverse_power_sum_norm (U : Matrix J J ℂ)
    (hU : U ∈ Matrix.unitaryGroup J ℂ) (η r : QState J)
    (hη : (1 - U) *ᵥ η = r) (τ : ℕ) :
    ‖toEuclidean_fromVec (∑ t : Fin τ, U ^ (t.val + 1) *ᵥ r)‖ ≤
      2 * ‖toEuclidean_fromVec η‖ := by
  rw [reflections_inverse_power_sum U η r hη τ]
  change ‖toEuclidean_fromVec (U *ᵥ η) -
    toEuclidean_fromVec (U ^ (τ + 1) *ᵥ η)‖ ≤ _
  calc
    _ ≤ ‖toEuclidean_fromVec (U *ᵥ η)‖ +
        ‖toEuclidean_fromVec (U ^ (τ + 1) *ᵥ η)‖ := norm_sub_le _ _
    _ = _ := by
      have hnU : ‖toEuclidean_fromVec (U *ᵥ η)‖ = ‖toEuclidean_fromVec η‖ :=
        norm_applyGate_of_mem_unitaryGroup hU η
      have hnP : ‖toEuclidean_fromVec (U ^ (τ + 1) *ᵥ η)‖ = ‖toEuclidean_fromVec η‖ :=
        norm_applyGate_of_mem_unitaryGroup ((Matrix.unitaryGroup J ℂ).pow_mem hU (τ + 1)) η
      rw [hnU, hnP]
      ring

theorem reflections_fixed_interference_lower (U : Matrix J J ℂ)
    (hU : U ∈ Matrix.unitaryGroup J ℂ) (ψ : QState J) (hψ : ψ ≠ 0)
    (hfix : U *ᵥ ψ = ψ) (z : J) (p : ℝ)
    (hp : p * (∑ j, ‖ψ j‖ ^ 2) ≤ ‖ψ z‖ ^ 2) (k : ℕ) :
    4 * p ≤ ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket z + U ^ k *ᵥ Qatlib.Foundations.PureStateMath.Ket z)‖ ^ 2 := by
  have hpow : U ^ k *ᵥ ψ = ψ := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hfix]
  have hu := (Matrix.unitaryGroup J ℂ).pow_mem hU k
  have hi : Qatlib.Foundations.PureStateMath.Inner ψ (U ^ k *ᵥ Qatlib.Foundations.PureStateMath.Ket z) = Qatlib.Foundations.PureStateMath.Inner ψ (Qatlib.Foundations.PureStateMath.Ket z) := by
    have he := inner_applyGate hu ψ (Qatlib.Foundations.PureStateMath.Ket z)
    simpa only [ApplyGate, hpow] using he
  have hsum : Qatlib.Foundations.PureStateMath.Inner ψ (Qatlib.Foundations.PureStateMath.Ket z + U ^ k *ᵥ Qatlib.Foundations.PureStateMath.Ket z) = 2 * Qatlib.Foundations.PureStateMath.Inner ψ (Qatlib.Foundations.PureStateMath.Ket z) := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct_add] at hi ⊢
    rw [hi]
    ring
  have hk : ‖Qatlib.Foundations.PureStateMath.Inner ψ (Qatlib.Foundations.PureStateMath.Ket z)‖ = ‖ψ z‖ := by
    simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct,
        Qatlib.Foundations.PureStateMath.Ket]
  have hc := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec ψ)
    (toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket z + U ^ k *ᵥ Qatlib.Foundations.PureStateMath.Ket z))
  rw [inner_euclidean_fromVec, hsum, norm_mul, Complex.norm_ofNat, hk] at hc
  have hs := sq_le_sq₀ (by positivity : 0 ≤ 2 * ‖ψ z‖)
    (by positivity : 0 ≤ ‖toEuclidean_fromVec ψ‖ *
      ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket z + U ^ k *ᵥ Qatlib.Foundations.PureStateMath.Ket z)‖) |>.mpr hc
  simp only [mul_pow, norm_toEuclidean_fromVec_sq] at hs
  have hn : 0 < ∑ j, ‖ψ j‖ ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hψ
    exact (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hj)).trans_le
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖ψ i‖) (Finset.mem_univ j))
  rw [norm_toEuclidean_fromVec_sq]
  nlinarith

theorem reflections_power_interference_formula (U : Matrix J J ℂ)
    (hU : U ∈ Matrix.unitaryGroup J ℂ) (r : QState J) (hr : Normalized r) (k : ℕ) :
    ‖toEuclidean_fromVec (r + U ^ k *ᵥ r)‖ ^ 2 =
      2 + 2 * (Qatlib.Foundations.PureStateMath.Inner r (U ^ k *ᵥ r)).re := by
  have hn : ‖toEuclidean_fromVec r‖ ^ 2 = 1 := by
    rw [norm_toEuclidean_fromVec_sq]
    exact hr
  have hp : ‖toEuclidean_fromVec (U ^ k *ᵥ r)‖ = ‖toEuclidean_fromVec r‖ :=
    norm_applyGate_of_mem_unitaryGroup ((Matrix.unitaryGroup J ℂ).pow_mem hU k) r
  change ‖toEuclidean_fromVec r + toEuclidean_fromVec (U ^ k *ᵥ r)‖ ^ 2 = _
  rw [norm_add_sq (𝕜 := ℂ), inner_euclidean_fromVec, hp, hn]
  change 1 + 2 * (Qatlib.Foundations.PureStateMath.Inner r (U ^ k *ᵥ r)).re + 1 = _
  ring

theorem reflections_power_mean_formula (U : Matrix J J ℂ)
    (hU : U ∈ Matrix.unitaryGroup J ℂ) (r : QState J) (hr : Normalized r)
    (τ : ℕ) (hτ : 0 < τ) :
    reflectionsPowerMean τ U r = 1 / 2 +
      (Qatlib.Foundations.PureStateMath.Inner r (∑ t : Fin τ, U ^ (t.val + 1) *ᵥ r)).re / (2 * (τ : ℝ)) := by
  have hi : Qatlib.Foundations.PureStateMath.Inner r (∑ t : Fin τ, U ^ (t.val + 1) *ᵥ r) =
      ∑ t : Fin τ, Qatlib.Foundations.PureStateMath.Inner r (U ^ (t.val + 1) *ᵥ r) := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Finset.sum_apply,
        Finset.mul_sum]
    rw [Finset.sum_comm]
  simp only [reflectionsPowerMean, reflections_power_interference_formula U hU r hr,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, hi, Complex.re_sum]
  have ht : (τ : ℝ) ≠ 0 := by exact_mod_cast hτ.ne'
  field_simp
  ring

theorem reflections_inverse_power_mean_upper (U : Matrix J J ℂ)
    (hU : U ∈ Matrix.unitaryGroup J ℂ) (η r : QState J) (hr : Normalized r)
    (hη : (1 - U) *ᵥ η = r) (τ : ℕ) (hτ : 0 < τ) :
    reflectionsPowerMean τ U r ≤ 1 / 2 + ‖toEuclidean_fromVec η‖ / (τ : ℝ) := by
  let S := ∑ t : Fin τ, U ^ (t.val + 1) *ᵥ r
  have hn : ‖toEuclidean_fromVec r‖ = 1 := by
    have hs : ‖toEuclidean_fromVec r‖ ^ 2 = 1 := by
      rw [norm_toEuclidean_fromVec_sq]
      exact hr
    nlinarith [norm_nonneg (toEuclidean_fromVec r)]
  have hc : (Qatlib.Foundations.PureStateMath.Inner r S).re ≤ 2 * ‖toEuclidean_fromVec η‖ := by
    have hcs := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec r) (toEuclidean_fromVec S)
    rw [inner_euclidean_fromVec, hn, one_mul] at hcs
    exact (Complex.re_le_norm _).trans
      (hcs.trans (reflections_inverse_power_sum_norm U hU η r hη τ))
  rw [reflections_power_mean_formula U hU r hr τ hτ]
  have ht : 0 < (τ : ℝ) := Nat.cast_pos.mpr hτ
  have hd := (div_le_div_of_nonneg_right hc (by positivity : 0 ≤ 2 * (τ : ℝ)))
  dsimp only [S] at hc
  have he : 2 * ‖toEuclidean_fromVec η‖ / (2 * (τ : ℝ)) =
      ‖toEuclidean_fromVec η‖ / (τ : ℝ) := by ring
  rw [he] at hd
  exact add_le_add_right hd (1 / 2)

end PowerMean

theorem reflections_true_power_mean (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (hd : SourceDualFeasible input f v W)
    (hW : 1 ≤ W) (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ)
    (hΔ : IsOrthogonalProjector Δ)
    (hk : ∀ z, adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z)
    (x : X) (hx : f x = true) (τ : ℕ) (hτ : 0 < τ) :
    (9 / 10 : ℝ) ≤ reflectionsPowerMean τ (twoReflectionUnitary input f x Δ)
      (Qatlib.Foundations.PureStateMath.Ket (Sum.inr (Sum.inl ()))) := by
  obtain ⟨ψ, hn, hfix, hover⟩ := reflections_true_zero_witness input f v W hd hW Δ hk x hx
  have hp := (twoReflectionConstruction X n m input f v W).2.1 x
  have hU := reflections_product_unitary _ _ hp hΔ
  have hb (t : Fin τ) := reflections_fixed_interference_lower
    (twoReflectionUnitary input f x Δ) hU ψ hn hfix
    (Sum.inr (Sum.inl ())) (9 / 10) hover (t.val + 1)
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin τ))) => hb t)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [reflectionsPowerMean, ← div_eq_inv_mul]
  apply (le_div_iff₀ (by positivity : 0 < 4 * (τ : ℝ))).mpr
  nlinarith

theorem reflections_false_power_mean (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (hd : SourceDualFeasible input f v W)
    (hW : 1 ≤ W) (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ)
    (hΔ : IsOrthogonalProjector Δ)
    (hk : ∀ z, adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z)
    (x : X) (hx : f x = false) :
    reflectionsPowerMean (4000 * Nat.ceil W) (twoReflectionUnitary input f x Δ)
      (Qatlib.Foundations.PureStateMath.Ket (Sum.inr (Sum.inl ()))) ≤ (3 / 5 : ℝ) := by
  obtain ⟨η, he, hn⟩ := reflections_false_root_inverse input f v W hd hW Δ hΔ hk x hx
  have hp := (twoReflectionConstruction X n m input f v W).2.1 x
  have hU := reflections_product_unitary _ _ hp hΔ
  have hw : 0 < W := by linarith
  have hτ : 0 < 4000 * Nat.ceil W := Nat.mul_pos (by decide) (Nat.ceil_pos.mpr hw)
  have hm := reflections_inverse_power_mean_upper (twoReflectionUnitary input f x Δ) hU
    η (Qatlib.Foundations.PureStateMath.Ket (Sum.inr (Sum.inl ()))) (normalized_ket _) he (4000 * Nat.ceil W) hτ
  have hnorm : ‖toEuclidean_fromVec η‖ ≤ 2 * W := by
    rw [← norm_toEuclidean_fromVec_sq] at hn
    nlinarith [norm_nonneg (toEuclidean_fromVec η), sq_nonneg W]
  have hcost : W ≤ (Nat.ceil W : ℝ) := Nat.le_ceil W
  have ht : 0 < (4000 * Nat.ceil W : ℕ) := hτ
  have htail : ‖toEuclidean_fromVec η‖ / (4000 * Nat.ceil W : ℕ) ≤ (1 / 10 : ℝ) := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr ht)).mpr
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  linarith

section PhaseMass
variable {J : Type} [Fintype J] [DecidableEq J]

theorem reflections_inverse_phase_mass (U : Matrix H H ℂ) (r η : QState H)
    (V : Matrix H J ℂ) (θ : J → ℝ) (hV : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V) (hfull : V * Vᴴ = 1)
    (hEV : U * V = V * Matrix.diagonal (fun i => Complex.exp (Complex.I * θ i)))
    (hη : (1 - U) *ᵥ η = r) (hr : Normalized r) (Θ : ℝ) (hΘ : 0 ≤ Θ) :
    (∑ i ∈ Finset.univ.filter (fun i => |θ i| ≤ Θ), ‖(Vᴴ *ᵥ r) i‖ ^ 2) ≤ 1 ∧
    (∑ i ∈ Finset.univ.filter (fun i => |θ i| ≤ Θ), ‖(Vᴴ *ᵥ r) i‖ ^ 2) ≤
      Θ ^ 2 * ∑ z, ‖η z‖ ^ 2 := by
  let D := Matrix.diagonal (fun i => Complex.exp (Complex.I * θ i))
  have hL : Vᴴ * U = D * Vᴴ := by
    calc
      _ = (Vᴴ * U) * (V * Vᴴ) := by rw [hfull, Matrix.mul_one]
      _ = Vᴴ * (U * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = Vᴴ * (V * D) * Vᴴ := by rw [hEV]
      _ = (Vᴴ * V) * (D * Vᴴ) := by simp only [Matrix.mul_assoc]
      _ = D * Vᴴ := by rw [hV, Matrix.one_mul]
  have he : Vᴴ *ᵥ r = Vᴴ *ᵥ η - D *ᵥ (Vᴴ *ᵥ η) := by
    rw [← hη, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hL,
      Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
  have hcoef (i : J) : (Vᴴ *ᵥ r) i =
      (1 - Complex.exp (Complex.I * θ i)) * (Vᴴ *ᵥ η) i := by
    have hi := congrFun he i
    simp only [Pi.sub_apply, D, Matrix.mulVec_diagonal] at hi
    rw [hi]
    ring
  have hVi : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry Vᴴ := by
    simpa only [Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry,
        Matrix.conjTranspose_conjTranspose] using hfull
  have hrmass :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.measureProb_mulVec hVi r
  have hηmass :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.measureProb_mulVec hVi η
  change (∑ i, ‖(Vᴴ *ᵥ r) i‖ ^ 2) = ∑ z, ‖r z‖ ^ 2 at hrmass
  change (∑ i, ‖(Vᴴ *ᵥ η) i‖ ^ 2) = ∑ z, ‖η z‖ ^ 2 at hηmass
  constructor
  · calc
      _ ≤ ∑ i, ‖(Vᴴ *ᵥ r) i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => sq_nonneg _)
      _ = 1 := hrmass.trans hr
  · calc
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => |θ i| ≤ Θ),
          Θ ^ 2 * ‖(Vᴴ *ᵥ η) i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have ht := (Finset.mem_filter.mp hi).2
        have hc : ‖1 - Complex.exp (Complex.I * θ i)‖ ≤ Θ := by
          calc
            _ = ‖Complex.exp (Complex.I * θ i) - 1‖ := norm_sub_rev _ _
            _ ≤ |θ i| := Real.norm_exp_I_mul_ofReal_sub_one_le
            _ ≤ Θ := ht
        rw [hcoef, norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (sq_le_sq₀ (norm_nonneg _) hΘ |>.mpr hc) (sq_nonneg _)
      _ ≤ ∑ i, Θ ^ 2 * ‖(Vᴴ *ᵥ η) i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = Θ ^ 2 * ∑ z, ‖η z‖ ^ 2 := by rw [← Finset.mul_sum, hηmass]

end PhaseMass

theorem reflections_false_root_phase (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (hd : SourceDualFeasible input f v W)
    (hW : 1 ≤ W) (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ)
    (hΔ : IsOrthogonalProjector Δ)
    (hk : ∀ z, adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z)
    (x : X) (hx : f x = false) (J : Type) [Fintype J] [DecidableEq J]
    (V : Matrix (Vertex X f n m) J ℂ) (θ : J → ℝ)
    (hV : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V) (hfull : V * Vᴴ = 1)
    (hEV : twoReflectionUnitary input f x Δ * V =
      V * Matrix.diagonal (fun i => Complex.exp (Complex.I * θ i)))
    (Θ : ℝ) (hΘ : 0 ≤ Θ) :
    (∑ i ∈ Finset.univ.filter (fun i => |θ i| ≤ Θ),
      ‖(Vᴴ *ᵥ Qatlib.Foundations.PureStateMath.Ket (Sum.inr (Sum.inl ()))) i‖ ^ 2) ≤
      (2 * Real.sqrt (6 * Θ * W) + Θ / 2) ^ 2 := by
  obtain ⟨η, he, hn⟩ := reflections_false_root_inverse input f v W hd hW Δ hΔ hk x hx
  obtain ⟨hb1, hb2⟩ := reflections_inverse_phase_mass
    (twoReflectionUnitary input f x Δ) (Qatlib.Foundations.PureStateMath.Ket (Sum.inr (Sum.inl ()))) η V θ
    hV hfull hEV he (normalized_ket _) Θ hΘ
  have hq := mul_le_mul_of_nonneg_left hn (sq_nonneg Θ)
  have hs : 0 ≤ Θ * W := mul_nonneg hΘ (by linarith)
  have hroot := Real.sqrt_nonneg (6 * Θ * W)
  have hsqrt := Real.sq_sqrt (show 0 ≤ 6 * Θ * W by nlinarith)
  have hrhs : 24 * (Θ * W) ≤ (2 * Real.sqrt (6 * Θ * W) + Θ / 2) ^ 2 := by
    nlinarith [mul_nonneg hΘ hroot, sq_nonneg Θ]
  by_cases hsmall : Θ * W ≤ 1
  · have hsq : (Θ * W) ^ 2 ≤ Θ * W := by nlinarith
    nlinarith
  · have hlarge : 1 < Θ * W := by linarith
    linarith

theorem reflections_source_full_cs (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) :
    ∃ Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ,
      IsOrthogonalProjector Δ ∧
      (∀ z, adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z) ∧
      ∀ x, ∃ (a b c d k : ℕ) (t : Fin k → ℝ)
        (V : Matrix (Vertex X f n m) (CSIndex a b c d k) ℂ),
        (∀ i, 0 < t i ∧ t i < 1) ∧ Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V ∧ V * Vᴴ = 1 ∧
        pixProj input f x = V * csCanonicalP a b c d k * Vᴴ ∧
        Δ = V * csCanonicalQ a b c d k t * Vᴴ := by
  obtain ⟨_, hP, _, Δ, hΔ, hk⟩ := twoReflectionConstruction X n m input f v W
  refine ⟨Δ, hΔ, hk, ?_⟩
  intro x
  exact complete_two_projector_cs_normal_form (Vertex X f n m)
    (pixProj input f x) Δ (hP x) hΔ

end Qatlib.Concepts.QueryComplexity.Reflections
