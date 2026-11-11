/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
import Qatlib.Concepts.QueryComplexity.Amplification.PiTensorState
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Tensor phase witnesses and operator error lower bounds

This module turns normalized eigenvectors with conjugate phases into lower bounds on the
operator-norm distance of tensor powers from identity. It uses tensor eigenvectors and the
eigenvalue norm principle from finite-dimensional matrix analysis [Bhatia1997].

A phase-grid argument gives a lower bound that grows linearly with the tensor count until it
reaches one, for phases in `[0, 1/8]`. Relative-product identities transfer this bound to the
distance between two tensor powers when the reference factor is unitary.

## Main statements

* `paired_phase_tensor_witness`: a sine lower bound for every choice of phase signs.
* `phase_grid_saturation`: a phase-grid witness for the capped linear lower bound.
* `paired_relative_tensor_saturation`: the corresponding relative tensor error bound.
* `principal_phase_small_of_chord`: small chord length implies phase at most `1/8`.

## References

* [Bhatia, 1997][Bhatia1997]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
noncomputable section

namespace Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound

open Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- A register tensor product acts on a product state by applying each local matrix to the
corresponding local vector. -/
theorem productMatrix_mulVec_piTensorState
    {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (A : ι → Matrix I I ℂ) (v : ι → Qatlib.Foundations.PureStateMath.QState I) :
    Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix A *ᵥ Qatlib.Concepts.QueryComplexity.Amplification.PiTensorState v =
      Qatlib.Concepts.QueryComplexity.Amplification.PiTensorState (fun i => A i *ᵥ v i) := by
  funext x
  change (∑ y : ι → I, (∏ i, A i (x i) (y i)) * (∏ i, v i (y i))) =
    ∏ i, ∑ j, A i (x i) j * v i j
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => A i (x i) j * v i j)).symm

/-- A tensor product of local eigenvectors is an eigenvector of the product matrix with
eigenvalue equal to the product of the local eigenvalues. -/
theorem productMatrix_mulVec_eigen
    {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (A : ι → Matrix I I ℂ) (v : ι → Qatlib.Foundations.PureStateMath.QState I) (z : ι → ℂ)
    (hv : ∀ i, A i *ᵥ v i = z i • v i) :
    Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix A *ᵥ Qatlib.Concepts.QueryComplexity.Amplification.PiTensorState v =
      (∏ i, z i) • Qatlib.Concepts.QueryComplexity.Amplification.PiTensorState v := by
  rw [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.productMatrix_mulVec_piTensorState]
  simp_rw [hv]
  funext x
  simp [Qatlib.Concepts.QueryComplexity.Amplification.PiTensorState, Finset.prod_mul_distrib,
      smul_eq_mul]

/-- If `v` is a normalized eigenvector of `A` with eigenvalue `z`, then `‖z - 1‖ ≤ ‖A - 1‖`. -/
theorem eigenvalue_sub_one_le_norm
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (v : Qatlib.Foundations.PureStateMath.QState I) (z : ℂ)
    (hv : Qatlib.Foundations.PureStateMath.Normalized v) (hAv : A *ᵥ v = z • v) :
    ‖z - 1‖ ≤ ‖A - 1‖ := by
  have hn :=
      (Qatlib.Foundations.PureStateMath.BornBridge.normalized_iff_norm_toEuclidean_fromVec v).mp hv
  have ha : (A - 1) *ᵥ v = (z - 1) • v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hAv, sub_smul, one_smul]
  have hb := Qatlib.Concepts.ReferenceError.RefTraceError.l2_norm_mulVec_fromVec_le (A - 1) v
  rw [ha, hn, mul_one] at hb
  change ‖(z - 1) • Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec v‖ ≤ ‖A - 1‖ at hb
  simpa only [norm_smul, hn, mul_one] using hb

/-- For normalized local eigenvectors, the distance of the product eigenvalue from one is at
most the operator-norm distance of the product matrix from identity. -/
theorem product_eigenvalue_sub_one_le_norm
    {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (A : ι → Matrix I I ℂ) (v : ι → Qatlib.Foundations.PureStateMath.QState I) (z : ι → ℂ)
    (hv : ∀ i, Qatlib.Foundations.PureStateMath.Normalized (v i)) (hAv : ∀ i, A i *ᵥ v i = z i • v i) :
    ‖(∏ i, z i) - 1‖ ≤ ‖Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix A - 1‖ :=
  Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.eigenvalue_sub_one_le_norm _ _ _ (Qatlib.Concepts.QueryComplexity.Amplification.normalized_piTensorState hv)
    (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.productMatrix_mulVec_eigen A v z hAv)

/-- Normalized eigenvectors of `A` with phases `±θ` give the lower bound `2 * |sin ((n - k) * θ
/ 2)|` for the distance of its `(n + k)`-fold tensor product from identity. -/
theorem paired_phase_tensor_witness_add
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (vplus vminus : Qatlib.Foundations.PureStateMath.QState I) (θ : ℝ)
    (hp : Qatlib.Foundations.PureStateMath.Normalized vplus) (hm : Qatlib.Foundations.PureStateMath.Normalized vminus)
    (hAp : A *ᵥ vplus = Complex.exp (Complex.I * θ) • vplus)
    (hAm : A *ᵥ vminus = Complex.exp (Complex.I * (-θ)) • vminus)
    (n k : ℕ) :
    2 * |Real.sin (((n : ℝ) - (k : ℝ)) * θ / 2)| ≤
      ‖Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun _ : Fin (n + k) => A) - 1‖ := by
  let v : Fin (n + k) → Qatlib.Foundations.PureStateMath.QState I :=
    Fin.addCases (fun _ => vplus) (fun _ => vminus)
  let z : Fin (n + k) → ℂ :=
    Fin.addCases (fun _ => Complex.exp (Complex.I * θ))
      (fun _ => Complex.exp (Complex.I * (-θ)))
  have hv : ∀ i, Qatlib.Foundations.PureStateMath.Normalized (v i) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [v] using hp
    · intro j
      simpa [v] using hm
  have hAv : ∀ i, A *ᵥ v i = z i • v i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [v, z] using hAp
    · intro j
      simpa [v, z] using hAm
  have hz : (∏ i, z i) =
      Complex.exp (Complex.I * Complex.ofReal (((n : ℝ) - (k : ℝ)) * θ)) := by
    simp only [z, Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h := Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.product_eigenvalue_sub_one_le_norm
    (fun _ : Fin (n + k) => A) v z hv hAv
  rw [hz, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul] at h
  norm_num at h
  exact h

/-- Normalized eigenvectors with phases `±θ` give the lower bound `2 * |sin ((N - 2k) * θ / 2)|`
for the `N`-fold tensor product error whenever `k ≤ N`. -/
theorem paired_phase_tensor_witness
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (vplus vminus : Qatlib.Foundations.PureStateMath.QState I) (θ : ℝ)
    (hp : Qatlib.Foundations.PureStateMath.Normalized vplus) (hm : Qatlib.Foundations.PureStateMath.Normalized vminus)
    (hAp : A *ᵥ vplus = Complex.exp (Complex.I * θ) • vplus)
    (hAm : A *ᵥ vminus = Complex.exp (Complex.I * (-θ)) • vminus)
    (N k : ℕ) (hk : k ≤ N) :
    2 * |Real.sin (((N : ℝ) - 2 * (k : ℝ)) * θ / 2)| ≤
      ‖Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun _ : Fin N => A) - 1‖ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + k := ⟨N - k, (Nat.sub_add_cancel hk).symm⟩
  have hcast : ((n + k : ℕ) : ℝ) - 2 * (k : ℝ) = (n : ℝ) - (k : ℝ) := by
    push_cast
    ring
  rw [hcast]
  exact Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.paired_phase_tensor_witness_add A vplus vminus θ hp hm hAp hAm n k

/-- The register tensor product of unitary local matrices is unitary. -/
theorem productMatrix_unitary
    {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (U : ι → Matrix I I ℂ) (hU : ∀ i, U i ∈ Matrix.unitaryGroup I ℂ) :
    Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix U ∈ Matrix.unitaryGroup (ι → I) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose,
      Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_adjoint, Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_mul]
  have h : (fun i => U i * (U i)ᴴ) = fun _ : ι => (1 : Matrix I I ℂ) := by
    funext i
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp (hU i))
  rw [h, Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_one]

/-- For unitary reference factors `U`, the distance between the tensor products of `W` and `U`
equals the distance from identity of the tensor product of `(U i)ᴴ * W i`. -/
theorem productMatrix_relative_error
    {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (U W : ι → Matrix I I ℂ) (hU : ∀ i, U i ∈ Matrix.unitaryGroup I ℂ) :
    ‖Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix W - Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix U‖ =
      ‖Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun i => (U i)ᴴ * W i) - 1‖ := by
  have hu :=
      Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.productMatrix_unitary U hU
  have hh : (Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix U)ᴴ * Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hu)
  have hn := CStarRing.norm_mem_unitary_mul
    (Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix W - Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix U) (Unitary.star_mem hu)
  change ‖(Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix U)ᴴ * (Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix W - Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix U)‖ =
    ‖Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix W - Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix U‖ at hn
  rw [Matrix.mul_sub, hh, Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_adjoint,
      Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_mul] at hn
  exact hn.symm

/-- If `θ > 0` and `N * θ > π`, some grid point `(N - 2k) * θ` with `k ≤ N` lies in `(π - 2θ,
π]`. -/
theorem phase_grid_below_pi (N : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hlarge : Real.pi < (N : ℝ) * θ) :
    ∃ k : ℕ, k ≤ N ∧
      Real.pi - 2 * θ < ((N : ℝ) - 2 * (k : ℝ)) * θ ∧
      ((N : ℝ) - 2 * (k : ℝ)) * θ ≤ Real.pi := by
  let a : ℝ := ((N : ℝ) - Real.pi / θ) / 2
  let k : ℕ := ⌈a⌉₊
  have hquot : Real.pi / θ < (N : ℝ) :=
    (div_lt_iff₀ hθ).2 hlarge
  have ha : 0 ≤ a := by
    dsimp [a]
    linarith
  have hklo : a ≤ (k : ℝ) := by
    dsimp [k]
    exact Nat.le_ceil a
  have hkhi : (k : ℝ) < a + 1 := by
    dsimp [k]
    exact Nat.ceil_lt_add_one ha
  have hkN : k ≤ N := by
    dsimp [k]
    apply Nat.ceil_le.mpr
    dsimp [a]
    have hp : 0 ≤ Real.pi / θ := le_of_lt (div_pos Real.pi_pos hθ)
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith
  have hdiv : (Real.pi / θ) * θ = Real.pi :=
    div_mul_cancel₀ _ (ne_of_gt hθ)
  have hkloθ := mul_le_mul_of_nonneg_right hklo (le_of_lt hθ)
  have hkhiθ := mul_lt_mul_of_pos_right hkhi hθ
  refine ⟨k, hkN, ?_, ?_⟩
  · dsimp [a] at hkhiθ
    nlinarith [hdiv]
  · dsimp [a] at hkloθ
    nlinarith [hdiv]

/-- For positive `N` and `θ ∈ [0, 1/8]`, some phase-grid sine witness is at least `min (2 * N *
(2 * sin (θ/2)) / π) 1`. -/
theorem phase_grid_saturation (N : ℕ) (hN : 0 < N)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 8) :
    ∃ k : ℕ, k ≤ N ∧
      min (2 * (N : ℝ) * (2 * Real.sin (θ / 2)) / Real.pi) 1 ≤
        2 * |Real.sin (((N : ℝ) - 2 * (k : ℝ)) * θ / 2)| := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hδ : 2 * Real.sin (θ / 2) ≤ θ := by
    have hs := Real.sin_le (show 0 ≤ θ / 2 by positivity)
    linarith
  by_cases hsmall : (N : ℝ) * θ ≤ Real.pi
  · refine ⟨0, Nat.zero_le N, ?_⟩
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    have hhalf0 : 0 ≤ (N : ℝ) * θ / 2 :=
      div_nonneg (mul_nonneg hNR.le hθ0) (by norm_num)
    have hhalfπ : (N : ℝ) * θ / 2 ≤ Real.pi / 2 := by linarith
    have hs := Real.mul_le_sin hhalf0 hhalfπ
    have hcoef : 0 ≤ (2 / Real.pi) * (N : ℝ) :=
      mul_nonneg (by positivity) hNR.le
    calc
      min (2 * (N : ℝ) * (2 * Real.sin (θ / 2)) / Real.pi) 1
          ≤ 2 * (N : ℝ) * (2 * Real.sin (θ / 2)) / Real.pi := min_le_left _ _
      _ = (2 / Real.pi) * (N : ℝ) * (2 * Real.sin (θ / 2)) := by ring
      _ ≤ (2 / Real.pi) * (N : ℝ) * θ :=
        mul_le_mul_of_nonneg_left hδ hcoef
      _ = 2 * ((2 / Real.pi) * ((N : ℝ) * θ / 2)) := by ring
      _ ≤ 2 * Real.sin ((N : ℝ) * θ / 2) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ ≤ 2 * |Real.sin ((N : ℝ) * θ / 2)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
  · have hlarge : Real.pi < (N : ℝ) * θ := lt_of_not_ge hsmall
    have hθpos : 0 < θ := by
      by_contra hn
      have hz : θ = 0 := le_antisymm (le_of_not_gt hn) hθ0
      rw [hz, mul_zero] at hlarge
      linarith [Real.pi_pos]
    obtain ⟨k, hkN, hlo, hhi⟩ :=
        Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.phase_grid_below_pi N θ hθpos hlarge
    refine ⟨k, hkN, ?_⟩
    let x : ℝ := ((N : ℝ) - 2 * (k : ℝ)) * θ
    have hxlo : Real.pi / 2 ≤ x := by
      dsimp [x]
      linarith [Real.pi_gt_three]
    have hxhi : x ≤ Real.pi := hhi
    have hhalf0 : 0 ≤ x / 2 := by linarith [Real.pi_pos]
    have hhalfπ : x / 2 ≤ Real.pi / 2 := by linarith
    have hs := Real.mul_le_sin hhalf0 hhalfπ
    have hquot : (1 : ℝ) ≤ (2 / Real.pi) * x := by
      calc
        (1 : ℝ) ≤ (2 * x) / Real.pi :=
          (le_div_iff₀ Real.pi_pos).2 (by linarith)
        _ = (2 / Real.pi) * x := by ring
    change min (2 * (N : ℝ) * (2 * Real.sin (θ / 2)) / Real.pi) 1 ≤
      2 * |Real.sin (x / 2)|
    calc
      min (2 * (N : ℝ) * (2 * Real.sin (θ / 2)) / Real.pi) 1
          ≤ 1 := min_le_right _ _
      _ ≤ (2 / Real.pi) * x := hquot
      _ = 2 * ((2 / Real.pi) * (x / 2)) := by ring
      _ ≤ 2 * Real.sin (x / 2) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ ≤ 2 * |Real.sin (x / 2)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)

/-- For normalized eigenvectors with phases `±θ`, positive `N`, and `θ ∈ [0, 1/8]`, the `N`-fold
tensor error is at least `min (2 * N * (2 * sin (θ/2)) / π) 1`. -/
theorem paired_phase_tensor_saturation
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (vplus vminus : Qatlib.Foundations.PureStateMath.QState I) (θ : ℝ)
    (hp : Qatlib.Foundations.PureStateMath.Normalized vplus) (hm : Qatlib.Foundations.PureStateMath.Normalized vminus)
    (hAp : A *ᵥ vplus = Complex.exp (Complex.I * θ) • vplus)
    (hAm : A *ᵥ vminus = Complex.exp (Complex.I * (-θ)) • vminus)
    (N : ℕ) (hN : 0 < N) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1/8) :
    min (2 * (N : ℝ) * (2 * Real.sin (θ/2)) / Real.pi) 1 ≤
      ‖Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun _ : Fin N => A) - 1‖ := by
  obtain ⟨k, hk, hb⟩ :=
      Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.phase_grid_saturation N hN θ hθ0 hθ
  exact hb.trans
      (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.paired_phase_tensor_witness A vplus vminus θ hp hm hAp hAm N k hk)

/-- If `U` is unitary and `Uᴴ * W` has normalized eigenvectors with phases `±θ ∈ ±[0, 1/8]`, the
distance between their positive tensor powers is at least `min (2 * N * (2 * sin (θ/2)) / π)
1`. -/
theorem paired_relative_tensor_saturation
    {I : Type*} [Fintype I] [DecidableEq I]
    (U W : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (vplus vminus : Qatlib.Foundations.PureStateMath.QState I) (θ : ℝ)
    (hp : Qatlib.Foundations.PureStateMath.Normalized vplus) (hm : Qatlib.Foundations.PureStateMath.Normalized vminus)
    (hAp : (Uᴴ * W) *ᵥ vplus = Complex.exp (Complex.I * θ) • vplus)
    (hAm : (Uᴴ * W) *ᵥ vminus = Complex.exp (Complex.I * (-θ)) • vminus)
    (N : ℕ) (hN : 0 < N) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1/8) :
    min (2 * (N : ℝ) * (2 * Real.sin (θ/2)) / Real.pi) 1 ≤
      ‖Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun _ : Fin N => W) - Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun _ : Fin N => U)‖ := by
  rw [Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.productMatrix_relative_error (fun _ : Fin N => U) (fun _ => W) (fun _ => hU)]
  exact Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.paired_phase_tensor_saturation (Uᴴ * W) vplus vminus θ hp hm hAp hAm N hN hθ0 hθ

/-- Under the paired relative-phase hypotheses with `θ ∈ [0, 1/8]` and positive `N`, any lower
bound `d ≤ 2 * sin (θ/2)` gives tensor error at least `min (2 * N * d / π) 1`. -/
theorem paired_relative_tensor_saturation_of_lower
    {I : Type*} [Fintype I] [DecidableEq I]
    (U W : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (vplus vminus : Qatlib.Foundations.PureStateMath.QState I) (θ d : ℝ)
    (hp : Qatlib.Foundations.PureStateMath.Normalized vplus) (hm : Qatlib.Foundations.PureStateMath.Normalized vminus)
    (hAp : (Uᴴ * W) *ᵥ vplus = Complex.exp (Complex.I * θ) • vplus)
    (hAm : (Uᴴ * W) *ᵥ vminus = Complex.exp (Complex.I * (-θ)) • vminus)
    (N : ℕ) (hN : 0 < N) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1/8)
    (hd : d ≤ 2 * Real.sin (θ/2)) :
    min (2 * (N : ℝ) * d / Real.pi) 1 ≤
      ‖Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun _ : Fin N => W) - Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix (fun _ : Fin N => U)‖ := by
  have hl : 2 * (N : ℝ) * d / Real.pi ≤
      2 * (N : ℝ) * (2 * Real.sin (θ/2)) / Real.pi :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd (by positivity)) Real.pi_pos.le
  exact (min_le_min hl le_rfl).trans
    (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.paired_relative_tensor_saturation U W hU vplus vminus θ hp hm hAp hAm N hN hθ0 hθ)

/-- For `θ ∈ [0, π]`, the phase is at most twice its chord length `2 * sin (θ / 2)`. -/
theorem principal_phase_le_twice_chord (θ : ℝ)
    (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    θ ≤ 2*(2*Real.sin (θ/2)) := by
  have hh0 : 0 ≤ θ/2 := by positivity
  have hhπ : θ/2 ≤ Real.pi/2 := by linarith
  have hs := Real.mul_le_sin hh0 hhπ
  have hmul := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
  have hcancel : Real.pi*((2/Real.pi)*(θ/2)) = θ := by
    field_simp
  rw [hcancel] at hmul
  have hsin : 0 ≤ Real.sin (θ/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hh0 (by linarith [Real.pi_pos])
  calc
    θ ≤ Real.pi*Real.sin (θ/2) := hmul
    _ ≤ 4*Real.sin (θ/2) :=
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le hsin
    _ = _ := by ring

/-- For a principal phase `θ ∈ [0, π]`, chord length at most `1/16` implies `θ ≤ 1/8`. -/
theorem principal_phase_small_of_chord (θ : ℝ)
    (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (hc : 2*Real.sin (θ/2) ≤ 1/16) : θ ≤ 1/8 := by
  have h :=
      Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound.principal_phase_le_twice_chord θ h0 hπ
  linarith

end Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.TensorPhaseLowerBound
