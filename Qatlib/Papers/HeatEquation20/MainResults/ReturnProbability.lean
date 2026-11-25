/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HeatEquation20.MainResults.NormBounds
public import Qatlib.Papers.HeatEquation20.MainResults.ConditionNumber

@[expose] public section


/-!
# HeatEquation20 — the norm/return-probability identity (D3), p. 33

Fixed source: arXiv:2004.06516v2.

Appendix D, step (D3) (p. 33) writes the squared norm of the evolved state as a
matrix element of the random-walk operator:

`‖L^τ |0⟩‖₂² = ⟨0|L^{2τ}|0⟩ = (L^{2τ})_{00}`.

Lemma 14 (p. 17) and Lemma 28 (p. 34) both take this identity as the starting
point before bounding the two sides.  The formal layer of `MainResults` fixes
`heatStep`, the kernel `L_{xy} = (2d)⁻¹ · #{i : y = x ± e_i}`, `l2Sq` and, in
this development, `delta0`, `iterHeat`; the identity itself is proved here:

* `heatStep` is multiplication by the kernel matrix (`heatStep_eq_kernel_mulVec`);
* `l2Sq (iterHeat τ)` is the `(0,0)` entry of the `2τ`-th power of that matrix
  (`l2Sq_iterHeat_eq_matrixPow`).

The two ingredients are the symmetry of the kernel (the shifts are inverse
permutations of the grid) and the elementary `mulVec`/`mul` algebra of matrix
powers.  The `d = 1` identification of the right-hand side with `returnProb` is
not included: it needs the reindexing `Grid 1 n ≃ Fin n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open Qatlib.Papers.HeatEquation20.MainResults

open scoped BigOperators Matrix

/-! ## The shifts as inverse permutations -/

/-- The backward shift undoes the forward shift of the same coordinate. -/
lemma shiftDown_shiftUp_eq_self {d n : ℕ} [NeZero n] (i : Fin d) (x : Grid d n) :
    shiftDown i (shiftUp i x) = x :=
  (shiftEquiv i).left_inv x

/-- The forward shift undoes the backward shift of the same coordinate. -/
lemma shiftUp_shiftDown_eq_self {d n : ℕ} [NeZero n] (i : Fin d) (x : Grid d n) :
    shiftUp i (shiftDown i x) = x :=
  (shiftEquiv i).right_inv x

/-- A grid point is the forward shift of `y` exactly when `y` is the backward
shift of it. -/
lemma eq_shiftUp_iff_eq_shiftDown {d n : ℕ} [NeZero n] (i : Fin d) (x y : Grid d n) :
    x = shiftUp i y ↔ y = shiftDown i x := by
  constructor
  · intro h
    rw [h, shiftDown_shiftUp_eq_self]
  · intro h
    rw [h, shiftUp_shiftDown_eq_self]

/-! ## Symmetry of the random-walk kernel -/

/-- The indicator of the forward shift equals the indicator of the inverse
backward shift. -/
lemma indicator_shiftUp_eq {d n : ℕ} [NeZero n] (i : Fin d) (x y : Grid d n) :
    (if x = shiftUp i y then (1 : ℝ) else 0) = (if y = shiftDown i x then 1 else 0) := by
  by_cases h : x = shiftUp i y
  · rw [ite_eq_left h, ite_eq_left ((eq_shiftUp_iff_eq_shiftDown i x y).mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h ((eq_shiftUp_iff_eq_shiftDown i x y).mpr hh))]

/-- The random-walk kernel is symmetric, `L_{xy} = L_{yx}`: moving from `y` to
`x` is moving from `x` to `y` backwards. -/
lemma heatStepKernel_comm {d n : ℕ} [NeZero n] (x y : Grid d n) :
    heatStepKernel x y = heatStepKernel y x := by
  unfold heatStepKernel
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [indicator_shiftUp_eq i x y, indicator_shiftUp_eq i y x]
  ring

/-- The matrix of the random-walk kernel is symmetric. -/
lemma kernelMatrix_transpose {d n : ℕ} [NeZero n] :
    (Matrix.of (heatStepKernel (d := d) (n := n)))ᵀ
      = Matrix.of (heatStepKernel (d := d) (n := n)) := by
  ext x y
  exact heatStepKernel_comm y x

/-- Every power of the symmetric kernel matrix is symmetric. -/
lemma kernelMatrix_pow_comm {d n : ℕ} [NeZero n] (τ : ℕ) (x y : Grid d n) :
    (Matrix.of (heatStepKernel (d := d) (n := n)) ^ τ) x y
      = (Matrix.of (heatStepKernel (d := d) (n := n)) ^ τ) y x := by
  have h : (Matrix.of (heatStepKernel (d := d) (n := n)) ^ τ)ᵀ
      = Matrix.of (heatStepKernel (d := d) (n := n)) ^ τ := by
    rw [Matrix.transpose_pow, kernelMatrix_transpose]
  have hxy := congrFun (congrFun h x) y
  simpa using hxy.symm

/-! ## The random-walk step as a matrix-vector product -/

/-- A single shift picks out one entry of the vector: the inverse shift of `x`. -/
lemma sum_indicator_shiftUp {d n : ℕ} [NeZero n] (i : Fin d) (x : Grid d n)
    (u : Grid d n → ℝ) :
    ∑ y : Grid d n, (if x = shiftUp i y then (1 : ℝ) else 0) * u y
      = u (shiftDown i x) := by
  refine (Finset.sum_eq_single (shiftDown i x) ?_ ?_).trans ?_
  · intro b _ hb
    have h : ¬ (x = shiftUp i b) := fun h => hb ((eq_shiftUp_iff_eq_shiftDown i x b).mp h)
    rw [ite_eq_right h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_left (shiftUp_shiftDown_eq_self i x).symm, one_mul]

/-- The backward shift picks out the forward-shifted entry of the vector. -/
lemma sum_indicator_shiftDown {d n : ℕ} [NeZero n] (i : Fin d) (x : Grid d n)
    (u : Grid d n → ℝ) :
    ∑ y : Grid d n, (if x = shiftDown i y then (1 : ℝ) else 0) * u y
      = u (shiftUp i x) := by
  refine (Finset.sum_eq_single (shiftUp i x) ?_ ?_).trans ?_
  · intro b _ hb
    have h : ¬ (x = shiftDown i b) :=
      fun h => hb ((eq_shiftUp_iff_eq_shiftDown i b x).mpr h)
    rw [ite_eq_right h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_left (shiftDown_shiftUp_eq_self i x).symm, one_mul]

/-- **The matrix form of (13)** (arXiv:2004.06516v2, p. 6 and Appendix D): the
random-walk step is multiplication by the kernel matrix,
`(L u)(x) = Σ_y L_{xy} u(y)`. -/
lemma heatStep_eq_kernel_mulVec {d n : ℕ} [NeZero n] (u : Grid d n → ℝ) :
    heatStep u = Matrix.of (heatStepKernel (d := d) (n := n)) *ᵥ u := by
  funext x
  rw [Matrix.mulVec_apply_eq_sum]
  calc heatStep u x
      = (2 * (d : ℝ))⁻¹ * ∑ i : Fin d, (u (shiftUp i x) + u (shiftDown i x)) := rfl
    _ = (2 * (d : ℝ))⁻¹ * ∑ i : Fin d,
          ((∑ y : Grid d n, (if x = shiftUp i y then (1 : ℝ) else 0) * u y)
            + (∑ y : Grid d n, (if x = shiftDown i y then (1 : ℝ) else 0) * u y)) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_indicator_shiftUp, sum_indicator_shiftDown]
        ring
    _ = (2 * (d : ℝ))⁻¹ * ∑ i : Fin d, ∑ y : Grid d n,
          ((if x = shiftUp i y then (1 : ℝ) else 0)
            + (if x = shiftDown i y then (1 : ℝ) else 0)) * u y := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ y : Grid d n, (2 * (d : ℝ))⁻¹ * (∑ i : Fin d,
          ((if x = shiftUp i y then (1 : ℝ) else 0)
            + (if x = shiftDown i y then (1 : ℝ) else 0))) * u y := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ y : Grid d n, heatStepKernel x y * u y := rfl

/-- Reading a matrix-vector product at the origin: `(M δ₀)(x) = M_{x0}`. -/
lemma mulVec_delta0 {d n : ℕ} [NeZero n] (M : Matrix (Grid d n) (Grid d n) ℝ) :
    M *ᵥ delta0 (d := d) (n := n) = fun x => M x 0 := by
  funext x
  rw [Matrix.mulVec_apply_eq_sum]
  refine (Finset.sum_eq_single (0 : Grid d n) ?_ ?_).trans ?_
  · intro b _ hb
    have hb' : delta0 (d := d) (n := n) b = 0 := by simp [delta0, hb]
    rw [hb', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · rw [delta0]
    simp

/-- The `τ`-fold random-walk iterate is the `τ`-th power of the kernel matrix
applied to the origin state. -/
lemma iterHeat_eq_pow_mulVec {d n : ℕ} [NeZero n] (τ : ℕ) :
    iterHeat (d := d) (n := n) τ
      = (Matrix.of (heatStepKernel (d := d) (n := n)) ^ τ) *ᵥ delta0 (d := d) (n := n) := by
  induction τ with
  | zero => simp [iterHeat]
  | succ k ih =>
      have hsucc : iterHeat (d := d) (n := n) (k + 1)
          = heatStep (iterHeat (d := d) (n := n) k) := by
        show (heatStep (d := d) (n := n))^[k + 1] (delta0 (d := d) (n := n))
          = heatStep ((heatStep (d := d) (n := n))^[k] (delta0 (d := d) (n := n)))
        rw [Function.iterate_succ_apply']
      rw [hsucc, ih, heatStep_eq_kernel_mulVec, Matrix.mulVec_mulVec, ← pow_succ']

/-- **Appendix D, (D3)** (arXiv:2004.06516v2, p. 33; used by Lemma 14, p. 17
and Lemma 28, p. 34).  The random-walk step acts by the kernel matrix, and the
squared `ℓ₂` norm of `L^τ |0⟩` is the `(0,0)` entry of the `2τ`-th power of that
matrix, i.e. the return probability `⟨0|L^{2τ}|0⟩`. -/
theorem l2Sq_iterHeat_eq_matrixPow {d n : ℕ} [NeZero n] (τ : ℕ) :
    (∀ u : Grid d n → ℝ, heatStep u = fun x => ∑ y, heatStepKernel x y * u y)
      ∧ l2Sq (iterHeat (d := d) (n := n) τ)
        = (Matrix.of (heatStepKernel (d := d) (n := n)) ^ (2 * τ)) 0 0 := by
  refine ⟨fun u => ?_, ?_⟩
  · rw [heatStep_eq_kernel_mulVec]
    funext x
    simp only [Matrix.mulVec_apply_eq_sum, Matrix.of_apply]
  · rw [iterHeat_eq_pow_mulVec, mulVec_delta0]
    rw [show 2 * τ = τ + τ from by ring, pow_add]
    rw [Matrix.mul_apply]
    simp only [l2Sq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_two, kernelMatrix_pow_comm τ 0 k]

end Qatlib.Papers.HeatEquation20.MainResults
