/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TensorDiff

/-!
# Tensor polynomial objectives and gradient matrices

Tensor indices encode products of input coordinates through `amplitude`, with `environment`
omitting one factor. The module differentiates the quadratic tensor objective and constructs
`derivativeMatrix`, whose action on the input equals `gradient` and which is symmetric for
symmetric coefficients. See [GaoEtAl2021] for the paper context.

## Main statements

* `objective_partial`: For symmetric `A`, the coordinate derivative of the objective at `x`
  equals the corresponding coordinate of `gradient A x`.
* `derivativeMatrix_mulVec`: Applying the derivative matrix to `x` gives `gradient A x`.
* `derivativeMatrix_symmetric`: The derivative matrix is symmetric whenever the tensor
  coefficient matrix is symmetric.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Matrix

namespace Qatlib.Papers.QGradient20.Polynomial

/-- The type of length-`p` tuples of indices from `I`, represented as functions on `Fin p`. -/
abbrev TensorIndex (p : ℕ) (I : Type*) := Fin p → I

/-- The product of the coordinates of `x` selected by a tensor index. -/
def amplitude {p : ℕ} {I : Type*} (x : I → ℝ) (u : TensorIndex p I) : ℝ :=
  ∏ k, x (u k)

/-- The tensor amplitude product with the factor at slot `k` omitted. -/
def environment {p : ℕ} {I : Type*} (x : I → ℝ) (k : Fin p) (u : TensorIndex p I) : ℝ :=
  ∏ l ∈ Finset.univ.erase k, x (u l)

/-- A tensor amplitude factors into its coordinate at slot `k` times the environment omitting
that slot. -/
theorem amplitude_factor {p : ℕ} {I : Type*} (x : I → ℝ) (u : TensorIndex p I) (k : Fin p) :
    amplitude x u = x (u k) * environment x k u :=
  (Finset.mul_prod_erase Finset.univ (fun l => x (u l)) (Finset.mem_univ k)).symm

/-- The sum over tensor slots of the direction coordinate times the environment product. -/
def amplitudeDerivative {p : ℕ} {I : Type*} (x y : I → ℝ) (u : TensorIndex p I) : ℝ :=
  ∑ k, environment x k u * y (u k)

/-- Along the line `x + t * y`, the amplitude has derivative `amplitudeDerivative x y` at zero. -/
theorem amplitude_hasDerivAt {p : ℕ} {I : Type*} [Fintype I] (x y : I → ℝ) (u : TensorIndex p I) :
    HasDerivAt (fun t : ℝ => amplitude (fun i => x i + t * y i) u)
      (amplitudeDerivative x y u) 0 := by
  classical
  let e := Fintype.equivFin I
  have h := Qatlib.Foundations.MatrixAlgebra.TensorDiff.tensor_energy_hasDerivAt
    (Pi.single (fun k => e (u k)) (1 : ℝ)) (fun i => x (e.symm i)) (fun i => y (e.symm i))
  simpa only [Qatlib.Foundations.MatrixAlgebra.TensorDiff.tensorEnergy_single,
    Qatlib.Foundations.MatrixAlgebra.TensorDiff.tensorDirectional_single,
    Equiv.symm_apply_apply, one_mul, amplitude, amplitudeDerivative, environment] using h

/-- Half the quadratic form in the tensor amplitudes with coefficient matrix `A`. -/
def objective {p : ℕ} {I : Type*} [Fintype I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (x : I → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ u, ∑ v, A u v * amplitude x u * amplitude x v

/-- The directional derivative expression obtained by differentiating both amplitude factors in
the objective. -/
def objectiveDerivative {p : ℕ} {I : Type*} [Fintype I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (x y : I → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ u, ∑ v, A u v *
    (amplitudeDerivative x y u * amplitude x v + amplitude x u * amplitudeDerivative x y v)

/-- Along the line `x + t * y`, the objective has derivative `objectiveDerivative A x y` at
zero. -/
theorem objective_hasDerivAt {p : ℕ} {I : Type*} [Fintype I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (x y : I → ℝ) :
    HasDerivAt (fun t : ℝ => objective A (fun i => x i + t * y i))
      (objectiveDerivative A x y) 0 := by
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro u _
  apply HasDerivAt.fun_sum
  intro v _
  convert! ((amplitude_hasDerivAt x y u).mul (amplitude_hasDerivAt x y v)).const_mul (A u v) using 1
  · funext t
    simp only [Pi.mul_apply]
    ring
  · (try simp only [zero_mul, add_zero])

/-- The coordinate vector obtained by contracting `A` against the environments in its first
tensor index and the amplitudes in its second. -/
def gradient {p : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (x : I → ℝ) (i : I) : ℝ :=
  ∑ k, ∑ u, ∑ v, A u v * (if u k = i then 1 else 0) * environment x k u * amplitude x v

/-- For symmetric coefficients, the two terms in the directional derivative combine into a
single contraction. -/
theorem objectiveDerivative_symmetric {p : ℕ} {I : Type*} [Fintype I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (hA : A.IsSymm) (x y : I → ℝ) :
    objectiveDerivative A x y = ∑ u, ∑ v, A u v * amplitudeDerivative x y u * amplitude x v := by
  let L := ∑ u, ∑ v, A u v * amplitudeDerivative x y u * amplitude x v
  let R := ∑ u, ∑ v, A u v * amplitude x u * amplitudeDerivative x y v
  have he : R = L := by
    dsimp [R, L]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    have hs : A v u = A u v :=
        congrArg (fun M : Matrix (TensorIndex p I) (TensorIndex p I) ℝ => M u v) hA.eq
    rw [hs]
    ring
  have hsplit : objectiveDerivative A x y = (1 / 2 : ℝ) * (L + R) := by
    dsimp [objectiveDerivative, L, R]
    simp only [mul_add, Finset.sum_add_distrib, mul_assoc]
  rw [hsplit, he]
  dsimp [L]
  ring

/-- For symmetric `A`, the coordinate derivative of the objective at `x` equals the
corresponding coordinate of `gradient A x`. See [GaoEtAl2021]. -/
theorem objective_partial {p : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (hA : A.IsSymm) (x : I → ℝ) (i : I) :
    HasDerivAt (fun t : ℝ => objective A (fun j => x j + t * ((Pi.single i (1 : ℝ) : I → ℝ) j)))
      (gradient A x i) 0 := by
  convert! objective_hasDerivAt A x (Pi.single i 1) using 1
  rw [objectiveDerivative_symmetric A hA]
  simp only [amplitudeDerivative, Finset.mul_sum, Finset.sum_mul]
  rw [gradient, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : u k = i
  · simp [Pi.single_apply, h]
  · simp [h]

/-- The matrix obtained by contracting both tensor indices of `A` with environments, leaving the
coordinates at a common slot free. -/
def derivativeMatrix {p : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (x : I → ℝ) : Matrix I I ℝ :=
  fun i j => ∑ k, ∑ u, ∑ v, A u v * (if u k = i then 1 else 0) * environment x k u *
    environment x k v * (if v k = j then 1 else 0)

/-- Applying the derivative matrix to `x` gives `gradient A x`. See [GaoEtAl2021]. -/
theorem derivativeMatrix_mulVec {p : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (x : I → ℝ) :
    derivativeMatrix A x *ᵥ x = gradient A x := by
  funext i
  simp only [Matrix.mulVec, dotProduct, derivativeMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hu : u k = i
  · simp [hu]
    rw [amplitude_factor x v k]
    ring
  · simp [hu]

/-- The derivative matrix is symmetric whenever the tensor coefficient matrix is symmetric. See
[GaoEtAl2021]. -/
theorem derivativeMatrix_symmetric {p : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (hA : A.IsSymm) (x : I → ℝ) :
    (derivativeMatrix A x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  unfold derivativeMatrix
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  have hs : A v u = A u v :=
      congrArg (fun M : Matrix (TensorIndex p I) (TensorIndex p I) ℝ => M u v) hA.eq
  rw [hs]
  ring

end Qatlib.Papers.QGradient20.Polynomial
