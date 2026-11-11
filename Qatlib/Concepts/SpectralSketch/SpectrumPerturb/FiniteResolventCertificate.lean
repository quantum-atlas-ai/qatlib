/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ApproximationAlgorithmsDefs

/-!
# Finite certificates for resolvent quadrature

This module turns a residual bound below one into an inverse error bound and applies it to
matrix resolvents. It provides exact rational complex data, a Boolean certificate checker, and
arithmetic programs for finite resolvent quadrature, using standard spectral and matrix analysis
as background [Bhatia1997].

`Certified` records the nodewise hypotheses used by `quadratureError`, while the program cost
functions record the chosen arithmetic cost model.

## Main statements

* `inverse_error_of_residual`: certifies invertibility and bounds inverse error from a residual.
* `FiniteResolventNode.resolvent_error_of_check`: proves the soundness of the finite checker.
* `nonnormal_quadrature_error` and `normal_quadrature_error`: combine representation error with
  certified node errors.
* `programCost_eq`: separates inverse program costs from scalar evaluation and matrix
  combination costs.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator Ring

/-- The inverse of `1 - E` differs from one by at most `‖E‖ / (1 - ‖E‖)` whenever `‖E‖ < 1`. -/
theorem norm_inverse_one_sub_sub_one_le {R : Type*} [NormedRing R]
    [HasSummableGeomSeries R] (E : R) (hE : ‖E‖ < 1) :
    ‖(1 - E)⁻¹ʳ - 1‖ ≤ ‖E‖ / (1 - ‖E‖) := by
  have hs : Summable (fun n : ℕ => E ^ n) := summable_geometric_of_norm_lt_one hE
  have htail : ‖∑' n : ℕ, E ^ (n + 1)‖ ≤ (1 - ‖E‖)⁻¹ - 1 := by
    refine tsum_of_norm_bounded ?_ fun n => norm_pow_le' E (Nat.succ_pos n)
    convert! (hasSum_nat_add_iff' 1).mpr
      (hasSum_geometric_of_lt_one (norm_nonneg E) hE) using 1; simp
  rw [← geom_series_eq_inverse E hE, hs.tsum_eq_zero_add]
  simp only [pow_zero, add_sub_cancel_left]
  calc
    ‖∑' n : ℕ, E ^ (n + 1)‖ ≤ (1 - ‖E‖)⁻¹ - 1 := htail
    _ = ‖E‖ / (1 - ‖E‖) := by
      have hden : 1 - ‖E‖ ≠ 0 := ne_of_gt (sub_pos.mpr hE)
      field_simp [hden]
      ring

/-- If `B` is a unit and `‖1 - M * B‖ ≤ q < 1`, then `M` is a unit and `‖M⁻¹ʳ - B‖ ≤ ‖B‖ * q /
(1 - q)`. -/
theorem inverse_error_of_residual {R : Type*} [NormedRing R]
    [HasSummableGeomSeries R] (M B : R) (q : ℝ) (hB : IsUnit B)
    (hq : q < 1) (hres : ‖1 - M * B‖ ≤ q) :
    IsUnit M ∧ ‖M⁻¹ʳ - B‖ ≤ ‖B‖ * q / (1 - q) := by
  let E : R := 1 - M * B
  have hE : ‖E‖ < 1 := lt_of_le_of_lt hres hq
  let v : Rˣ := Units.oneSub E hE
  let u : Rˣ := hB.unit
  have hu : (u : R) = B := hB.unit_spec
  have hv : (v : R) = 1 - E := rfl
  have hMB : M * B = 1 - E := by simp [E]
  have hMval : M = (v : R) * (↑u⁻¹ : R) := by
    calc
      M = M * 1 := (mul_one M).symm
      _ = M * (B * (↑u⁻¹ : R)) := by rw [← hu, Units.mul_inv]
      _ = (M * B) * (↑u⁻¹ : R) := by rw [mul_assoc]
      _ = (v : R) * (↑u⁻¹ : R) := by rw [hMB, hv]
  have hM : IsUnit M := hMval ▸ v.isUnit.mul u⁻¹.isUnit
  have hX : IsUnit (1 - E) := v.isUnit
  have hMinv : M⁻¹ʳ = B * (1 - E)⁻¹ʳ := by
    have hright : M * (B * (1 - E)⁻¹ʳ) = 1 := by
      rw [← mul_assoc, hMB, Ring.mul_inverse_cancel _ hX]
    calc
      M⁻¹ʳ = M⁻¹ʳ * 1 := (mul_one _).symm
      _ = M⁻¹ʳ * (M * (B * (1 - E)⁻¹ʳ)) := by rw [hright]
      _ = (M⁻¹ʳ * M) * (B * (1 - E)⁻¹ʳ) := by rw [mul_assoc]
      _ = B * (1 - E)⁻¹ʳ := by rw [Ring.inverse_mul_cancel _ hM, one_mul]
  have hfrac : ‖E‖ / (1 - ‖E‖) ≤ q / (1 - q) := by
    have hEq : ‖E‖ ≤ q := hres
    apply (div_le_div_iff₀ (sub_pos.mpr hE) (sub_pos.mpr hq)).mpr
    nlinarith
  refine ⟨hM, ?_⟩
  calc
    ‖M⁻¹ʳ - B‖ = ‖B * ((1 - E)⁻¹ʳ - 1)‖ := by
      rw [hMinv, mul_sub, mul_one]
    _ ≤ ‖B‖ * ‖(1 - E)⁻¹ʳ - 1‖ := norm_mul_le _ _
    _ ≤ ‖B‖ * (‖E‖ / (1 - ‖E‖)) :=
      mul_le_mul_of_nonneg_left (norm_inverse_one_sub_sub_one_le E hE) (norm_nonneg B)
    _ ≤ ‖B‖ * (q / (1 - q)) := mul_le_mul_of_nonneg_left hfrac (norm_nonneg B)
    _ = ‖B‖ * q / (1 - q) := by ring

/-- A unit matrix `B` with resolvent residual at most `q < 1` certifies that `z • 1 - A` is
invertible and bounds the resolvent error by `‖B‖ * q / (1 - q)`. -/
theorem resolvent_error_of_certificate {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (q : ℝ) (hB : IsUnit B) (hq : q < 1)
    (hres : ‖(1 : Matrix (Fin n) (Fin n) ℂ) -
      (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A) * B‖ ≤ q) :
    IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A) ∧
      ‖resolvent A z - B‖ ≤ ‖B‖ * q / (1 - q) := by
  simpa only [resolvent, Algebra.algebraMap_eq_smul_one] using
    inverse_error_of_residual (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A) B q hB hq hres

/-- The entrywise embedding of a rational matrix into complex matrices. -/
def rationalMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => (A i j : ℂ)

/-- A residual certificate for a rational matrix embedded in the complex matrices establishes
invertibility of `z • 1 - rationalMatrix A` and the corresponding resolvent error bound. -/
theorem rational_resolvent_error_of_certificate {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (q : ℝ) (hB : IsUnit B) (hq : q < 1)
    (hres : ‖(1 : Matrix (Fin n) (Fin n) ℂ) -
      (z • (1 : Matrix (Fin n) (Fin n) ℂ) - rationalMatrix A) * B‖ ≤ q) :
    IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - rationalMatrix A) ∧
      ‖resolvent (rationalMatrix A) z - B‖ ≤ ‖B‖ * q / (1 - q) :=
  resolvent_error_of_certificate (rationalMatrix A) B z q hB hq hres

/-- The Euclidean norm of a finite complex vector is at most the sum of its coordinate norms. -/
theorem euclidean_norm_le_entry_sum {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  rw [EuclideanSpace.norm_eq]
  exact (Real.sqrt_le_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
    (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _)

/-- Each coordinate norm of a finite complex vector is at most its Euclidean norm. -/
theorem euclidean_norm_apply_le {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    ‖x i‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  exact Real.le_sqrt_of_sq_le
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖x j‖) (Finset.mem_univ i))

/-- The operator norm of a finite complex square matrix is at most the sum of the norms of all
its entries. -/
theorem operator_norm_le_entry_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) fun x => ?_
  change ‖WithLp.toLp 2 (A *ᵥ (x : Fin n → ℂ))‖ ≤ _
  calc
    ‖WithLp.toLp 2 (A *ᵥ (x : Fin n → ℂ))‖ ≤ ∑ i, ‖(A *ᵥ (x : Fin n → ℂ)) i‖ :=
      euclidean_norm_le_entry_sum _
    _ = ∑ i, ‖∑ j, A i j * x j‖ := by simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ i, ∑ j, ‖A i j * x j‖ := by
      exact Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ = ∑ i, ∑ j, ‖A i j‖ * ‖x j‖ := by simp
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖x‖ := by
      exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (euclidean_norm_apply_le x j) (norm_nonneg _)
    _ = (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
      simp [Finset.sum_mul]

/-- The norm of a complex number is at most the sum of the absolute values of its real and
imaginary parts. -/
theorem complex_norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  rw [Complex.norm_def, Complex.normSq_apply]
  apply (Real.sqrt_le_left (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
  nlinarith [sq_abs z.re, sq_abs z.im, abs_nonneg z.re, abs_nonneg z.im,
    mul_nonneg (abs_nonneg z.re) (abs_nonneg z.im)]

/-- The quadratic algebra `QuadraticAlgebra ℚ (-1) 0`, representing complex numbers with
rational real and imaginary parts. -/
abbrev FiniteComplex := QuadraticAlgebra ℚ (-1) 0

namespace FiniteComplex

/-- The ring homomorphism embedding rational complex numbers into `ℂ` by casting their real and
imaginary parts. -/
def toComplex : FiniteComplex →+* ℂ where
  toFun z := ⟨(z.re : ℝ), (z.im : ℝ)⟩
  map_zero' := by
    apply Complex.ext <;> simp
  map_one' := by
    apply Complex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by
    apply Complex.ext <;> simp
  map_mul' z w := by
    apply Complex.ext
    · simp; ring
    · simp

/-- The rational bound `|z.re| + |z.im|` on the complex norm of `z`. -/
def absBound (z : FiniteComplex) : ℚ := |z.re| + |z.im|

/-- The embedding of rational complex numbers into `ℂ` is injective. -/
theorem toComplex_injective : Function.Injective toComplex := by
  intro z w h
  have hr : (z.re : ℝ) = (w.re : ℝ) := by
    simpa [toComplex] using congrArg Complex.re h
  have hi : (z.im : ℝ) = (w.im : ℝ) := by
    simpa [toComplex] using congrArg Complex.im h
  apply QuadraticAlgebra.ext
  · exact_mod_cast hr
  · exact_mod_cast hi

/-- The norm of the complex embedding of `z` is bounded by its rational `absBound`, cast to `ℝ`. -/
theorem norm_toComplex_le_absBound (z : FiniteComplex) :
    ‖toComplex z‖ ≤ (absBound z : ℝ) := by
  simpa [toComplex, absBound] using complex_norm_le_abs_re_add_abs_im (toComplex z)

end FiniteComplex

/-- The entrywise embedding of a matrix over `FiniteComplex` into complex matrices. -/
def toComplexMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) FiniteComplex) :
    Matrix (Fin n) (Fin n) ℂ := A.map FiniteComplex.toComplex

/-- Finite rational complex data for a resolvent node, consisting of a matrix `A`, a spectral
parameter `z`, and a proposed inverse `B`. -/
structure FiniteResolventNode (n : ℕ) where
  A : Matrix (Fin n) (Fin n) FiniteComplex
  z : FiniteComplex
  B : Matrix (Fin n) (Fin n) FiniteComplex

namespace FiniteResolventNode

/-- The finite matrix `z • 1 - A` associated with a resolvent node. -/
def resolventMatrix {n : ℕ} (N : FiniteResolventNode n) :
    Matrix (Fin n) (Fin n) FiniteComplex := Matrix.diagonal (fun _ => N.z) - N.A

/-- The residual matrix `1 - N.resolventMatrix * N.B` of the proposed inverse. -/
def residual {n : ℕ} (N : FiniteResolventNode n) :
    Matrix (Fin n) (Fin n) FiniteComplex := 1 - N.resolventMatrix * N.B

/-- The sum of the rational `absBound` values of all residual entries. -/
def residualBound {n : ℕ} (N : FiniteResolventNode n) : ℚ :=
  ∑ i, ∑ j, FiniteComplex.absBound (N.residual i j)

/-- The Boolean test that the proposed inverse has nonzero determinant and the rational residual
bound is less than one. -/
def check {n : ℕ} (N : FiniteResolventNode n) : Bool :=
  decide (N.B.det ≠ 0) && decide (N.residualBound < 1)

/-- Embedding the finite resolvent matrix into complex matrices gives `z • 1 - A` with the
corresponding embedded data. -/
theorem toComplex_resolventMatrix {n : ℕ} (N : FiniteResolventNode n) :
    toComplexMatrix N.resolventMatrix =
      FiniteComplex.toComplex N.z • (1 : Matrix (Fin n) (Fin n) ℂ) -
        toComplexMatrix N.A := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [resolventMatrix, toComplexMatrix, FiniteComplex.toComplex, Complex.ext_iff]
  · simp [resolventMatrix, toComplexMatrix, h, FiniteComplex.toComplex, Complex.ext_iff]

/-- Embedding the finite residual gives the complex residual `1 - (z • 1 - A) * B`. -/
theorem toComplex_residual {n : ℕ} (N : FiniteResolventNode n) :
    toComplexMatrix N.residual =
      (1 : Matrix (Fin n) (Fin n) ℂ) -
        (FiniteComplex.toComplex N.z • (1 : Matrix (Fin n) (Fin n) ℂ) -
          toComplexMatrix N.A) * toComplexMatrix N.B := by
  change FiniteComplex.toComplex.mapMatrix (1 - N.resolventMatrix * N.B) =
    1 - (FiniteComplex.toComplex N.z • 1 - FiniteComplex.toComplex.mapMatrix N.A) *
      FiniteComplex.toComplex.mapMatrix N.B
  rw [map_sub, map_one, map_mul]
  exact congrArg (fun X : Matrix (Fin n) (Fin n) ℂ =>
    1 - X * FiniteComplex.toComplex.mapMatrix N.B) (toComplex_resolventMatrix N)

/-- The complex operator norm of a node's residual is bounded by its rational `residualBound`,
cast to `ℝ`. -/
theorem residual_norm_le {n : ℕ} (N : FiniteResolventNode n) :
    ‖(1 : Matrix (Fin n) (Fin n) ℂ) -
      (FiniteComplex.toComplex N.z • (1 : Matrix (Fin n) (Fin n) ℂ) -
        toComplexMatrix N.A) * toComplexMatrix N.B‖ ≤ (N.residualBound : ℝ) := by
  rw [← toComplex_residual]
  calc
    ‖toComplexMatrix N.residual‖ ≤ ∑ i, ∑ j, ‖toComplexMatrix N.residual i j‖ :=
      operator_norm_le_entry_sum _
    _ ≤ ∑ i, ∑ j, (FiniteComplex.absBound (N.residual i j) : ℝ) := by
      exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
        FiniteComplex.norm_toComplex_le_absBound _
    _ = (N.residualBound : ℝ) := by simp [residualBound]

/-- A nonzero determinant of the finite proposed inverse implies that its complex embedding is a
unit. -/
theorem isUnit_toComplexMatrix_of_det_ne_zero {n : ℕ} (N : FiniteResolventNode n)
    (h : N.B.det ≠ 0) : IsUnit (toComplexMatrix N.B) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  change (toComplexMatrix N.B).det ≠ 0
  rw [show (toComplexMatrix N.B).det = FiniteComplex.toComplex N.B.det by
    exact (FiniteComplex.toComplex.map_det N.B).symm]
  exact fun hz => h (FiniteComplex.toComplex_injective (by simpa using hz))

/-- A successful node check certifies that the embedded proposed inverse is a unit and that its
residual norm is bounded by a real number less than one. -/
theorem certificate_of_check {n : ℕ} (N : FiniteResolventNode n) (h : N.check = true) :
    IsUnit (toComplexMatrix N.B) ∧
      ‖(1 : Matrix (Fin n) (Fin n) ℂ) -
        (FiniteComplex.toComplex N.z • (1 : Matrix (Fin n) (Fin n) ℂ) -
          toComplexMatrix N.A) * toComplexMatrix N.B‖ ≤ (N.residualBound : ℝ) ∧
      (N.residualBound : ℝ) < 1 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨isUnit_toComplexMatrix_of_det_ne_zero N h.1, residual_norm_le N, by exact_mod_cast h.2⟩

end FiniteResolventNode

/-- Scalar expression trees built from complex constants, the identity function, addition,
multiplication, and reciprocal. -/
inductive ScalarProgram where
  | const (z : ℂ)
  | id
  | add (f g : ScalarProgram)
  | mul (f g : ScalarProgram)
  | inv (f : ScalarProgram)

/-- Evaluate a scalar expression tree as a function from complex numbers to complex numbers. -/
def ScalarProgram.eval : ScalarProgram → ℂ → ℂ
  | .const z, _ => z
  | .id, z => z
  | .add f g, z => f.eval z + g.eval z
  | .mul f g, z => f.eval z * g.eval z
  | .inv f, z => (f.eval z)⁻¹

/-- The arithmetic operation count of a scalar expression tree, assigning unit cost to addition,
multiplication, and reciprocal. -/
def ScalarProgram.cost : ScalarProgram → ℕ
  | .const _ => 0
  | .id => 0
  | .add f g => f.cost + g.cost + 1
  | .mul f g => f.cost + g.cost + 1
  | .inv f => f.cost + 1

/-- The cost `n * n` assigned to reading a supplied square inverse matrix. -/
def inverseReadCost (n : ℕ) : ℕ := n * n

/-- Matrix expression trees built from supplied matrices, addition, scalar multiplication, and
matrix multiplication. -/
inductive InverseProgram (n : ℕ) where
  | supplied (B : Matrix (Fin n) (Fin n) ℂ)
  | add (J K : InverseProgram n)
  | smul (c : ℂ) (J : InverseProgram n)
  | mul (J K : InverseProgram n)

/-- Evaluate a matrix expression tree in the complex square matrices. -/
def InverseProgram.eval {n : ℕ} : InverseProgram n → Matrix (Fin n) (Fin n) ℂ
  | .supplied B => B
  | .add J K => J.eval + K.eval
  | .smul c J => c • J.eval
  | .mul J K => J.eval * K.eval

/-- The recursive cost of a matrix expression tree, charging quadratic cost for reading,
addition, and scaling and cubic cost for multiplication. -/
def InverseProgram.cost {n : ℕ} : InverseProgram n → ℕ
  | .supplied _ => inverseReadCost n
  | .add J K => J.cost + K.cost + n * n
  | .smul _ J => J.cost + n * n
  | .mul J K => J.cost + K.cost + n * n * n

/-- Data for finite resolvent quadrature, including a scalar expression, nodes, weights,
proposed inverse programs, and residual bounds. -/
structure QuadratureProgram (n m : ℕ) where
  scalar : ScalarProgram
  z : Fin m → ℂ
  weight : Fin m → ℂ
  inverseProgram : Fin m → InverseProgram n
  residualBound : Fin m → ℝ

namespace QuadratureProgram

/-- Evaluate the proposed inverse program at the specified quadrature node. -/
def approximateInverse {n m : ℕ} (P : QuadratureProgram n m) (i : Fin m) :
    Matrix (Fin n) (Fin n) ℂ := (P.inverseProgram i).eval

end QuadratureProgram

/-- The cost `2 * (n * n)` assigned to combining a weighted matrix contribution. -/
def combinationCost (n : ℕ) : ℕ := 2 * (n * n)

/-- The sum of inverse program cost, scalar evaluation cost, and matrix combination cost at one
node. -/
def nodeCost (n : ℕ) (f : ScalarProgram) (J : InverseProgram n) : ℕ :=
  J.cost + f.cost + combinationCost n

/-- The total cost of the inverse programs over all quadrature nodes. -/
def inversionProgramCost {n m : ℕ} (P : QuadratureProgram n m) : ℕ :=
  ∑ i : Fin m, (P.inverseProgram i).cost

/-- The total node cost of a quadrature program. -/
def programCost {n m : ℕ} (P : QuadratureProgram n m) : ℕ :=
  ∑ i : Fin m, nodeCost n P.scalar (P.inverseProgram i)

/-- The weighted sum of exact matrix resolvents, with coefficients obtained by evaluating the
scalar program at the nodes. -/
def exactQuadrature {n m : ℕ} (P : QuadratureProgram n m)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ i : Fin m, (P.weight i * P.scalar.eval (P.z i)) • resolvent A (P.z i)

/-- The weighted sum of the evaluated proposed inverse programs. -/
def approximateQuadrature {n m : ℕ} (P : QuadratureProgram n m) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ i : Fin m, (P.weight i * P.scalar.eval (P.z i)) • P.approximateInverse i

/-- The condition that every proposed inverse is a unit and has residual bounded by its
prescribed bound, which is less than one. -/
def Certified {n m : ℕ} (P : QuadratureProgram n m)
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i : Fin m, IsUnit (P.approximateInverse i) ∧
    ‖(1 : Matrix (Fin n) (Fin n) ℂ) -
      (P.z i • (1 : Matrix (Fin n) (Fin n) ℂ) - A) * P.approximateInverse i‖ ≤
        P.residualBound i ∧ P.residualBound i < 1

/-- The prescribed arithmetic cost `2 * n.factorial * n + n * n * n + 2 * n * n + 2` of checking
a finite certificate. -/
def certificateCost (n : ℕ) : ℕ := 2 * n.factorial * n + n * n * n + 2 * n * n + 2

namespace FiniteResolventNode

/-- The one-node quadrature program determined by a finite resolvent node, a scalar expression,
and a weight. -/
def program {n : ℕ} (N : FiniteResolventNode n) (scalar : ScalarProgram)
    (weight : ℂ) : QuadratureProgram n 1 where
  scalar := scalar
  z := fun _ => FiniteComplex.toComplex N.z
  weight := fun _ => weight
  inverseProgram := fun _ => .supplied (toComplexMatrix N.B)
  residualBound := fun _ => (N.residualBound : ℝ)

/-- A successful finite node check certifies its associated one-node quadrature program for the
embedded matrix. -/
theorem program_certified {n : ℕ} (N : FiniteResolventNode n)
    (scalar : ScalarProgram) (weight : ℂ) (h : N.check = true) :
    Certified (N.program scalar weight) (toComplexMatrix N.A) := by
  intro i
  simpa [program, QuadratureProgram.approximateInverse, InverseProgram.eval] using
    N.certificate_of_check h

/-- A successful finite node check certifies invertibility of the resolvent matrix and bounds
the error of the embedded proposed inverse. -/
theorem resolvent_error_of_check {n : ℕ} (N : FiniteResolventNode n)
    (h : N.check = true) :
    IsUnit (toComplexMatrix N.resolventMatrix) ∧
      ‖resolvent (toComplexMatrix N.A) (FiniteComplex.toComplex N.z) -
        toComplexMatrix N.B‖ ≤
          ‖toComplexMatrix N.B‖ * (N.residualBound : ℝ) /
            (1 - (N.residualBound : ℝ)) := by
  rw [toComplex_resolventMatrix]
  exact resolvent_error_of_certificate (toComplexMatrix N.A) (toComplexMatrix N.B)
    (FiniteComplex.toComplex N.z) (N.residualBound : ℝ)
    (N.certificate_of_check h).1 (N.certificate_of_check h).2.2
    (N.certificate_of_check h).2.1

/-- The certificate checking cost plus the cost of the associated one-node quadrature program. -/
def checkedProgramCost {n : ℕ} (N : FiniteResolventNode n)
    (scalar : ScalarProgram) (weight : ℂ) : ℕ :=
  certificateCost n + programCost (N.program scalar weight)

/-- The checked program cost is the certificate cost plus the inverse read, scalar evaluation,
and combination costs. -/
theorem checkedProgramCost_eq {n : ℕ} (N : FiniteResolventNode n)
    (scalar : ScalarProgram) (weight : ℂ) :
    checkedProgramCost N scalar weight =
      certificateCost n + (inverseReadCost n + scalar.cost + combinationCost n) := by
  simp [checkedProgramCost, programCost, nodeCost, program, InverseProgram.cost]

end FiniteResolventNode

/-- The residual-based inverse error expression at a quadrature node. -/
def nodeError {n m : ℕ} (P : QuadratureProgram n m) (i : Fin m) : ℝ :=
  ‖P.approximateInverse i‖ * P.residualBound i / (1 - P.residualBound i)

/-- The sum of node error expressions weighted by the norms of the quadrature coefficients. -/
def quadratureError {n m : ℕ} (P : QuadratureProgram n m) : ℝ :=
  ∑ i : Fin m, ‖P.weight i * P.scalar.eval (P.z i)‖ * nodeError P i

/-- For a certified quadrature program, the norm of the difference between its exact and
approximate quadrature sums is at most `quadratureError P`. -/
theorem exact_sub_approximate_norm_le {n m : ℕ} (P : QuadratureProgram n m)
    (A : Matrix (Fin n) (Fin n) ℂ) (hP : Certified P A) :
    ‖exactQuadrature P A - approximateQuadrature P‖ ≤ quadratureError P := by
  rw [show exactQuadrature P A - approximateQuadrature P =
    ∑ i : Fin m, (P.weight i * P.scalar.eval (P.z i)) •
      (resolvent A (P.z i) - P.approximateInverse i) by
    simp only [exactQuadrature, approximateQuadrature, ← Finset.sum_sub_distrib, smul_sub]]
  refine (norm_sum_le_of_le Finset.univ fun i _ => ?_).trans_eq rfl
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (resolvent_error_of_certificate A (P.approximateInverse i) (P.z i)
      (P.residualBound i) (hP i).1 (hP i).2.2 (hP i).2.1).2
    (norm_nonneg _)

/-- A representation error at most `η` and a certified quadrature program give total
approximation error at most `η + quadratureError P`. -/
theorem nonnormal_quadrature_error {n m : ℕ} (P : QuadratureProgram n m)
    (A fA : Matrix (Fin n) (Fin n) ℂ) (η : ℝ) (hP : Certified P A)
    (hrep : ‖fA - exactQuadrature P A‖ ≤ η) :
    ‖fA - approximateQuadrature P‖ ≤ η + quadratureError P := by
  calc
    ‖fA - approximateQuadrature P‖ ≤ ‖fA - exactQuadrature P A‖ +
        ‖exactQuadrature P A - approximateQuadrature P‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le (fA - exactQuadrature P A)
          (exactQuadrature P A - approximateQuadrature P)
    _ ≤ η + quadratureError P := add_le_add hrep (exact_sub_approximate_norm_le P A hP)

instance matrixCStarAlgebra {I : Type} [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

instance matrixContinuousFunctionalCalculus {I : Type} [Fintype I] [DecidableEq I] :
    ContinuousFunctionalCalculus ℂ (Matrix I I ℂ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- For a normal matrix and a scalar function continuous on its spectrum, a certified quadrature
approximation has functional calculus error at most `η + quadratureError P` under the stated
representation bound. -/
theorem normal_quadrature_error {n m : ℕ} (P : QuadratureProgram n m)
    (A : Matrix (Fin n) (Fin n) ℂ) [IsStarNormal A] (η : ℝ)
    (hcont : ContinuousOn P.scalar.eval (spectrum ℂ A)) (hP : Certified P A)
    (hrep : ‖cfc P.scalar.eval A - exactQuadrature P A‖ ≤ η) :
    ContinuousOn P.scalar.eval (spectrum ℂ A) ∧
      ‖cfc P.scalar.eval A - approximateQuadrature P‖ ≤ η + quadratureError P :=
  ⟨hcont, nonnormal_quadrature_error P A (cfc P.scalar.eval A) η hP hrep⟩

/-- The total program cost equals the inverse program cost plus `m` copies of the scalar
evaluation and matrix combination costs. -/
theorem programCost_eq {n m : ℕ} (P : QuadratureProgram n m) :
    programCost P = inversionProgramCost P + m * (P.scalar.cost + 2 * (n * n)) := by
  simp [programCost, nodeCost, inversionProgramCost, combinationCost,
    Finset.sum_add_distrib, Nat.mul_add, add_assoc]

/-- A nonnegative Schur multiplier bound `M` transports the certified quadrature error bound to
`M * (η + quadratureError P)`. -/
theorem schur_multiplier_error_transport {n m : ℕ} (P : QuadratureProgram n m)
    (A fA B : Matrix (Fin n) (Fin n) ℂ) (η M : ℝ) (hP : Certified P A)
    (hrep : ‖fA - exactQuadrature P A‖ ≤ η) (hM : 0 ≤ M)
    (hB : Qatlib.Concepts.OrderedOracle.TiSdpBridge.SchurMultiplierBounded B M) :
    ‖B ⊙ (fA - approximateQuadrature P)‖ ≤ M * (η + quadratureError P) :=
  (hB fA (approximateQuadrature P)).trans
    (mul_le_mul_of_nonneg_left (nonnormal_quadrature_error P A fA η hP hrep) hM)

/-- Collect the residual inverse estimate, normal and general quadrature error bounds, program
cost formula, and soundness and cost statements for finite node checks. -/
theorem frontier1 :
    (∀ {R : Type} [NormedRing R] [HasSummableGeomSeries R] (M B : R) (q : ℝ),
      IsUnit B → q < 1 → ‖1 - M * B‖ ≤ q →
        IsUnit M ∧ ‖M⁻¹ʳ - B‖ ≤ ‖B‖ * q / (1 - q)) ∧
    (∀ {n m : ℕ} (P : QuadratureProgram n m)
      (A fA : Matrix (Fin n) (Fin n) ℂ) (η : ℝ), Certified P A →
      ‖fA - exactQuadrature P A‖ ≤ η →
      ‖fA - approximateQuadrature P‖ ≤ η + quadratureError P) ∧
    (∀ {n m : ℕ} (P : QuadratureProgram n m)
      (A : Matrix (Fin n) (Fin n) ℂ) [IsStarNormal A] (η : ℝ),
      ContinuousOn P.scalar.eval (spectrum ℂ A) → Certified P A →
      ‖cfc P.scalar.eval A - exactQuadrature P A‖ ≤ η →
      ContinuousOn P.scalar.eval (spectrum ℂ A) ∧
        ‖cfc P.scalar.eval A - approximateQuadrature P‖ ≤ η + quadratureError P) ∧
    (∀ {n m : ℕ} (P : QuadratureProgram n m),
      programCost P = inversionProgramCost P + m * (P.scalar.cost + 2 * (n * n))) ∧
    (∀ {n : ℕ} (N : FiniteResolventNode n), N.check = true →
      IsUnit (toComplexMatrix N.resolventMatrix) ∧
        ‖resolvent (toComplexMatrix N.A) (FiniteComplex.toComplex N.z) -
          toComplexMatrix N.B‖ ≤ ‖toComplexMatrix N.B‖ * (N.residualBound : ℝ) /
            (1 - (N.residualBound : ℝ))) ∧
    (∀ {n : ℕ} (N : FiniteResolventNode n) (scalar : ScalarProgram) (weight : ℂ),
      N.check = true → Certified (N.program scalar weight) (toComplexMatrix N.A)) ∧
    (∀ {n : ℕ} (N : FiniteResolventNode n) (scalar : ScalarProgram) (weight : ℂ),
      FiniteResolventNode.checkedProgramCost N scalar weight =
        certificateCost n + (inverseReadCost n + scalar.cost + combinationCost n)) := by
  exact ⟨inverse_error_of_residual, nonnormal_quadrature_error,
    normal_quadrature_error, programCost_eq, FiniteResolventNode.resolvent_error_of_check,
    FiniteResolventNode.program_certified, FiniteResolventNode.checkedProgramCost_eq⟩

end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
