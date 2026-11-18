/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

/-!
# Null electromagnetic fields and Hopf coordinates

[IrvineBouwmeester2008KnottedLight], pp. 716–719,
[DOI](https://doi.org/10.1038/nphys1056).
The Riemann–Silberstein vector uses the complex **bilinear** dot product,
not the Hermitian inner product. Its real and imaginary invariants are computed
exactly. Inverse stereographic coordinates and the polynomial Hopf map preserve
the appropriate sphere equations; quaternionic tangent vectors form an orthogonal
frame on the unit three-sphere. These algebraic results do not prove linking
numbers, global Maxwell evolution, finite spatial energy, or optical realizability.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HopfField

/-- The bilinear Cartesian dot product, valid over real or complex scalars. -/
def dot3 {R : Type*} [CommRing R] (u v : Fin 3 → R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The oriented Cartesian cross product. -/
def cross3 {R : Type*} [CommRing R] (u v : Fin 3 → R) : Fin 3 → R :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- Squared Euclidean length in Cartesian coordinates. -/
def squaredLength (u : Fin 3 → ℝ) : ℝ := dot3 u u

/-- The complex field with real electric and imaginary magnetic components. -/
def riemannSilberstein (E B : Fin 3 → ℝ) : Fin 3 → ℂ :=
  fun j => (E j : ℂ) + Complex.I * (B j : ℂ)

/-- The real null invariant is the difference of squared field magnitudes. -/
theorem complex_square_re (E B : Fin 3 → ℝ) :
    (dot3 (riemannSilberstein E B) (riemannSilberstein E B)).re =
      squaredLength E - squaredLength B := by
  simp [dot3, riemannSilberstein, squaredLength, Complex.mul_re, Complex.mul_im]
  ring

/-- The imaginary null invariant is twice the electric–magnetic dot product. -/
theorem complex_square_im (E B : Fin 3 → ℝ) :
    (dot3 (riemannSilberstein E B) (riemannSilberstein E B)).im =
      2 * dot3 E B := by
  simp [dot3, riemannSilberstein, Complex.mul_re, Complex.mul_im]
  ring

/-- Nullness is equivalent to orthogonality and equality of squared Euclidean lengths. -/
theorem null_iff (E B : Fin 3 → ℝ) :
    dot3 (riemannSilberstein E B) (riemannSilberstein E B) = 0 ↔
      dot3 E B = 0 ∧ squaredLength E = squaredLength B := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    rw [complex_square_re] at hr
    rw [complex_square_im] at hi
    simp only [Complex.zero_re, Complex.zero_im] at hr hi
    constructor <;> linarith
  · rintro ⟨ho, he⟩
    apply Complex.ext
    · rw [complex_square_re, Complex.zero_re, he, sub_self]
    · rw [complex_square_im, Complex.zero_im, ho, mul_zero]

/-- A cross product is orthogonal to its first factor. -/
theorem dot_cross_left {R : Type*} [CommRing R] (u v : Fin 3 → R) :
    dot3 (cross3 u v) u = 0 := by
  simp [dot3, cross3]
  ring

/-- A cross product is orthogonal to its second factor. -/
theorem dot_cross_right {R : Type*} [CommRing R] (u v : Fin 3 → R) :
    dot3 (cross3 u v) v = 0 := by
  simp [dot3, cross3]
  ring

/-- Lagrange's identity holds for the bilinear dot product, including over the complexes. -/
theorem cross_square {R : Type*} [CommRing R] (u v : Fin 3 → R) :
    dot3 (cross3 u v) (cross3 u v) = dot3 u u * dot3 v v - (dot3 u v) ^ 2 := by
  simp [dot3, cross3]
  ring

/-- Four-dimensional squared length in real coordinates. -/
def square4 (q : Fin 4 → ℝ) : ℝ :=
  q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2

/-- The real Cartesian dot product in four dimensions. -/
def dot4 (q r : Fin 4 → ℝ) : ℝ :=
  q 0 * r 0 + q 1 * r 1 + q 2 * r 2 + q 3 * r 3

/-- Inverse stereographic projection with the north pole omitted. -/
noncomputable def stereo (x y z : ℝ) : Fin 4 → ℝ :=
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  ![2 * x / d, 2 * y / d, 2 * z / d, (x ^ 2 + y ^ 2 + z ^ 2 - 1) / d]

/-- The stereographic denominator never vanishes on real three-space. -/
theorem stereo_denominator_pos (x y z : ℝ) : 0 < x ^ 2 + y ^ 2 + z ^ 2 + 1 := by
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]

/-- Inverse stereographic projection lands exactly on the unit three-sphere. -/
theorem stereo_unit (x y z : ℝ) : square4 (stereo x y z) = 1 := by
  have hd := ne_of_gt (stereo_denominator_pos x y z)
  simp [square4, stereo]
  field_simp [hd]
  ring

/-- The polynomial Hopf map in real coordinates, with a fixed orientation. -/
def hopf (q : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![2 * (q 0 * q 2 + q 1 * q 3), 2 * (q 1 * q 2 - q 0 * q 3),
    q 0 ^ 2 + q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2]

/-- The Hopf polynomial converts the sphere equation into its square. -/
theorem hopf_square (q : Fin 4 → ℝ) : squaredLength (hopf q) = square4 q ^ 2 := by
  simp [squaredLength, dot3, hopf, square4]
  ring

/-- The Hopf map sends the unit three-sphere to the unit two-sphere. -/
theorem hopf_unit (q : Fin 4 → ℝ) (hq : square4 q = 1) :
    squaredLength (hopf q) = 1 := by rw [hopf_square, hq, one_pow]

/-- Simultaneous complex phase multiplication in real coordinates. -/
def phaseRotate (c s : ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![c * q 0 - s * q 1, s * q 0 + c * q 1,
    c * q 2 - s * q 3, s * q 2 + c * q 3]

/-- Unit complex phase rotations stay in a Hopf fibre. -/
theorem hopf_phase_invariant (c s : ℝ) (q : Fin 4 → ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    hopf (phaseRotate c s q) = hopf q := by
  funext j
  fin_cases j <;> simp [hopf, phaseRotate]
  · linear_combination (q 0 * q 2 + q 1 * q 3) * h
  · linear_combination (q 1 * q 2 - q 0 * q 3) * h
  · linear_combination (q 0 ^ 2 + q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2) * h

/-- The first quaternionic tangent direction. -/
def frameFirst (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![-q 1, q 0, -q 3, q 2]

/-- The second quaternionic tangent direction. -/
def frameSecond (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![-q 2, q 3, q 0, -q 1]

/-- The third quaternionic tangent direction completes the three-sphere frame. -/
def frameThird (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![-q 3, -q 2, q 1, q 0]

/-- Quaternionic tangent vectors are tangent, mutually orthogonal and length preserving. -/
theorem frame_orthogonal (q : Fin 4 → ℝ) :
    dot4 q (frameFirst q) = 0 ∧ dot4 q (frameSecond q) = 0 ∧
      dot4 (frameFirst q) (frameSecond q) = 0 ∧
      square4 (frameFirst q) = square4 q ∧ square4 (frameSecond q) = square4 q := by
  simp [dot4, square4, frameFirst, frameSecond]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The third direction is tangent, orthogonal to the first two and length preserving. -/
theorem frame_third_orthogonal (q : Fin 4 → ℝ) :
    dot4 q (frameThird q) = 0 ∧ dot4 (frameFirst q) (frameThird q) = 0 ∧
      dot4 (frameSecond q) (frameThird q) = 0 ∧ square4 (frameThird q) = square4 q := by
  simp [dot4, square4, frameFirst, frameSecond, frameThird]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end Qatlib.Papers.KnottedLight08.HopfField
