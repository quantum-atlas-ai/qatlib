/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AncilFreeClfT14.MainResults.CoreModel

@[expose] public section


/-! # Preserved closed legacy mathematics
This module uses the archived coefficient model at the fixed public pin.
It does not identify free operation counts with Clifford+T circuit costs.
-/
set_option autoImplicit false
noncomputable section
open scoped Real
open Complex
namespace Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
open Qatlib.Papers.AncilFreeClfT14.MainResults

/-- `ω³ + ω = i√2`.  Together with `ω - ω³ = √2` this is what lets us pass
between the paper's `aω³ + bω² + cω + d` coordinates and the complex
coordinates used in Lemma 5.5. -/
theorem omega_add_omega_cube :
    omega ^ 3 + omega = Complex.I * (Real.sqrt 2 : ℂ) := by
  have h1 : Complex.I * omega = omega ^ 3 := by
    rw [omega_cube]
    ring
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h2 : Complex.I * omega ^ 3 = -omega := by
    calc Complex.I * omega ^ 3 = Complex.I * (omega * Complex.I) := by rw [omega_cube]
      _ = omega * (Complex.I * Complex.I) := by ring
      _ = omega * (-1) := by rw [hI2]
      _ = -omega := by ring
  calc omega ^ 3 + omega = Complex.I * omega - Complex.I * omega ^ 3 := by
        rw [h1, h2]; ring
    _ = Complex.I * (omega - omega ^ 3) := by ring
    _ = Complex.I * (Real.sqrt 2 : ℂ) := by rw [omega_sub_omega_cube]

/-- `ω = √2/2 + i√2/2`, obtained by adding `ω - ω³ = √2` and `ω³ + ω = i√2`. -/
theorem omega_eq_sqrt2_half :
    omega = ((Real.sqrt 2 / 2 : ℝ) : ℂ) +
      Complex.I * ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  have h1 := omega_sub_omega_cube
  have h2 := omega_add_omega_cube
  have hsum : (2 : ℂ) * omega =
      ((Real.sqrt 2 : ℂ) + Complex.I * (Real.sqrt 2 : ℂ)) := by
    calc (2 : ℂ) * omega = (omega - omega ^ 3) + (omega ^ 3 + omega) := by ring
      _ = ((Real.sqrt 2 : ℂ) + Complex.I * (Real.sqrt 2 : ℂ)) := by rw [h1, h2]
  calc omega = (2 : ℂ) * omega / 2 := by ring
    _ = (((Real.sqrt 2 : ℂ) + Complex.I * (Real.sqrt 2 : ℂ))) / 2 := by rw [hsum]
    _ = ((Real.sqrt 2 / 2 : ℝ) : ℂ) +
          Complex.I * ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
        push_cast
        ring

namespace Zomega

/-- Coordinate decomposition of `aω³ + bω² + cω + d` in the basis
`(ω - ω³, ω³ + ω)` of the `√2`-direction.  This is the computational heart of
Lemma 5.5: the real `√2`-coefficient is `(c-a)/2` and the imaginary
`√2`-coefficient is `(c+a)/2`, whose integrality on each parity class is
exactly the paper's even/odd case distinction. -/
theorem toComplex_decomp (w : Zomega) :
    w.toComplex = (w.d : ℂ) + (w.b : ℂ) * Complex.I +
      (((w.c - w.a : ℤ) : ℂ) / 2) * (omega - omega ^ 3) +
      (((w.c + w.a : ℤ) : ℂ) / 2) * (omega ^ 3 + omega) := by
  simp only [Zomega.toComplex]
  rw [omega_cube, omega_sq]
  push_cast
  ring_nf

end Zomega

/-! ## Lemma 5.5 -/

/-- **Lemma 5.5** (arXiv:1403.2975v3, p. 15).  Every element of `ℤ[ω]` is of
the form `α + βi` or `α + βi + ω` with `α, β ∈ ℤ[√2]`.

Proof (the paper's): writing `u = aω³ + bω² + cω + d`, we have
`u = d + b·i + (c-a)/2·(ω-ω³) + (c+a)/2·(ω³+ω)`
(`Zomega.toComplex_decomp`), and `(c-a)/2`, `(c+a)/2` are simultaneously
integers when `c-a` is even, and simultaneously half-integers when `c-a` is
odd (in which case `(c-a)/2 = m + 1/2` and the leftover is exactly `ω`).
Conversely an explicit coordinate vector is produced for each of the two
cases. -/
theorem lemma_5_5 (u : ℂ) :
    u ∈ ZomegaSet ↔
      ∃ α β : Zsqrt2,
        u = α.toComplex + β.toComplex * Complex.I ∨
        u = α.toComplex + β.toComplex * Complex.I + omega := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Int.even_or_odd (w.c - w.a)
    · -- Even case: `w.c - w.a = 2m`, and `w.c + w.a = 2(a+m)`.
      have hm2 : w.c - w.a = 2 * m := by omega
      have hc : w.c + w.a = 2 * (w.a + m) := by omega
      refine ⟨⟨w.d, m⟩, ⟨w.b, w.a + m⟩, Or.inl ?_⟩
      rw [Zomega.toComplex_decomp]
      have h1 : (((w.c - w.a : ℤ)) : ℂ) / 2 = (m : ℂ) := by
        rw [hm2]; push_cast; ring
      have h2 : (((w.c + w.a : ℤ)) : ℂ) / 2 = ((w.a + m : ℤ) : ℂ) := by
        rw [hc]; push_cast; ring
      rw [h1, h2, omega_sub_omega_cube, omega_add_omega_cube]
      simp [Zsqrt2.toComplex]
      ring
    · -- Odd case: `w.c - w.a = 2m+1`, and `w.c + w.a = 2(a+m)+1`.
      have hm2 : w.c - w.a = 2 * m + 1 := by omega
      have hc : w.c + w.a = 2 * (w.a + m) + 1 := by omega
      refine ⟨⟨w.d, m⟩, ⟨w.b, w.a + m⟩, Or.inr ?_⟩
      rw [Zomega.toComplex_decomp]
      have h1 : (((w.c - w.a : ℤ)) : ℂ) / 2 = (m : ℂ) + 1 / 2 := by
        rw [hm2]; push_cast; ring
      have h2 : (((w.c + w.a : ℤ)) : ℂ) / 2 = ((w.a + m : ℤ) : ℂ) + 1 / 2 := by
        rw [hc]; push_cast; ring
      rw [h1, h2, omega_sub_omega_cube, omega_add_omega_cube, omega_eq_sqrt2_half]
      simp [Zsqrt2.toComplex]
      ring
  · -- Conversely, both displayed forms are in `ℤ[ω]`.
    rintro ⟨α, β, h | h⟩
    · refine ⟨⟨β.b - α.b, β.a, α.b + β.b, α.a⟩, ?_⟩
      rw [h, Zomega.toComplex_decomp, omega_sub_omega_cube, omega_add_omega_cube]
      simp [Zsqrt2.toComplex]
      ring
    · refine ⟨⟨β.b - α.b, β.a, α.b + β.b + 1, α.a⟩, ?_⟩
      rw [h, Zomega.toComplex_decomp, omega_sub_omega_cube, omega_add_omega_cube,
        omega_eq_sqrt2_half]
      simp [Zsqrt2.toComplex]
      ring

/-- A grid operator in the explicit form (7) of Lemma 5.11, with the integer
data only (validity of the parity conditions is a separate predicate). -/
structure FormGridOperator where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  a' : ℤ
  b' : ℤ
  c' : ℤ
  d' : ℤ

namespace FormGridOperator

/-- The real matrix of the operator, in the form (7). -/
def mat (G : FormGridOperator) : Mat2 :=
  ⟨(G.a : ℝ) + (G.a' : ℝ) / Real.sqrt 2,
   (G.b : ℝ) + (G.b' : ℝ) / Real.sqrt 2,
   (G.c : ℝ) + (G.c' : ℝ) / Real.sqrt 2,
   (G.d : ℝ) + (G.d' : ℝ) / Real.sqrt 2⟩

/-- Entrywise 2-conjugation `G•`: replace `a', b', c', d'` by their negatives,
as in Remark 5.12. -/
def bullet (G : FormGridOperator) : FormGridOperator :=
  ⟨G.a, G.b, G.c, G.d, -G.a', -G.b', -G.c', -G.d'⟩

/-- The parity conditions of Lemma 5.11. -/
def valid (G : FormGridOperator) : Prop :=
  (G.a + G.b + G.c + G.d) % 2 = 0 ∧
    G.a' % 2 = G.b' % 2 ∧ G.b' % 2 = G.c' % 2 ∧ G.c' % 2 = G.d' % 2

/-- A special grid operator: determinant `±1` (Definition 5.10). -/
def special (G : FormGridOperator) : Prop :=
  G.mat.det = 1 ∨ G.mat.det = -1

end FormGridOperator

/-- The image `M(A) = {M u | u ∈ A}` of a real matrix acting on the plane. -/
def matImage (M : Mat2) (A : Set ℂ) : Set ℂ := {z | ∃ u ∈ A, z = M.apply u}

end Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
