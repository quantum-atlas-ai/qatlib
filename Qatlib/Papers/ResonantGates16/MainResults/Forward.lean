/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ResonantGates16.MainResults.SourceModel
public import Mathlib.Tactic

@[expose] public section


/-! Necessary endpoint, unitarity and partial-polynomial bounds for composite rotations. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Papers.ResonantGates16.MainResults.AchievableTuples
open Matrix Polynomial
open Qatlib.Papers.ResonantGates16.MainResults.SourceModel
open scoped Matrix

/-! ## Partial-tuple achievability

A `n`-partial tuple is achievable iff it is consistent with some full
achievable tuple (p. 3, just below Eq. 6). -/

/-- `(A, ·, C, ·)` is achievable: extendable to an achievable full tuple. -/
def AchievableAC (L : ℕ) (A C : Polynomial ℝ) : Prop :=
  ∃ B D : Polynomial ℝ, Achievable L A B C D

/-- `(·, B, C, ·)` is achievable. -/
def AchievableBC (L : ℕ) (B C : Polynomial ℝ) : Prop :=
  ∃ A D : Polynomial ℝ, Achievable L A B C D

/-- `(A, B, ·, ·)` is achievable. -/
def AchievableAB (L : ℕ) (A B : Polynomial ℝ) : Prop :=
  ∃ C D : Polynomial ℝ, Achievable L A B C D

/-- `(·, ·, C, D)` is achievable. -/
def AchievableCD (L : ℕ) (C D : Polynomial ℝ) : Prop :=
  ∃ A B : Polynomial ℝ, Achievable L A B C D

/-- `(A, ·, ·, ·)` is achievable. -/
def AchievableA (L : ℕ) (A : Polynomial ℝ) : Prop :=
  ∃ B C D : Polynomial ℝ, Achievable L A B C D

/-- `(·, B, ·, ·)` is achievable. -/
def AchievableB (L : ℕ) (B : Polynomial ℝ) : Prop :=
  ∃ A C D : Polynomial ℝ, Achievable L A B C D

/-- `(·, ·, C, ·)` is achievable. -/
def AchievableC (L : ℕ) (C : Polynomial ℝ) : Prop :=
  ∃ A B D : Polynomial ℝ, Achievable L A B C D

/-- `(·, ·, ·, D)` is achievable. -/
def AchievableD (L : ℕ) (D : Polynomial ℝ) : Prop :=
  ∃ A B C : Polynomial ℝ, Achievable L A B C D

/-- `A(ix)² + B(ix)²` for real polynomials `A, B` evaluated at the imaginary
point `i x` (used in Theorem 2 condition (3c), p. 4).  `A,B` being real, this
quantity is real for even `L`; we read it through its real part. -/
noncomputable def evalC (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  p.eval₂ Complex.ofRealHom z

/-! ## Proven support: positivity consequences of the normalization (Eq. 7)

The forward directions of Theorems 2 and 3 (the `(a)` conditions and the
3-partial bounds) are, in the paper, immediate from Eq. (7) and the positivity
of the squares.  We isolate and *prove* those consequences here; they are used
as the `→` half of the partial-tuple characterizations where the
achievability part is factored out. -/

/-- Odd `L`, Eq. (7): `A² ≤ 1` (drop `B², C², D² ≥ 0`). -/
theorem norm_odd_A_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 1) (h : NormOK L A B C D) (θ : ℝ) :
    (A.eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_left hL] at hθ
  nlinarith [sq_nonneg (B.eval (Real.cos (θ / 2))),
    sq_nonneg (C.eval (Real.sin (θ / 2))),
    sq_nonneg (D.eval (Real.sin (θ / 2)))]

/-- Odd `L`, Eq. (7): `A² + C² ≤ 1` (drop `B², D² ≥ 0`).  This is condition
(1a) of Theorem 2, p. 3. -/
theorem norm_odd_A_sq_add_C_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 1) (h : NormOK L A B C D) (θ : ℝ) :
    (A.eval (Real.cos (θ / 2))) ^ 2 + (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_left hL] at hθ
  nlinarith [sq_nonneg (B.eval (Real.cos (θ / 2))),
    sq_nonneg (D.eval (Real.sin (θ / 2)))]

/-- Odd `L`, Eq. (7): `C² ≤ 1` (drop `A², B², D² ≥ 0`). -/
theorem norm_odd_C_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 1) (h : NormOK L A B C D) (θ : ℝ) :
    (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_left hL] at hθ
  nlinarith [sq_nonneg (A.eval (Real.cos (θ / 2))),
    sq_nonneg (B.eval (Real.cos (θ / 2))),
    sq_nonneg (D.eval (Real.sin (θ / 2)))]

/-- Even `L`, Eq. (7): `A² ≤ 1`. -/
theorem norm_even_A_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 0) (h : NormOK L A B C D) (θ : ℝ) :
    (A.eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_right (by rw [hL]; norm_num)] at hθ
  nlinarith [sq_nonneg (B.eval (Real.cos (θ / 2))),
    mul_nonneg (sq_nonneg (Real.cos (θ / 2)))
      (sq_nonneg (C.eval (Real.sin (θ / 2)))),
    mul_nonneg (sq_nonneg (Real.cos (θ / 2)))
      (sq_nonneg (D.eval (Real.sin (θ / 2))))]

/-- Even `L`, Eq. (7): `x² C² ≤ 1`. -/
theorem norm_even_x_sq_mul_C_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 0) (h : NormOK L A B C D) (θ : ℝ) :
    (Real.cos (θ / 2)) ^ 2 * (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_right (by rw [hL]; norm_num)] at hθ
  nlinarith [sq_nonneg (A.eval (Real.cos (θ / 2))),
    sq_nonneg (B.eval (Real.cos (θ / 2))),
    mul_nonneg (sq_nonneg (Real.cos (θ / 2)))
      (sq_nonneg (D.eval (Real.sin (θ / 2))))]


/-- A `2×2` complex matrix is unitary when `U†U = 1`. -/
def IsUnitary (U : Matrix (Fin 2) (Fin 2) ℂ) : Prop := Uᴴ * U = 1

/-- The primitive rotation `R̂_φ(θ)` is unitary for real `φ, θ`. -/
theorem primitiveGate_unitary (φ θ : ℝ) : IsUnitary (primitiveGate φ θ) := by
  have hθ := Real.cos_sq_add_sin_sq (θ * (1 / 2))
  have hfac : Real.sin (θ * (1 / 2)) ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2)
      = Real.sin (θ * (1 / 2)) ^ 2 := by
    rw [Real.cos_sq_add_sin_sq φ, mul_one]
  unfold IsUnitary
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primitiveGate, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose,
      Complex.ext_iff, -Complex.ofReal_div, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  all_goals constructor
  all_goals ring_nf
  all_goals nlinarith [hθ, Real.cos_sq_add_sin_sq φ, hfac]

/-- A product of unitary matrices is unitary. -/
theorem IsUnitary.mul {U V : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U * V) := by
  unfold IsUnitary at *
  rw [Matrix.conjTranspose_mul]
  calc Vᴴ * Uᴴ * (U * V) = Vᴴ * (Uᴴ * U) * V := by simp only [Matrix.mul_assoc]
    _ = Vᴴ * 1 * V := by rw [hU]
    _ = 1 := by rw [Matrix.mul_one, hV]

/-- Every composite response `U(θ)` is unitary. -/
theorem qspProduct_unitary (φs : List ℝ) (θ : ℝ) : IsUnitary (qspProduct φs θ) := by
  induction φs with
  | nil => unfold IsUnitary; simp
  | cons φ φs ih => exact ih.mul (primitiveGate_unitary φ θ)

/-- The response of a length-`L` phase vector is unitary. -/
theorem responseMatrix_unitary (L : ℕ) (φs : Fin L → ℝ) (θ : ℝ) :
    IsUnitary (responseMatrix L φs θ) :=
  qspProduct_unitary (List.ofFn φs) θ

/-- An achievable tuple's Eq. (4) matrix is unitary at every `θ`. -/
theorem achievable_tupleMatrix_unitary {L : ℕ} {A B C D : Polynomial ℝ}
    (h : Achievable L A B C D) (θ : ℝ) :
    IsUnitary (tupleMatrix L A B C D θ) := by
  obtain ⟨φs, hφ⟩ := h
  rw [← hφ θ]
  exact responseMatrix_unitary L φs θ

/-- **Theorem 1, condition (2), forward direction.**  An achievable tuple
satisfies `A(1) = 1 ∨ B(1) = 0`: at `θ = 0` the response is the identity, so
the `(0,0)` entry of Eq. (4) is `A(1) + iB(1) = 1`. -/
theorem achievable_endpoint {L : ℕ} {A B C D : Polynomial ℝ}
    (h : Achievable L A B C D) : EndpointOK A B := by
  obtain ⟨φs, hφ⟩ := h
  have hU0 : tupleMatrix L A B C D 0 = 1 := by
    rw [← hφ 0, responseMatrix_zero]
  have h00 := congrFun (congrFun hU0 0) 0
  simp [tupleMatrix, xOf, sigmaX, sigmaY, sigmaZ, idMat] at h00
  have hA : A.eval 1 = 1 := by
    have := congrArg Complex.re h00
    simpa using this
  exact Or.inl hA

/-- **Theorem 1, condition (4), forward direction.**  An achievable tuple
satisfies the unitarity normalisation: the `(0,0)` entry of `U†U = 1` in the
Eq. (4) representation is `A²+B²+C²+D²` (odd `L`) or `A²+B²+x²C²+x²D²`
(even `L`). -/
theorem achievable_norm {L : ℕ} {A B C D : Polynomial ℝ}
    (h : Achievable L A B C D) : NormOK L A B C D := by
  intro θ
  by_cases hL : L % 2 = 1
  · rw [ite_eq_left hL]
    have hunit := achievable_tupleMatrix_unitary h θ
    unfold IsUnitary at hunit
    have h00 := congrFun (congrFun hunit 0) 0
    simp [tupleMatrix, hL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose,
      sigmaX, sigmaY, sigmaZ, idMat, Complex.ext_iff] at h00
    have hreal : (A.eval (Real.cos (θ / 2))) * (A.eval (Real.cos (θ / 2)))
        + (B.eval (Real.cos (θ / 2))) * (B.eval (Real.cos (θ / 2)))
        + ((D.eval (Real.sin (θ / 2))) * (D.eval (Real.sin (θ / 2)))
          + (C.eval (Real.sin (θ / 2))) * (C.eval (Real.sin (θ / 2)))) = 1 := by
      exact_mod_cast h00.1
    nlinarith
  · rw [ite_eq_right hL]
    have hunit := achievable_tupleMatrix_unitary h θ
    unfold IsUnitary at hunit
    have h00 := congrFun (congrFun hunit 0) 0
    simp [tupleMatrix, hL, xOf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose,
      sigmaX, sigmaY, sigmaZ, idMat, Complex.ext_iff, -Complex.ofReal_div,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im] at h00
    have hreal : (A.eval (Real.cos (θ / 2))) * (A.eval (Real.cos (θ / 2)))
        + (B.eval (Real.cos (θ / 2))) * (B.eval (Real.cos (θ / 2)))
        + ((Real.cos (θ / 2) * (D.eval (Real.sin (θ / 2))))
          * (Real.cos (θ / 2) * (D.eval (Real.sin (θ / 2))))
          + (Real.cos (θ / 2) * (C.eval (Real.sin (θ / 2))))
          * (Real.cos (θ / 2) * (C.eval (Real.sin (θ / 2))))) = 1 := by
      exact_mod_cast h00.1
    nlinarith

/-! ## Forward bounds for the partial tuples (Theorems 2 and 3) -/

/-- Odd `L`, Eq. (7): `B² ≤ 1`. -/
theorem norm_odd_B_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 1) (h : NormOK L A B C D) (θ : ℝ) :
    (B.eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_left hL] at hθ
  nlinarith [sq_nonneg (A.eval (Real.cos (θ / 2))),
    sq_nonneg (C.eval (Real.sin (θ / 2))),
    sq_nonneg (D.eval (Real.sin (θ / 2)))]

/-- Odd `L`, Eq. (7): `D² ≤ 1`. -/
theorem norm_odd_D_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 1) (h : NormOK L A B C D) (θ : ℝ) :
    (D.eval (Real.sin (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_left hL] at hθ
  nlinarith [sq_nonneg (A.eval (Real.cos (θ / 2))),
    sq_nonneg (B.eval (Real.cos (θ / 2))),
    sq_nonneg (C.eval (Real.sin (θ / 2)))]

/-- Even `L`, Eq. (7): `B² ≤ 1`. -/
theorem norm_even_B_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 0) (h : NormOK L A B C D) (θ : ℝ) :
    (B.eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_right (by rw [hL]; norm_num)] at hθ
  nlinarith [sq_nonneg (A.eval (Real.cos (θ / 2))),
    mul_nonneg (sq_nonneg (Real.cos (θ / 2)))
      (sq_nonneg (C.eval (Real.sin (θ / 2)))),
    mul_nonneg (sq_nonneg (Real.cos (θ / 2)))
      (sq_nonneg (D.eval (Real.sin (θ / 2))))]

/-- Even `L`, Eq. (7): `x² D² ≤ 1`. -/
theorem norm_even_x_sq_mul_D_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 0) (h : NormOK L A B C D) (θ : ℝ) :
    (Real.cos (θ / 2)) ^ 2 * (D.eval (Real.sin (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_right (by rw [hL]; norm_num)] at hθ
  nlinarith [sq_nonneg (A.eval (Real.cos (θ / 2))),
    sq_nonneg (B.eval (Real.cos (θ / 2))),
    mul_nonneg (sq_nonneg (Real.cos (θ / 2)))
      (sq_nonneg (C.eval (Real.sin (θ / 2))))]

/-- Odd `L`, Eq. (7): `B² + C² ≤ 1`. -/
theorem norm_odd_B_sq_add_C_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 1) (h : NormOK L A B C D) (θ : ℝ) :
    (B.eval (Real.cos (θ / 2))) ^ 2 + (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_left hL] at hθ
  nlinarith [sq_nonneg (A.eval (Real.cos (θ / 2))),
    sq_nonneg (D.eval (Real.sin (θ / 2)))]

/-- Even `L`, Eq. (7): `A² + x² C² ≤ 1`. -/
theorem norm_even_A_sq_add_x_sq_mul_C_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 0) (h : NormOK L A B C D) (θ : ℝ) :
    (A.eval (Real.cos (θ / 2))) ^ 2
      + (Real.cos (θ / 2)) ^ 2 * (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_right (by rw [hL]; norm_num)] at hθ
  nlinarith [sq_nonneg (B.eval (Real.cos (θ / 2))),
    mul_nonneg (sq_nonneg (Real.cos (θ / 2)))
      (sq_nonneg (D.eval (Real.sin (θ / 2))))]

/-- Even `L`, Eq. (7): `B² + x² C² ≤ 1`. -/
theorem norm_even_B_sq_add_x_sq_mul_C_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (hL : L % 2 = 0) (h : NormOK L A B C D) (θ : ℝ) :
    (B.eval (Real.cos (θ / 2))) ^ 2
      + (Real.cos (θ / 2)) ^ 2 * (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  rw [ite_eq_right (by rw [hL]; norm_num)] at hθ
  nlinarith [sq_nonneg (A.eval (Real.cos (θ / 2))),
    mul_nonneg (sq_nonneg (Real.cos (θ / 2)))
      (sq_nonneg (D.eval (Real.sin (θ / 2))))]

/-- Both parities, Eq. (7): `A² + B² ≤ 1`. -/
theorem norm_A_sq_add_B_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (h : NormOK L A B C D) (θ : ℝ) :
    (A.eval (Real.cos (θ / 2))) ^ 2 + (B.eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
  have hθ := h θ
  by_cases hL : L % 2 = 1
  · rw [ite_eq_left hL] at hθ
    nlinarith [sq_nonneg (C.eval (Real.sin (θ / 2))),
      sq_nonneg (D.eval (Real.sin (θ / 2)))]
  · rw [ite_eq_right hL] at hθ
    nlinarith [mul_nonneg (sq_nonneg (Real.cos (θ / 2)))
        (sq_nonneg (C.eval (Real.sin (θ / 2)))),
      mul_nonneg (sq_nonneg (Real.cos (θ / 2)))
        (sq_nonneg (D.eval (Real.sin (θ / 2))))]

/-- Both parities, Eq. (7): `C² + D² ≤ 1` (odd `L`) or `x²C² + x²D² ≤ 1`
(even `L`). -/
theorem norm_C_D_bound {L : ℕ} {A B C D : Polynomial ℝ}
    (h : NormOK L A B C D) :
    (if L % 2 = 1 then
      ∀ θ : ℝ, (C.eval (Real.sin (θ / 2))) ^ 2
        + (D.eval (Real.sin (θ / 2))) ^ 2 ≤ 1
    else
      ∀ θ : ℝ, (Real.cos (θ / 2)) ^ 2 * (C.eval (Real.sin (θ / 2))) ^ 2
        + (Real.cos (θ / 2)) ^ 2 * (D.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) := by
  by_cases hL : L % 2 = 1
  · rw [ite_eq_left hL]
    intro θ
    have hθ := h θ
    rw [ite_eq_left hL] at hθ
    nlinarith [sq_nonneg (A.eval (Real.cos (θ / 2))),
      sq_nonneg (B.eval (Real.cos (θ / 2)))]
  · rw [ite_eq_right hL]
    intro θ
    have hθ := h θ
    rw [ite_eq_right hL] at hθ
    nlinarith [sq_nonneg (A.eval (Real.cos (θ / 2))),
      sq_nonneg (B.eval (Real.cos (θ / 2)))]

/-- Both parities, Eq. (7): `A² ≤ 1`. -/
theorem norm_A_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (h : NormOK L A B C D) (θ : ℝ) :
    (A.eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
  by_cases hL : L % 2 = 1
  · exact norm_odd_A_sq_le_one hL h θ
  · have hL0 : L % 2 = 0 := by omega
    exact norm_even_A_sq_le_one hL0 h θ

/-- Both parities, Eq. (7): `B² ≤ 1`. -/
theorem norm_B_sq_le_one {L : ℕ} {A B C D : Polynomial ℝ}
    (h : NormOK L A B C D) (θ : ℝ) :
    (B.eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
  by_cases hL : L % 2 = 1
  · exact norm_odd_B_sq_le_one hL h θ
  · have hL0 : L % 2 = 0 := by omega
    exact norm_even_B_sq_le_one hL0 h θ

/-- Both parities: `C² ≤ 1` (odd `L`) or `x²C² ≤ 1` (even `L`). -/
theorem norm_C_bound {L : ℕ} {A B C D : Polynomial ℝ}
    (h : NormOK L A B C D) :
    (if L % 2 = 1 then
      ∀ θ : ℝ, (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1
    else
      ∀ θ : ℝ, (Real.cos (θ / 2)) ^ 2
        * (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) := by
  by_cases hL : L % 2 = 1
  · rw [ite_eq_left hL]
    intro θ
    exact norm_odd_C_sq_le_one hL h θ
  · rw [ite_eq_right hL]
    intro θ
    have hL0 : L % 2 = 0 := by omega
    exact norm_even_x_sq_mul_C_sq_le_one hL0 h θ

/-- Both parities: `D² ≤ 1` (odd `L`) or `x²D² ≤ 1` (even `L`). -/
theorem norm_D_bound {L : ℕ} {A B C D : Polynomial ℝ}
    (h : NormOK L A B C D) :
    (if L % 2 = 1 then
      ∀ θ : ℝ, (D.eval (Real.sin (θ / 2))) ^ 2 ≤ 1
    else
      ∀ θ : ℝ, (Real.cos (θ / 2)) ^ 2
        * (D.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) := by
  by_cases hL : L % 2 = 1
  · rw [ite_eq_left hL]
    intro θ
    exact norm_odd_D_sq_le_one hL h θ
  · rw [ite_eq_right hL]
    intro θ
    have hL0 : L % 2 = 0 := by omega
    exact norm_even_x_sq_mul_D_sq_le_one hL0 h θ

/-- Both parities: `A²+C² ≤ 1` (odd `L`) or `A²+x²C² ≤ 1` (even `L`). -/
theorem norm_A_C_bound {L : ℕ} {A B C D : Polynomial ℝ}
    (h : NormOK L A B C D) :
    (if L % 2 = 1 then
      ∀ θ : ℝ, (A.eval (Real.cos (θ / 2))) ^ 2
        + (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1
    else
      ∀ θ : ℝ, (A.eval (Real.cos (θ / 2))) ^ 2
        + (Real.cos (θ / 2)) ^ 2 * (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) := by
  by_cases hL : L % 2 = 1
  · rw [ite_eq_left hL]
    intro θ
    exact norm_odd_A_sq_add_C_sq_le_one hL h θ
  · rw [ite_eq_right hL]
    intro θ
    have hL0 : L % 2 = 0 := by omega
    exact norm_even_A_sq_add_x_sq_mul_C_sq_le_one hL0 h θ

/-- Both parities: `B²+C² ≤ 1` (odd `L`) or `B²+x²C² ≤ 1` (even `L`). -/
theorem norm_B_C_bound {L : ℕ} {A B C D : Polynomial ℝ}
    (h : NormOK L A B C D) :
    (if L % 2 = 1 then
      ∀ θ : ℝ, (B.eval (Real.cos (θ / 2))) ^ 2
        + (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1
    else
      ∀ θ : ℝ, (B.eval (Real.cos (θ / 2))) ^ 2
        + (Real.cos (θ / 2)) ^ 2 * (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) := by
  by_cases hL : L % 2 = 1
  · rw [ite_eq_left hL]
    intro θ
    exact norm_odd_B_sq_add_C_sq_le_one hL h θ
  · rw [ite_eq_right hL]
    intro θ
    have hL0 : L % 2 = 0 := by omega
    exact norm_even_B_sq_add_x_sq_mul_C_sq_le_one hL0 h θ

/-- **Theorem 2, condition (1a), forward direction.**  Achievable `(A,·,C,·)`
satisfies the stated `A,C` bound. -/
theorem achievableAC_bound {L : ℕ} {A C : Polynomial ℝ}
    (h : AchievableAC L A C) :
    (if L % 2 = 1 then
      ∀ θ : ℝ, (A.eval (Real.cos (θ / 2))) ^ 2
        + (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1
    else
      ∀ θ : ℝ, (A.eval (Real.cos (θ / 2))) ^ 2
        + (Real.cos (θ / 2)) ^ 2 * (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) := by
  obtain ⟨B, D, h⟩ := h
  exact norm_A_C_bound (achievable_norm h)

/-- **Theorem 2, condition (2a), forward direction.**  Achievable `(·,B,C,·)`
satisfies the stated `B,C` bound. -/
theorem achievableBC_bound {L : ℕ} {B C : Polynomial ℝ}
    (h : AchievableBC L B C) :
    (if L % 2 = 1 then
      ∀ θ : ℝ, (B.eval (Real.cos (θ / 2))) ^ 2
        + (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1
    else
      ∀ θ : ℝ, (B.eval (Real.cos (θ / 2))) ^ 2
        + (Real.cos (θ / 2)) ^ 2 * (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) := by
  obtain ⟨A, D, h⟩ := h
  exact norm_B_C_bound (achievable_norm h)

/-- **Theorem 2, condition (3a), forward direction.**  Achievable `(A,B,·,·)`
satisfies `A²+B² ≤ 1`. -/
theorem achievableAB_upper {L : ℕ} {A B : Polynomial ℝ}
    (h : AchievableAB L A B) :
    ∀ θ : ℝ, (A.eval (Real.cos (θ / 2))) ^ 2
      + (B.eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
  obtain ⟨C, D, h⟩ := h
  exact norm_A_sq_add_B_sq_le_one (achievable_norm h)

/-- **Theorem 2, condition (4a), forward direction.**  Achievable `(·,·,C,D)`
satisfies the stated `C,D` bound. -/
theorem achievableCD_upper {L : ℕ} {C D : Polynomial ℝ}
    (h : AchievableCD L C D) :
    (if L % 2 = 1 then
      ∀ θ : ℝ, (C.eval (Real.sin (θ / 2))) ^ 2
        + (D.eval (Real.sin (θ / 2))) ^ 2 ≤ 1
    else
      ∀ θ : ℝ, (Real.cos (θ / 2)) ^ 2 * (C.eval (Real.sin (θ / 2))) ^ 2
        + (Real.cos (θ / 2)) ^ 2 * (D.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) := by
  obtain ⟨A, B, h⟩ := h
  exact norm_C_D_bound (achievable_norm h)

/-- **Theorem 3, condition (1), forward direction.**  Achievable `(A,·,·,·)`
satisfies `A² ≤ 1`. -/
theorem achievableA_bound {L : ℕ} {A : Polynomial ℝ}
    (h : AchievableA L A) :
    ∀ θ : ℝ, (A.eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
  obtain ⟨B, C, D, h⟩ := h
  exact norm_A_sq_le_one (achievable_norm h)

/-- **Theorem 3, condition (2), forward direction.**  Achievable `(·,B,·,·)`
satisfies `B² ≤ 1`. -/
theorem achievableB_bound {L : ℕ} {B : Polynomial ℝ}
    (h : AchievableB L B) :
    ∀ θ : ℝ, (B.eval (Real.cos (θ / 2))) ^ 2 ≤ 1 := by
  obtain ⟨A, C, D, h⟩ := h
  exact norm_B_sq_le_one (achievable_norm h)

/-- **Theorem 3, condition (3), forward direction.**  Achievable `(·,·,C,·)`
satisfies the stated `C` bound. -/
theorem achievableC_bound {L : ℕ} {C : Polynomial ℝ}
    (h : AchievableC L C) :
    (if L % 2 = 1 then
      ∀ θ : ℝ, (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1
    else
      ∀ θ : ℝ, (Real.cos (θ / 2)) ^ 2
        * (C.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) := by
  obtain ⟨A, B, D, h⟩ := h
  exact norm_C_bound (achievable_norm h)

/-- **Theorem 3, condition (4), forward direction.**  Achievable `(·,·,·,D)`
satisfies the stated `D` bound. -/
theorem achievableD_bound {L : ℕ} {D : Polynomial ℝ}
    (h : AchievableD L D) :
    (if L % 2 = 1 then
      ∀ θ : ℝ, (D.eval (Real.sin (θ / 2))) ^ 2 ≤ 1
    else
      ∀ θ : ℝ, (Real.cos (θ / 2)) ^ 2
        * (D.eval (Real.sin (θ / 2))) ^ 2 ≤ 1) := by
  obtain ⟨A, B, C, h⟩ := h
  exact norm_D_bound (achievable_norm h)


end Qatlib.Papers.ResonantGates16.MainResults.AchievableTuples
