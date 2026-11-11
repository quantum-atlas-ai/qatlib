/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation
import Qatlib.Foundations.MatrixGeometry.AxisRotations.SphericalAngles

/-!
# Majorana pair rotations

This module defines the trigonometric Majorana rotation and derives its adjoint and conjugation
action from the Clifford relations. It also records the involution, anticommutation, and
Hermitian properties of the concrete finite Majorana matrices. See [VonBurgEtAl2021].

## Main statements

* `rotation_conj_self`: Conjugation by a Majorana pair rotation sends its first generator to the
  cosine-sine combination with angle `2 * θ`.
* `rotation_conj_next`: Conjugation by a Majorana pair rotation sends its second generator to
  `cos (2 * θ) • γ q - sin (2 * θ) • γ p`.
* `frozen_majorana_herm`: Every concrete finite Majorana matrix is Hermitian.

## References

* [von Burg et al., 2021][VonBurgEtAl2021]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Matrix
open scoped BigOperators Classical
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion
open Qatlib.Foundations.MatrixGeometry.AxisRotations.SphericalAngles

namespace Qatlib.Papers.QCatalysis20.MainResults

variable {N : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

/-- The matrix `cos θ • 1 + sin θ • (γ p * γ q)` associated with a pair of Majorana indices. -/
def majoranaRotation (γ : Fin N → Matrix H H ℂ) (p q : Fin N) (θ : ℝ) :
    Matrix H H ℂ :=
  (Real.cos θ : ℂ) • (1 : Matrix H H ℂ) +
    (Real.sin θ : ℂ) • (γ p * γ q)

/-- The product of two distinct anticommuting involutions squares to minus the identity. -/
theorem pairGenerator_sq (γ : Fin N → Matrix H H ℂ)
    (hsq : ∀ p, γ p * γ p = 1)
    (hanti : ∀ p q, p ≠ q → γ p * γ q = -(γ q * γ p)) (p q : Fin N) (hpq : p≠q) :
    (γ p * γ q) * (γ p * γ q) = -(1 : Matrix H H ℂ) := by
  have hqp : γ q * γ p = -(γ p * γ q) :=
    hanti q p hpq.symm
  calc
    (γ p * γ q) * (γ p * γ q)
        = γ p * ((γ q * γ p) * γ q) := by noncomm_ring
    _ = γ p * ((-(γ p * γ q)) * γ q) := by rw [hqp]
    _ = -((γ p * γ p) * (γ q * γ q)) := by noncomm_ring
    _ = -(1 : Matrix H H ℂ) := by rw [hsq p, hsq (q), mul_one]

/-- For distinct Hermitian anticommuting generators, the adjoint rotation reverses the sign of
its sine term. -/
theorem majoranaRotation_adjoint (γ : Fin N → Matrix H H ℂ)
    (hherm : ∀ p, (γ p)ᴴ = γ p)
    (hanti : ∀ p q, p ≠ q → γ p * γ q = -(γ q * γ p)) (p q : Fin N) (hpq : p≠q) (θ : ℝ) :
    (majoranaRotation γ p q θ)ᴴ =
      (Real.cos θ : ℂ) • (1 : Matrix H H ℂ) -
        (Real.sin θ : ℂ) • (γ p * γ q) := by
  have hqp : γ q * γ p = -(γ p * γ q) :=
    hanti q p hpq.symm
  have hJ : (γ p * γ q)ᴴ = -(γ p * γ q) := by
    rw [Matrix.conjTranspose_mul, hherm, hherm, hqp]
  unfold majoranaRotation
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, hJ]
  simp only [Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, smul_neg,
    sub_eq_add_neg]

/-- Expand the product of the two linear factors `c • 1 ± s • J` around an arbitrary matrix. -/
theorem rotation_conj_expand (J C : Matrix H H ℂ) (c s : ℂ) :
    (c • (1 : Matrix H H ℂ) - s • J) * C * (c • (1 : Matrix H H ℂ) + s • J) =
      (c * c) • C + (c * s) • (C * J) - (s * c) • (J * C) - (s * s) • (J * C * J) := by
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_sub, smul_smul]
  module

/-- Conjugation by a Majorana pair rotation sends its first generator to the cosine-sine
combination with angle `2 * θ`. -/
theorem rotation_conj_self (γ : Fin N → Matrix H H ℂ)
    (hsq : ∀ p, γ p * γ p = 1)
    (hanti : ∀ p q, p ≠ q → γ p * γ q = -(γ q * γ p))
    (hherm : ∀ p, (γ p)ᴴ = γ p) (p q : Fin N) (hpq : p≠q) (θ : ℝ) :
    (majoranaRotation γ p q θ)ᴴ * γ p * majoranaRotation γ p q θ =
      (Real.cos (2 * θ) : ℂ) • γ p + (Real.sin (2 * θ) : ℂ) • γ q := by
  have hJadj := majoranaRotation_adjoint γ hherm hanti p q hpq θ
  have hqp : γ q * γ p = -(γ p * γ q) :=
    hanti q p hpq.symm
  have hCJ : γ p * (γ p * γ q) = γ q := by
    rw [← mul_assoc, hsq p, one_mul]
  have hJC : (γ p * γ q) * γ p = -(γ q) := by
    rw [mul_assoc, hqp, mul_neg, ← mul_assoc, hsq p, one_mul]
  have hqCq : γ q * (γ p * γ q) = -γ p := by
    rw [← mul_assoc, hqp, neg_mul, mul_assoc, hsq (q), mul_one]
  have hJCJ : (γ p * γ q) * γ p * (γ p * γ q) = γ p := by
    calc
      (γ p * γ q) * γ p * (γ p * γ q)
          = (-(γ q)) * (γ p * γ q) := by rw [hJC]
      _ = -(γ q * (γ p * γ q)) := by rw [neg_mul]
      _ = -(-γ p) := by rw [hqCq]
      _ = γ p := neg_neg _
  rw [hJadj, majoranaRotation, rotation_conj_expand, hCJ, hJCJ, hJC]
  rw [show (2 * θ : ℝ) = θ + θ by ring, Real.cos_add, Real.sin_add]
  push_cast
  simp only [smul_neg]
  module

/-- Conjugation by a Majorana pair rotation sends its second generator to `cos (2 * θ) • γ q -
sin (2 * θ) • γ p`. -/
theorem rotation_conj_next (γ : Fin N → Matrix H H ℂ)
    (hsq : ∀ p, γ p * γ p = 1)
    (hanti : ∀ p q, p ≠ q → γ p * γ q = -(γ q * γ p))
    (hherm : ∀ p, (γ p)ᴴ = γ p) (p q : Fin N) (hpq : p≠q) (θ : ℝ) :
    (majoranaRotation γ p q θ)ᴴ * γ q * majoranaRotation γ p q θ =
      (Real.cos (2 * θ) : ℂ) • γ q - (Real.sin (2 * θ) : ℂ) • γ p := by
  have hJadj := majoranaRotation_adjoint γ hherm hanti p q hpq θ
  have hqp : γ q * γ p = -(γ p * γ q) :=
    hanti q p hpq.symm
  have hCJ : γ q * (γ p * γ q) = -γ p := by
    rw [← mul_assoc, hqp, neg_mul, mul_assoc, hsq (q), mul_one]
  have hJC : (γ p * γ q) * γ q = γ p := by
    rw [mul_assoc, hsq (q), mul_one]
  have hJCJ : (γ p * γ q) * γ q * (γ p * γ q) = γ q := by
    calc
      (γ p * γ q) * γ q * (γ p * γ q)
          = γ p * (γ p * γ q) := by rw [hJC]
      _ = γ q := by rw [← mul_assoc, hsq p, one_mul]
  rw [hJadj, majoranaRotation, rotation_conj_expand, hCJ, hJCJ, hJC]
  rw [show (2 * θ : ℝ) = θ + θ by ring, Real.cos_add, Real.sin_add]
  push_cast
  simp only [smul_neg]
  module

/-- Conjugation by a Majorana pair rotation fixes each generator with an index distinct from
both rotated indices. -/
theorem rotation_conj_other (γ : Fin N → Matrix H H ℂ)
    (hsq : ∀ p, γ p * γ p = 1)
    (hanti : ∀ p q, p ≠ q → γ p * γ q = -(γ q * γ p))
    (hherm : ∀ p, (γ p)ᴴ = γ p) (p q r : Fin N) (hpq : p≠q) (θ : ℝ)
    (hrp : r ≠ p) (hrq : r ≠ q) :
    (majoranaRotation γ p q θ)ᴴ * γ r * majoranaRotation γ p q θ = γ r := by
  have hJadj := majoranaRotation_adjoint γ hherm hanti p q hpq θ
  have hJsq := pairGenerator_sq γ hsq hanti p q hpq
  have hJlp : γ r * (γ p * γ q) = (γ p * γ q) * γ r := by
    have hrp' : γ r * γ p = -(γ p * γ r) := hanti r p hrp
    have hrq' : γ r * γ q = -(γ q * γ r) := hanti r (q) hrq
    calc
      γ r * (γ p * γ q) = (γ r * γ p) * γ q := by noncomm_ring
      _ = (-(γ p * γ r)) * γ q := by rw [hrp']
      _ = -(γ p * (γ r * γ q)) := by noncomm_ring
      _ = -(γ p * (-(γ q * γ r))) := by rw [hrq']
      _ = (γ p * γ q) * γ r := by noncomm_ring
  have hJC : (γ p * γ q) * γ r = γ r * (γ p * γ q) := hJlp.symm
  have hJCJ : (γ p * γ q) * γ r * (γ p * γ q) = -γ r := by
    calc
      (γ p * γ q) * γ r * (γ p * γ q)
          = γ r * ((γ p * γ q) * (γ p * γ q)) := by
            rw [← hJlp, mul_assoc]
      _ = γ r * (-(1 : Matrix H H ℂ)) := by rw [hJsq]
      _ = -γ r := by rw [mul_neg, mul_one]
  have htrig : (Real.cos θ : ℂ) * Real.cos θ + (Real.sin θ : ℂ) * Real.sin θ = 1 := by
    have h := Real.cos_sq_add_sin_sq θ
    rw [pow_two, pow_two] at h
    exact_mod_cast h
  rw [hJadj, majoranaRotation, rotation_conj_expand, hJCJ, hJC]
  simp only [smul_neg]
  conv_rhs => rw [← one_smul ℂ (γ r), ← htrig]
  module

/-- Each concrete finite Majorana matrix squares to the identity. -/
theorem frozen_majorana_sq {n : ℕ} (a : Fin (2 * n)) :
    majorana a * majorana a = 1 :=
  Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation.majorana_sq a

/-- Concrete finite Majorana matrices with distinct indices anticommute. -/
theorem frozen_majorana_anticommute {n : ℕ} (a b : Fin (2 * n)) (h : a ≠ b) :
    majorana a * majorana b = -(majorana b * majorana a) :=
  Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation.majorana_anticommute a b h

/-- Each concrete even Majorana matrix is Hermitian. -/
theorem frozen_majoranaEven_herm {n : ℕ} (k : Fin n) :
    (majoranaEven k)ᴴ = majoranaEven k := by
  have h1 : (creation k)ᴴ = annihilation k := by
    rw [creation_eq_annihilation_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have h2 : (annihilation k)ᴴ = creation k := by
    rw [annihilation_eq_creation_conjTranspose, Matrix.conjTranspose_conjTranspose]
  unfold majoranaEven
  rw [Matrix.conjTranspose_add, h1, h2, add_comm]

/-- Each concrete odd Majorana matrix is Hermitian. -/
theorem frozen_majoranaOdd_herm {n : ℕ} (k : Fin n) :
    (majoranaOdd k)ᴴ = majoranaOdd k := by
  have h1 : (creation k)ᴴ = annihilation k := by
    rw [creation_eq_annihilation_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have h2 : (annihilation k)ᴴ = creation k := by
    rw [annihilation_eq_creation_conjTranspose, Matrix.conjTranspose_conjTranspose]
  unfold majoranaOdd
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.conjTranspose_sub,
    h1, h2,
    show (creation k - annihilation k) = -(annihilation k - creation k) by abel,
    smul_neg]
  module

/-- Every concrete finite Majorana matrix is Hermitian. -/
theorem frozen_majorana_herm {n : ℕ} (a : Fin (2 * n)) :
    (majorana a)ᴴ = majorana a := by
  have hk : a.val / 2 < n := by omega
  have hA : majorana a =
      if a.val % 2 = 0 then majoranaEven ⟨a.val / 2, hk⟩
      else majoranaOdd ⟨a.val / 2, hk⟩ := by
    by_cases h : a.val % 2 = 0
    · simp [majorana, majoranaEven, h]
    · simp [majorana, majoranaOdd, h]
  rw [hA]
  split_ifs
  · exact frozen_majoranaEven_herm _
  · exact frozen_majoranaOdd_herm _

end Qatlib.Papers.QCatalysis20.MainResults
