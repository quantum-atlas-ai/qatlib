/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# TraceEstimation — the trace-power law of BettiNumber25, Lemma 3.2

Akhalwaya–Bhayat–Connolly–Herbert–Horesh–Sorci–Ubaru,
*Comparing quantum and classical Monte Carlo algorithms for estimating
Betti numbers of clique complexes*, fixed arXiv:2408.16934v3
(Quantum 9, 1901, 2025), PDF SHA-256
`dcf534a47e98fb6bb6bc34039e64bac6e7ba07fdb7d9b17f781dae1a01fe7848`.

Source Lemma 3.2 (p. 6): if `M` is Hermitian positive semidefinite, written
`M = D† D`, then for every positive integer `d`,
`tr(M^d) = ∑_x ‖D^(d) |x⟩‖²`, where `D^(d)` is `(D†D)^{d/2}` for `d` even and
`(DD†)^{(d-1)/2} D` for `d` odd.

The file works with `Matrix (Fin N) (Fin N) ℂ`; `⟨x| A |y⟩` is the matrix
entry `A x y` and the source column vector `D^(d) |x⟩` is the `x`-th column of
`D^(d)`.  Everything here is exact finite matrix algebra; no spectral
hypothesis beyond `D` itself is used.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.BettiNumber25.MainResults.TraceEstimation

variable {N : ℕ}

/-- `‖v‖²` for a column vector of `ℂ^N`, as a real number. -/
def vecNormSq (v : Fin N → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- The `x`-th column of `A`, i.e. the vector `A |x⟩`. -/
def colVec (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N) : Fin N → ℂ := fun y => A y x

/-- `∑_x ‖A |x⟩‖²`, the source's right-hand side before specialising `A`. -/
def colNormSqSum (A : Matrix (Fin N) (Fin N) ℂ) : ℝ := ∑ x, vecNormSq (colVec A x)

/-- Entrywise expansion of `trace (Aᴴ * A)` as `∑_x ∑_y conj(A y x) * A y x`. -/
theorem trace_conjTranspose_mul_self_eq_sum (A : Matrix (Fin N) (Fin N) ℂ) :
    (Aᴴ * A).trace = ∑ x, ∑ y, star (A y x) * A y x := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- **Column-norm form of the Frobenius identity**:
`tr(Aᴴ A) = ∑_x ‖A |x⟩‖²`.  This is the algebraic heart of source Lemma 3.2. -/
theorem trace_conjTranspose_mul_self_eq_colNormSqSum (A : Matrix (Fin N) (Fin N) ℂ) :
    ((Aᴴ * A).trace).re = colNormSqSum A := by
  rw [trace_conjTranspose_mul_self_eq_sum]
  have hcast : ∀ x, (∑ y, star (A y x) * A y x)
      = ((∑ y, ‖A y x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun y _ => by
      simpa using (RCLike.conj_mul (A y x))
  simp only [hcast]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]
  rfl

/-- `Dᴴ * (D * Dᴴ)^k = (Dᴴ * D)^k * Dᴴ` for every `k`. -/
theorem conjTranspose_mul_pow_mul (D : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    Dᴴ * (D * Dᴴ) ^ k = (Dᴴ * D) ^ k * Dᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      calc Dᴴ * ((D * Dᴴ) ^ k * (D * Dᴴ))
          = Dᴴ * (D * Dᴴ) ^ k * (D * Dᴴ) := by rw [Matrix.mul_assoc]
        _ = (Dᴴ * D) ^ k * Dᴴ * (D * Dᴴ) := by rw [ih]
        _ = (Dᴴ * D) ^ k * (Dᴴ * (D * Dᴴ)) := by rw [Matrix.mul_assoc]
        _ = (Dᴴ * D) ^ k * ((Dᴴ * D) * Dᴴ) := by
              rw [← Matrix.mul_assoc Dᴴ D Dᴴ]
        _ = (Dᴴ * D) ^ k * (Dᴴ * D) * Dᴴ := by rw [← Matrix.mul_assoc]

/-- `(D * Dᴴ)^k * D = D * (Dᴴ * D)^k` for every `k`. -/
theorem pow_mul_self (D : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    (D * Dᴴ) ^ k * D = D * (Dᴴ * D) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      calc (D * Dᴴ) ^ k * (D * Dᴴ) * D
          = (D * Dᴴ) ^ k * ((D * Dᴴ) * D) := by rw [Matrix.mul_assoc]
        _ = (D * Dᴴ) ^ k * (D * (Dᴴ * D)) := by rw [Matrix.mul_assoc D Dᴴ D]
        _ = ((D * Dᴴ) ^ k * D) * (Dᴴ * D) := by
              rw [← Matrix.mul_assoc ((D * Dᴴ) ^ k) D (Dᴴ * D)]
        _ = (D * (Dᴴ * D) ^ k) * (Dᴴ * D) := by rw [ih]
        _ = D * ((Dᴴ * D) ^ k * (Dᴴ * D)) := by rw [Matrix.mul_assoc]
        _ = D * ((Dᴴ * D) ^ (k + 1)) := by rw [← pow_succ]

/-- `Dᴴ * D` is Hermitian. -/
theorem isHermitian_conjTranspose_mul_self (D : Matrix (Fin N) (Fin N) ℂ) :
    (Dᴴ * D)ᴴ = Dᴴ * D := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Every power of the Hermitian matrix `Dᴴ * D` is Hermitian. -/
theorem conjTranspose_pow_conjTranspose_mul_self (D : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    ((Dᴴ * D) ^ k)ᴴ = (Dᴴ * D) ^ k := by
  rw [Matrix.conjTranspose_pow, isHermitian_conjTranspose_mul_self]

/-- `D * Dᴴ` is Hermitian. -/
theorem isHermitian_mul_conjTranspose (D : Matrix (Fin N) (Fin N) ℂ) :
    (D * Dᴴ)ᴴ = D * Dᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Every power of the Hermitian matrix `D * Dᴴ` is Hermitian. -/
theorem conjTranspose_pow_mul_conjTranspose_self (D : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    ((D * Dᴴ) ^ k)ᴴ = (D * Dᴴ) ^ k := by
  rw [Matrix.conjTranspose_pow, isHermitian_mul_conjTranspose]

/-- The source's auxiliary matrix `D^(d)`: `(D†D)^{d/2}` for even `d`,
`(DD†)^{(d-1)/2} D` for odd `d` (source Lemma 3.2). -/
def Dpow (D : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  if Even d then (Dᴴ * D) ^ (d / 2) else (D * Dᴴ) ^ ((d - 1) / 2) * D

/-- `(D^(d))ᴴ * D^(d) = (Dᴴ D)^d`, for every positive `d`. -/
theorem Dpow_conjTranspose_mul_self (D : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) (hd : 0 < d) :
    (Dpow D d)ᴴ * Dpow D d = (Dᴴ * D) ^ d := by
  unfold Dpow
  by_cases hEven : Even d
  · simp only [hEven, if_true]
    rw [conjTranspose_pow_conjTranspose_mul_self]
    rw [← pow_add]
    obtain ⟨m, hm⟩ := hEven
    subst hm
    congr 1
    omega
  · simp only [hEven, if_false]
    obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hEven
    subst hm
    have hdiv : (2 * m + 1 - 1) / 2 = m := by omega
    rw [hdiv]
    rw [Matrix.conjTranspose_mul, conjTranspose_pow_mul_conjTranspose_self]
    rw [conjTranspose_mul_pow_mul, pow_mul_self]
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Dᴴ D ((Dᴴ * D) ^ m)]
    rw [← pow_succ', ← pow_add]
    congr 1
    omega

/-- **Source Lemma 3.2.**  For a positive integer `d`, the real trace of `(DᴴD)^d`
equals `∑_x ‖D^(d) |x⟩‖²`. -/
theorem lemma_3_2_trace_pow_eq_sum (D : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) (hd : 0 < d) :
    (((Dᴴ * D) ^ d).trace).re = ∑ x, vecNormSq (colVec (Dpow D d) x) := by
  rw [← Dpow_conjTranspose_mul_self D d hd]
  exact trace_conjTranspose_mul_self_eq_colNormSqSum (Dpow D d)

/-- Reading of the same identity in ket notation: summing the squared norms of
the propagated computational basis columns gives the normalised trace. -/
theorem lemma_3_2_normalised (D : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) (hd : 0 < d)
    (_hN : 0 < N) :
    (∑ x, vecNormSq (colVec (Dpow D d) x)) / (N : ℝ)
      = (((Dᴴ * D) ^ d).trace).re / (N : ℝ) := by
  rw [lemma_3_2_trace_pow_eq_sum D d hd]

end Qatlib.Papers.BettiNumber25.MainResults.TraceEstimation
