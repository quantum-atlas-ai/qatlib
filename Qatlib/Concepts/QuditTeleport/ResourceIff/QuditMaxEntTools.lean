/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux

/-!
# Orthonormal families and maximally mixed marginals

This module supplies matrix identities for orthonormal families and the normalization factors
used in maximally entangled qudit vectors. `quditFamilyColumns` turns a family into a square
matrix, allowing Gram and completeness identities to control partial traces.

`qudit_maxEnt_first_marginal` and `qudit_scaled_rows_orthonormal` provide the two directions
needed for the resource characterization in [BennettEtAl1993Teleportation].

## Main statements

* `quditFamily_complete`: resolution of the identity by an orthonormal family.
* `qudit_maxEnt_first_marginal`: the first reduced operator of the maximally entangled form.
* `qudit_scaled_rows_orthonormal`: extracts an orthonormal family from a maximally mixed
  marginal.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators
set_option linter.unusedSimpArgs false

/-- The square matrix whose columns are the vectors of the indexed family `u`. -/
noncomputable def quditFamilyColumns {n : ℕ} (u : Fin n → QState (Fin n)) : Operator n :=
  fun i j => u j i

/-- The column matrix of an orthonormal family has Gram matrix equal to the identity. -/
theorem quditFamily_gram {n : ℕ} {u : Fin n → QState (Fin n)}
    (hu : QuditOrthonormalFamily n u) :
    (quditFamilyColumns u)ᴴ * quditFamilyColumns u = 1 := by
  ext i j
  exact hu i j

/-- A full orthonormal family resolves the identity through the sum of its outer product
entries. -/
theorem quditFamily_complete {n : ℕ} {u : Fin n → QState (Fin n)}
    (hu : QuditOrthonormalFamily n u) (i j : Fin n) :
    ∑ a, u a i * star (u a j) = (1 : Operator n) i j := by
  have hU : quditFamilyColumns u ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact quditFamily_gram hu
  have h := Matrix.mem_unitaryGroup_iff.mp hU
  rw [Matrix.star_eq_conjTranspose] at h
  exact congrArg (fun A : Operator n => A i j) h

/-- The square of the complex embedding of `Real.sqrt n` is the complex embedding of `n`. -/
theorem qudit_sqrt_sq (n : ℕ) : (Real.sqrt (n : ℝ) : ℂ)^2 = (n : ℂ) := by
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

/-- The complex embedding of `Real.sqrt n` is nonzero when `n` is nonzero. -/
theorem qudit_sqrt_ne_zero (n : ℕ) [NeZero n] : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  intro hz
  have h := qudit_sqrt_sq n
  rw [hz, zero_pow (by decide : 2 ≠ 0)] at h
  exact hn h.symm

/-- The product of two inverse square root dimension factors equals `1 / n` in the complex
numbers. -/
theorem qudit_sqrt_inv_sq (n : ℕ) :
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹ = 1 / (n : ℂ) := by
  rw [← mul_inv, ← pow_two, qudit_sqrt_sq, one_div]

/-- The first marginal of a maximally entangled resource formed from two orthonormal families is
`1 / n` times the identity. -/
theorem qudit_maxEnt_first_marginal {n : ℕ}
    {u v : Fin n → QState (Fin n)}
    (hu : QuditOrthonormalFamily n u) (hv : QuditOrthonormalFamily n v) :
    PartialTrace (outerProduct (quditMaxEntResource n u v)) =
      (1 / (n : ℂ)) • (1 : Operator n) := by
  have hv' : ∀ a b, Inner (v a) (v b) = if a = b then 1 else 0 := hv
  ext i j
  let s : ℂ := (Real.sqrt (n : ℝ) : ℂ)⁻¹
  have hs : star s = s := by simp [s]
  calc
    _ = (s * s) * ∑ a, ∑ b,
        (u a i * star (u b j)) * Inner (v b) (v a) := by
      have hterm (k : Fin n) :
          quditMaxEntResource n u v (i,k) * star (quditMaxEntResource n u v (j,k)) =
          (s*s) * ∑ a, ∑ b, (u a i * star (u b j)) * (star (v b k) * v a k) := by
        simp only [quditMaxEntResource, Complex.star_def, map_mul, map_sum, s,
          map_inv₀, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      simp only [PartialTrace, outerProduct_apply, ← Complex.star_def, hterm,
        ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [inner_apply, Complex.star_def, Finset.mul_sum]
    _ = (s * s) * ∑ a, u a i * star (u a j) := by
      simp only [hv', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = _ := by
      rw [quditFamily_complete hu]
      change ((Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹) * _ = _
      rw [qudit_sqrt_inv_sq]; rfl

/-- If a pure vector has maximally mixed first marginal in nonzero dimension, its rows scaled by
`√n` form an orthonormal family. -/
theorem qudit_scaled_rows_orthonormal {n : ℕ} [NeZero n]
    (Ψ : QState (Fin n × Fin n))
    (h : PartialTrace (outerProduct Ψ) = (1 / (n : ℂ)) • (1 : Operator n)) :
    QuditOrthonormalFamily n (fun j k => (Real.sqrt (n : ℝ) : ℂ) * Ψ (j,k)) := by
  intro i j
  have he := congrArg (fun A : Operator n => A j i) h
  (try dsimp only at he)
  have hi : Inner (fun k => (Real.sqrt (n : ℝ) : ℂ) * Ψ (i,k))
      (fun k => (Real.sqrt (n : ℝ) : ℂ) * Ψ (j,k)) =
      (n : ℂ) * PartialTrace (outerProduct Ψ) j i := by
    simp only [inner_apply, map_mul, Complex.conj_ofReal,
      PartialTrace, outerProduct_apply]
    rw [← qudit_sqrt_sq]
    simp only [pow_two, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hi, he]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hn, eq_comm]

end Qatlib.Concepts.QuditTeleport.ResourceIff
