/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QHamDescent23.MainResults.SourceModel
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# Subspace-Encoded Hamiltonian Evolution and Observable Expectations

This module proves Lemma 4 and Proposition 4 of Leng, Hickman, Li, and Wu on
subspace-encoded quantum simulation: when `V : ℂ^m → ℂ^n` is an isometry (`Vᴴ * V = 1`)
intertwining a simulator Hamiltonian `H` with a compressed target Hamiltonian `Ht`
via `H * V = V * Ht`, the target unitary evolution is the compression
`exp(-i t Ht) = Vᴴ * exp(-i t H) * V` and observable expectations on `exp(-i t H) V ψ_0`
match expectations of `Vᴴ O V` on `exp(-i t Ht) ψ_0`.

## Main statements

* `source_lemma4_subspace_encoding_evolution`: compressed unitary evolution identity
  `exp((-i t) • Ht) = Vᴴ * (exp((-i t) • H) * V)`.
* `source_proposition4_subspace_encoding_expectation`: equality of full-space and
  compressed-subspace observable expectations.

## References

* [Leng et al., 2023][LengEtAl2023QHD], Appendix F.2, Lemma 4 and Proposition 4,
  Eqs. (F.28)--(F.29), pp. 51--52.
-/

open scoped Matrix
open scoped Matrix.Norms.Operator
open NormedSpace

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QHamDescent23.MainResults.SubspaceEncoding

open Qatlib.Papers.QHamDescent23.MainResults

private theorem exp_mul_encoding
    {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) (H : Matrix (Fin n) (Fin n) ℂ)
    (Ht : Matrix (Fin m) (Fin m) ℂ) (hinv : H * V = V * Ht) (c : ℂ) :
    exp (c • H) * V = V * exp (c • Ht) := by
  have hscale : (c • H) * V = V * (c • Ht) := by
    rw [Matrix.smul_mul, hinv, Matrix.mul_smul]
  have hpow (k : ℕ) : (c • H) ^ k * V = V * (c • Ht) ^ k := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [pow_succ, Matrix.mul_assoc, hscale, ← Matrix.mul_assoc, hk,
        Matrix.mul_assoc, ← pow_succ]
  have hs := exp_series_hasSum_exp' (𝕂 := ℂ) (c • H)
  have hst := exp_series_hasSum_exp' (𝕂 := ℂ) (c • Ht)
  ext i j
  have hl : HasSum (fun k : ℕ => (((k.factorial : ℂ)⁻¹ • (c • H) ^ k) * V) i j)
      ((exp (c • H) * V) i j) := by
    simpa only [Matrix.mul_apply] using
      hasSum_sum (s := Finset.univ) (fun l _ =>
        (Pi.hasSum.mp (Pi.hasSum.mp hs i) l).mul_right (V l j))
  have hr : HasSum (fun k : ℕ => (V * ((k.factorial : ℂ)⁻¹ • (c • Ht) ^ k)) i j)
      ((V * exp (c • Ht)) i j) := by
    simpa only [Matrix.mul_apply] using
      hasSum_sum (s := Finset.univ) (fun l _ =>
        (Pi.hasSum.mp (Pi.hasSum.mp hst l) j).mul_left (V i l))
  apply hl.unique
  apply hr.congr_fun
  intro k
  rw [Matrix.smul_mul, hpow, Matrix.mul_smul]

private theorem bracket_encoding_left
    {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) (x : Ket (Fin m)) (y : Ket (Fin n)) :
    bracket (V *ᵥ x) y = bracket x (Vᴴ *ᵥ y) := by
  rw [bracket_eq_dotProduct, bracket_eq_dotProduct, Matrix.star_mulVec]
  exact (Matrix.dotProduct_mulVec (star x) Vᴴ y).symm

/-- **Lemma 4 (Eq. F.28)**: the compressed evolution satisfies `U_t = Vᴴ * (U * V)`,
where `H` is the simulator Hamiltonian, `Ht` its target compression, and `V` the
encoding isometry. -/
theorem source_lemma4_subspace_encoding_evolution
    {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) (H : Matrix (Fin n) (Fin n) ℂ)
    (Ht : Matrix (Fin m) (Fin m) ℂ) (hH : H.IsHermitian) (hHt : Ht.IsHermitian)
    (hiso : Vᴴ * V = 1) (hinv : H * V = V * Ht) (t : ℝ) :
    exp ((-(Complex.I * (t : ℂ))) • Ht)
      = Vᴴ * (exp ((-(Complex.I * (t : ℂ))) • H) * V) := by
  rw [← hH.eq, hH.eq, ← hHt.eq, hHt.eq]
  rw [exp_mul_encoding V H Ht hinv, ← Matrix.mul_assoc, hiso, Matrix.one_mul]

/-- **Proposition 4 (Eq. F.29)**: observable expectations agree between the full
evolution of `V ψ₀` and the compressed evolution of `ψ₀`, with the observable
compressed to `Vᴴ * (O * V)`. -/
theorem source_proposition4_subspace_encoding_expectation
    {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) (H : Matrix (Fin n) (Fin n) ℂ)
    (Ht : Matrix (Fin m) (Fin m) ℂ) (O : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hHt : Ht.IsHermitian)
    (hiso : Vᴴ * V = 1) (hinv : H * V = V * Ht)
    (ψ0 : Ket (Fin m)) (t : ℝ) (ht : 0 ≤ t) :
    let U : Matrix (Fin n) (Fin n) ℂ := exp ((-(Complex.I * (t : ℂ))) • H)
    let Ut : Matrix (Fin m) (Fin m) ℂ := exp ((-(Complex.I * (t : ℂ))) • Ht)
    let ψt : Ket (Fin n) := U *ᵥ (V *ᵥ ψ0)
    let ψt' : Ket (Fin m) := Ut *ᵥ ψ0
    bracket ψt (O *ᵥ ψt)
      = bracket ψt' ((Vᴴ * (O * V)) *ᵥ ψt') := by
  rw [← hH.eq, hH.eq, ← hHt.eq, hHt.eq]
  dsimp only
  rw [← Matrix.one_mul (exp ((-(Complex.I * (t : ℂ))) • Ht)), ← hiso,
    hiso, Matrix.one_mul]
  have heq (s : ℝ) :
      exp ((-(Complex.I * (s : ℂ))) • H) *ᵥ (V *ᵥ ψ0)
        = V *ᵥ (exp ((-(Complex.I * (s : ℂ))) • Ht) *ᵥ ψ0) := by
    rw [Matrix.mulVec_mulVec, exp_mul_encoding V H Ht hinv,
      ← Matrix.mulVec_mulVec]
  obtain _hpos | rfl := lt_or_eq_of_le ht <;>
    rw [heq, bracket_encoding_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]

end Qatlib.Papers.QHamDescent23.MainResults.SubspaceEncoding
