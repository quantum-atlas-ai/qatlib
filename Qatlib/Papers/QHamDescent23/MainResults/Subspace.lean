/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QHamDescent23.MainResults.SourceModel
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section


/-!
# Exponential intertwining for a rectangular encoding

The finite-dimensional content of Lemma 4 and Proposition 4 in
arXiv:2303.01471v1, Appendix F.3.1. Hermiticity and nonnegative evolution time
are unnecessary for the algebraic intertwining and expectation identities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix NormedSpace
open Qatlib.Papers.QHamDescent23.MainResults
open scoped Matrix.Norms.Operator

namespace Qatlib.Papers.QHamDescent23.MainResults.Subspace

/-- A rectangular intertwiner of two square matrices also intertwines their exponentials. -/
theorem exp_intertwine {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin m) ℂ)
    (h : A * V = V * B) : exp A * V = V * exp B := by
  let R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin m) ℂ :=
    { toFun := fun X => X * V
      map_add' := fun X Y => Matrix.add_mul X Y V
      map_smul' := fun c X => Matrix.smul_mul c X V }
  let L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin m) ℂ :=
    { toFun := fun X => V * X
      map_add' := fun X Y => Matrix.mul_add V X Y
      map_smul' := fun c X => Matrix.mul_smul V c X }
  have hp (k : ℕ) : A ^ k * V = V * B ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h,
        Matrix.mul_assoc, ← pow_succ']
  have hr := ((expSeries_summable' (𝕂 := ℂ) A).hasSum.map R.toAddMonoidHom
    R.continuous_of_finiteDimensional).tsum_eq
  have hl := ((expSeries_summable' (𝕂 := ℂ) B).hasSum.map L.toAddMonoidHom
    L.continuous_of_finiteDimensional).tsum_eq
  calc exp A * V = ∑' k : ℕ, R ((k.factorial : ℂ)⁻¹ • A ^ k) := by
        rw [exp_eq_tsum ℂ]
        exact hr.symm
    _ = ∑' k : ℕ, L ((k.factorial : ℂ)⁻¹ • B ^ k) := by
        apply tsum_congr
        intro k
        change ((k.factorial : ℂ)⁻¹ • A ^ k) * V = V * ((k.factorial : ℂ)⁻¹ • B ^ k)
        rw [Matrix.smul_mul, Matrix.mul_smul, hp]
    _ = V * exp B := by
        rw [exp_eq_tsum ℂ]
        exact hl

/-- Compression of the full exponential evolution recovers the encoded evolution. -/
theorem source_lemma4_subspace_encoding_evolution
    {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) (H : Matrix (Fin n) (Fin n) ℂ)
    (Ht : Matrix (Fin m) (Fin m) ℂ)
    (hiso : Vᴴ * V = 1) (hinv : H * V = V * Ht) (t : ℝ) :
    exp ((-(Complex.I * (t : ℂ))) • Ht)
      = Vᴴ * (exp ((-(Complex.I * (t : ℂ))) • H) * V) := by
  have hi : ((-(Complex.I * (t : ℂ))) • H) * V =
      V * ((-(Complex.I * (t : ℂ))) • Ht) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hinv]
  rw [exp_intertwine _ _ _ hi, ← Matrix.mul_assoc, hiso, Matrix.one_mul]

/-- Moving a rectangular encoding from the left slot of a bracket to the right
slot replaces it by its conjugate transpose. -/
lemma bracket_rect {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ)
    (x : Ket (Fin m)) (y : Ket (Fin n)) :
    bracket (V *ᵥ x) y = bracket x (Vᴴ *ᵥ y) := by
  rw [bracket_eq_dotProduct, bracket_eq_dotProduct, Matrix.star_mulVec]
  exact (Matrix.dotProduct_mulVec (star x) Vᴴ y).symm

/-- The expectation of an observable after full encoded evolution equals the
expectation of its compression after the smaller evolution. -/
theorem source_proposition4_subspace_encoding_expectation
    {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ) (H : Matrix (Fin n) (Fin n) ℂ)
    (Ht : Matrix (Fin m) (Fin m) ℂ) (O : Matrix (Fin n) (Fin n) ℂ)
    (hinv : H * V = V * Ht) (ψ0 : Ket (Fin m)) (t : ℝ) :
    let U : Matrix (Fin n) (Fin n) ℂ := exp ((-(Complex.I * (t : ℂ))) • H)
    let Ut : Matrix (Fin m) (Fin m) ℂ := exp ((-(Complex.I * (t : ℂ))) • Ht)
    let ψt : Ket (Fin n) := U *ᵥ (V *ᵥ ψ0)
    let ψt' : Ket (Fin m) := Ut *ᵥ ψ0
    bracket ψt (O *ᵥ ψt) = bracket ψt' ((Vᴴ * (O * V)) *ᵥ ψt') := by
  dsimp
  have hi : ((-(Complex.I * (t : ℂ))) • H) * V =
      V * ((-(Complex.I * (t : ℂ))) • Ht) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hinv]
  have he := exp_intertwine _ _ _ hi
  have hstate : exp ((-(Complex.I * (t : ℂ))) • H) *ᵥ (V *ᵥ ψ0) =
      V *ᵥ (exp ((-(Complex.I * (t : ℂ))) • Ht) *ᵥ ψ0) := by
    rw [Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec]
  rw [hstate, bracket_rect]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end Qatlib.Papers.QHamDescent23.MainResults.Subspace
