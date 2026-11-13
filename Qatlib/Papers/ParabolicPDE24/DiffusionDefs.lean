/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.MatrixGram

/-!
# Diffusion realization and drift substitution

The scaled transport coefficients realize positive semidefinite diffusion matrices through a
Gram factorization. Substitution of `slavedFlux` yields `correctedDrift`; a one-dimensional
calculation distinguishes this expression from the printed drift coefficient in [JinLiu2024].

## Main statements

* `realize_diffusion`: nonzero scales allow realization of any positive semidefinite diffusion
  matrix.
* `printed_drift_counterexample`: the corrected and printed drift expressions differ in an
  explicit example.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped BigOperators
namespace Qatlib.Papers.ParabolicPDE24.DiffusionDefs
open Qatlib.Foundations.MatrixAlgebra.MatrixGram
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The diffusion coefficient `∑ i, α i j * α i k * (ε i)^2 / (ε j * ε k)`. -/
def diffusion (α : Matrix I I ℝ) (ε : I→ℝ) (j k : I) : ℝ :=
  ∑ i,α i j*α i k*ε i^2/(ε j*ε k)

/-- The scaled transport matrix with entry `C i j * ε j / ε i`. -/
def transportCoefficients (C : Matrix I I ℝ) (ε : I→ℝ) : Matrix I I ℝ :=
  fun i j=>C i j*ε j/ε i

omit [DecidableEq I] in

/-- When all scales are nonzero, the diffusion matrix of `transportCoefficients C ε` equals the
Gram matrix `Cᵀ * C` entrywise. See [JinLiu2024]. -/
theorem diffusion_transport (C : Matrix I I ℝ) (ε : I→ℝ) (hε : ∀i,ε i≠0) (j k : I) :
    diffusion (transportCoefficients C ε) ε j k=(Cᵀ*C) j k := by
  simp only [diffusion,transportCoefficients,Matrix.mul_apply,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hε i,hε j,hε k]

/-- Every positive semidefinite real matrix can be realized by `diffusion α ε` when every scale
`ε i` is nonzero. See [JinLiu2024]. -/
theorem realize_diffusion (D : Matrix I I ℝ) (hD : D.PosSemidef)
    (ε : I→ℝ) (hε : ∀i,ε i≠0) :
    ∃ α : Matrix I I ℝ,∀j k,diffusion α ε j k=D j k := by
  refine ⟨transportCoefficients (gramFactor D hD) ε,?_⟩
  intro j k
  rw [diffusion_transport _ ε hε,gramFactor_identity]

/-- The slaved flux component `−∑ k, α i k * (ε i)^2 / ε k * grad k`. See [JinLiu2024]. -/
def slavedFlux (α : Matrix I I ℝ) (ε grad : I→ℝ) (i : I) : ℝ :=
  -∑ k,α i k*ε i^2/ε k*grad k

/-- The drift coefficient `−∑ i, δ i * α i k * ε i / ε k` obtained from the slaved-flux
substitution. -/
def correctedDrift (α : Matrix I I ℝ) (ε δ : I→ℝ) (k : I) : ℝ :=
  -∑ i,δ i*α i k*ε i/ε k

omit [DecidableEq I] in

/-- For nonzero scales, the weighted sum of slaved fluxes equals the gradient contracted with
`correctedDrift`. See [JinLiu2024]. -/
theorem drift_substitution (α : Matrix I I ℝ) (ε δ grad : I→ℝ) (hε : ∀i,ε i≠0) :
    (∑ i,δ i/ε i*slavedFlux α ε grad i)=∑ k,correctedDrift α ε δ k*grad k := by
  simp only [slavedFlux,correctedDrift,mul_neg,Finset.mul_sum,neg_mul,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hε i,hε k]

/-- With one coordinate, unit transport and drift parameters, and scale `1/10`, the corrected
drift equals `−1`, whereas the displayed inverse-square expression equals `−100`. See
[JinLiu2024]. -/
theorem printed_drift_counterexample :
    correctedDrift (fun _ _ : Fin 1=>(1:ℝ)) (fun _=>1/10) (fun _=>1) 0= -1 ∧
      (-(∑ _k : Fin 1,(1:ℝ)*1/((1/10:ℝ)^2)))= -100 := by
  norm_num [correctedDrift,Fin.sum_univ_one]
end Qatlib.Papers.ParabolicPDE24.DiffusionDefs
