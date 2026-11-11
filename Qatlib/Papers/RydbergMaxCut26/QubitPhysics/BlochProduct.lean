/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubitCorrelation
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics

/-!
# Bloch matrices and product density operators

`bloch` constructs the trace-one Hermitian matrix associated with a real three-dimensional Bloch
vector. Its Gram decomposition proves positivity on the closed unit ball, and `productState`
tensors these matrices to obtain physical register density matrices from sitewise Bloch-ball
vectors.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `bloch_posSemidef` and `bloch_trace`: establish single-qubit physicality.
* `bloch_pauli_trace`: recovers each Bloch coordinate as a Pauli expectation.
* `product_density`: proves physicality of the tensor product.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch

/-- The sum of the squares of the three real coordinates of `v`. -/
def sqnorm (v : Fin 3 → ℝ) : ℝ := ∑ a, (v a)^2

/-- The one-qubit Bloch matrix `(I + v · σ)/2` associated with the real vector `v`. -/
noncomputable def bloch (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1+(v 2:ℂ))/2, ((v 0:ℂ)-Complex.I*(v 1:ℂ))/2;
     ((v 0:ℂ)+Complex.I*(v 1:ℂ))/2, (1-(v 2:ℂ))/2]

/-- The matrix `bloch v` equals one half of the sum of the identity and the coordinate-weighted
Pauli expansion. -/
theorem bloch_pauli (v : Fin 3 → ℝ) :
    bloch v = (1/2:ℂ) • (1+∑ a : Fin 3, (v a:ℂ) • pauliMatrix a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bloch,Fin.sum_univ_three,pauliMatrix,pauliX,pauliY,pauliZ] <;> ring

/-- The Bloch matrix of any real vector is Hermitian. -/
theorem bloch_hermitian (v : Fin 3 → ℝ) : (bloch v).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bloch,Matrix.conjTranspose_apply]
  ring

/-- The Bloch matrix equals its conjugate-transpose square plus `(1 - sqnorm v)/4` times the
identity. -/
theorem bloch_gram (v : Fin 3 → ℝ) :
    bloch v = (bloch v)ᴴ*bloch v + ((1-sqnorm v)/4:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [bloch_hermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bloch,sqnorm,Fin.sum_univ_three,
      Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_pow] <;>
    ring_nf <;> norm_num [Complex.I_sq]

/-- A Bloch vector of squared norm at most one defines a positive semidefinite Bloch matrix. -/
theorem bloch_posSemidef (v : Fin 3 → ℝ) (hv : sqnorm v ≤ 1) : (bloch v).PosSemidef := by
  rw [bloch_gram]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).add
      (Matrix.PosSemidef.one.smul (by linarith : 0≤(1-sqnorm v)/4))

/-- Every Bloch matrix has trace one. -/
theorem bloch_trace (v : Fin 3 → ℝ) : (bloch v).trace = 1 := by
  simp [bloch,Matrix.trace,Fin.sum_univ_two]
  ring

/-- A Bloch vector in the closed unit ball defines a density operator. -/
theorem bloch_density (v : Fin 3 → ℝ) (hv : sqnorm v ≤ 1) : IsDensityOperator (bloch v) :=
  ⟨bloch_posSemidef v hv,bloch_trace v⟩

/-- The trace of Pauli axis `a` against `bloch v` is the complex cast of the coordinate `v a`. -/
theorem bloch_pauli_trace (v : Fin 3 → ℝ) (a : Fin 3) :
    (pauliMatrix a*bloch v).trace = (v a:ℂ) := by
  fin_cases a <;> simp [pauliMatrix,pauliX,pauliY,pauliZ,bloch,Matrix.trace,Fin.sum_univ_two] <;> ring_nf
  norm_num [Complex.I_sq]

/-- The register matrix obtained by tensoring the sitewise Bloch matrices `bloch (v i)`. -/
noncomputable def productState {n : ℕ} (v : Fin n → Fin 3 → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  qubitTensor (fun i => bloch (v i))

/-- If every local Bloch vector has squared norm at most one, `productState v` is positive
semidefinite and has trace one. This establishes product-state feasibility for
[CrostaSaubanereHuber2026]. -/
theorem product_density {n : ℕ} (v : Fin n → Fin 3 → ℝ) (hv : ∀ i, sqnorm (v i) ≤ 1) :
    (productState v).PosSemidef ∧ (productState v).trace=1 :=
  qubitTensor_density _ (fun i => bloch_density (v i) (hv i))
end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
