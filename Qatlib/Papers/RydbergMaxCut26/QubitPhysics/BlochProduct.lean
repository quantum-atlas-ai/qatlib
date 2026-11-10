/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubitCorrelation
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics
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

def sqnorm (v : Fin 3 → ℝ) : ℝ := ∑ a, (v a)^2

noncomputable def bloch (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1+(v 2:ℂ))/2, ((v 0:ℂ)-Complex.I*(v 1:ℂ))/2;
     ((v 0:ℂ)+Complex.I*(v 1:ℂ))/2, (1-(v 2:ℂ))/2]

theorem bloch_pauli (v : Fin 3 → ℝ) :
    bloch v = (1/2:ℂ) • (1+∑ a : Fin 3, (v a:ℂ) • pauliMatrix a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bloch,Fin.sum_univ_three,pauliMatrix,pauliX,pauliY,pauliZ] <;> ring

theorem bloch_hermitian (v : Fin 3 → ℝ) : (bloch v).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bloch,Matrix.conjTranspose_apply]
  ring

theorem bloch_gram (v : Fin 3 → ℝ) :
    bloch v = (bloch v)ᴴ*bloch v + ((1-sqnorm v)/4:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [bloch_hermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bloch,sqnorm,Fin.sum_univ_three,
      Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_pow] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem bloch_posSemidef (v : Fin 3 → ℝ) (hv : sqnorm v ≤ 1) : (bloch v).PosSemidef := by
  rw [bloch_gram]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).add
      (Matrix.PosSemidef.one.smul (by linarith : 0≤(1-sqnorm v)/4))

theorem bloch_trace (v : Fin 3 → ℝ) : (bloch v).trace = 1 := by
  simp [bloch,Matrix.trace,Fin.sum_univ_two]
  ring

theorem bloch_density (v : Fin 3 → ℝ) (hv : sqnorm v ≤ 1) : IsDensityOperator (bloch v) :=
  ⟨bloch_posSemidef v hv,bloch_trace v⟩

theorem bloch_pauli_trace (v : Fin 3 → ℝ) (a : Fin 3) :
    (pauliMatrix a*bloch v).trace = (v a:ℂ) := by
  fin_cases a <;> simp [pauliMatrix,pauliX,pauliY,pauliZ,bloch,Matrix.trace,Fin.sum_univ_two] <;> ring_nf
  norm_num [Complex.I_sq]

noncomputable def productState {n : ℕ} (v : Fin n → Fin 3 → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  qubitTensor (fun i => bloch (v i))

theorem product_density {n : ℕ} (v : Fin n → Fin 3 → ℝ) (hv : ∀ i, sqnorm (v i) ≤ 1) :
    (productState v).PosSemidef ∧ (productState v).trace=1 :=
  qubitTensor_density _ (fun i => bloch_density (v i) (hv i))
end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
