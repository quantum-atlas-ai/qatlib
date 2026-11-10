/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.TensorModel.SparseXorsat
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.TensorModel.SparseXorsat

namespace Qatlib.Papers.OverlapGapGoh26.OgpBridge.Binary

def binaryOverlap {N : ℕ} (x y : Fin N → Bool) : ℝ :=
  |∑ i,bitSpin x i*bitSpin y i|/(N:ℝ)

theorem binary_overlap_range {N : ℕ} (hN : 0<N) (x y : Fin N → Bool) :
    binaryOverlap x y∈Set.Icc (0:ℝ) 1 := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  constructor
  · exact div_nonneg (abs_nonneg _) hn.le
  · apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ ∑ i,|bitSpin x i*bitSpin y i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _i : Fin N,(1:ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold bitSpin
        cases x i <;> cases y i <;> norm_num
      _ = _ := by simp

def binaryMaximum {q N : ℕ} (J : Tensor q N) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x : Fin N → Bool => tensorEnergy J (bitSpin x))

def binaryOGP {q N : ℕ} (J : Tensor q N) (ε μ₁ μ₂ : ℝ) : Prop :=
  ∀ x y : Fin N → Bool,
    binaryMaximum J-ε≤tensorEnergy J (bitSpin x) →
    binaryMaximum J-ε≤tensorEnergy J (bitSpin y) →
    binaryOverlap x y≤μ₁ ∨ μ₂≤binaryOverlap x y

theorem binary_energy_le_maximum {q N : ℕ} (J : Tensor q N) (x : Fin N → Bool) :
    tensorEnergy J (bitSpin x)≤binaryMaximum J :=
  Finset.le_sup' (f:=fun x : Fin N → Bool => tensorEnergy J (bitSpin x)) (Finset.mem_univ x)

end Qatlib.Papers.OverlapGapGoh26.OgpBridge.Binary
