/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.TensorModel.SparseXorsat

/-!
# Binary overlaps and the overlap gap property

`binaryOverlap` is the absolute spin inner product divided by the number of coordinates, and
`binaryMaximum` is the maximum binary tensor energy. `binaryOGP` requires every pair of
configurations within the specified energy tolerance of this maximum to have overlap outside the
forbidden interval, expressing the binary overlap gap notion used in [GohMuller2026].

## Main statements

* `binary_overlap_range`: For `N > 0`, the normalized absolute binary overlap lies in `[0,1]`.
* `binaryOGP`: The condition that every pair of binary configurations with energy at least
  `binaryMaximum J - ε` has overlap at most `μ₁` or at least `μ₂`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.TensorModel.SparseXorsat

namespace Qatlib.Papers.OverlapGapGoh26.OgpBridge.Binary

/-- The normalized absolute spin overlap `|∑ i, bitSpin x i * bitSpin y i| / N` of two Boolean
configurations. -/
def binaryOverlap {N : ℕ} (x y : Fin N → Bool) : ℝ :=
  |∑ i,bitSpin x i*bitSpin y i|/(N:ℝ)

/-- For `N > 0`, the normalized absolute binary overlap lies in `[0,1]`. See [GohMuller2026]. -/
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

/-- The maximum tensor energy over all Boolean spin configurations. -/
def binaryMaximum {q N : ℕ} (J : Tensor q N) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x : Fin N → Bool => tensorEnergy J (bitSpin x))

/-- The condition that every pair of binary configurations with energy at least `binaryMaximum J
- ε` has overlap at most `μ₁` or at least `μ₂`. -/
def binaryOGP {q N : ℕ} (J : Tensor q N) (ε μ₁ μ₂ : ℝ) : Prop :=
  ∀ x y : Fin N → Bool,
    binaryMaximum J-ε≤tensorEnergy J (bitSpin x) →
    binaryMaximum J-ε≤tensorEnergy J (bitSpin y) →
    binaryOverlap x y≤μ₁ ∨ μ₂≤binaryOverlap x y

/-- The energy of every Boolean spin configuration is at most `binaryMaximum J`. See
[GohMuller2026]. -/
theorem binary_energy_le_maximum {q N : ℕ} (J : Tensor q N) (x : Fin N → Bool) :
    tensorEnergy J (bitSpin x)≤binaryMaximum J :=
  Finset.le_sup' (f:=fun x : Fin N → Bool => tensorEnergy J (bitSpin x)) (Finset.mem_univ x)

end Qatlib.Papers.OverlapGapGoh26.OgpBridge.Binary
