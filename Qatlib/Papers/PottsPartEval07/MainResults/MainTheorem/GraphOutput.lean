/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.LatticeDecode
public import Qatlib.Papers.PottsPartEval07.PottsBridge.KernelComponents

@[expose] public section

/-!
# Compressed dual-code data compute the graph's Potts partition function

The graph code is the actual range of its coboundary map. MacWilliams duality
and the graph partition identity prove the output formula. The computation
uses the supplied compressed weight list, not the exponentially large spin sum.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators
open Qatlib.Papers.PottsPartEval07.ExactRecovery

variable {q : ℕ} [NeZero q] {V E : Type*}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The graph coboundary as a linear map over the spin alphabet. -/
def graphCoboundary (ends : E → V × V) : (V → ZMod q) →ₗ[ZMod q] (E → ZMod q) where
  toFun := Qatlib.Papers.PottsPartEval07.PottsBridge.coboundary q ends
  map_add' := (Qatlib.Papers.PottsPartEval07.PottsBridge.coboundary q ends).map_add
  map_smul' := by
    intro a σ
    ext e
    change a * σ (ends e).1 - a * σ (ends e).2 =
      a * (σ (ends e).1 - σ (ends e).2)
    ring

/-- The actual cocycle code of the endpoint graph. -/
def graphCode (ends : E → V × V) : Submodule (ZMod q) (E → ZMod q) :=
  LinearMap.range (graphCoboundary ends)

/-- The graph-code homogeneous enumerator at `(1,y)` is its actual weight sum. -/
theorem graphCode_enum (ends : E → V × V) (y : ℝ) :
    weightEnum (graphCode (q := q) ends) 1 (y : ℂ) =
      (Qatlib.Papers.PottsPartEval07.PottsBridge.codeWeightEnum q ends y : ℂ) := by
  classical
  unfold weightEnum Qatlib.Papers.PottsPartEval07.PottsBridge.codeWeightEnum
  simp only [one_pow, one_mul]
  push_cast
  have hweight : ∀ w : E → ZMod q,
      hammingWeight w = Qatlib.Papers.PottsPartEval07.PottsBridge.hammingWeight q w := fun _ => rfl
  simp only [hweight]
  symm
  exact Finset.sum_subtype (Finset.univ.image (Qatlib.Papers.PottsPartEval07.PottsBridge.coboundary q ends))
    (by
      intro w
      simp only [graphCode, LinearMap.mem_range, graphCoboundary,
        Finset.mem_image, Finset.mem_univ, true_and]
      rfl)
    (fun w => (y : ℂ) ^ Qatlib.Papers.PottsPartEval07.PottsBridge.hammingWeight q w)

/-- The computed Potts value from a compressed dual-code weight list. -/
def compressedPotts {classes : ℕ} (ends : E → V × V) (codeSize classSize : ℕ)
    (weights : Fin classes → ℕ) (y : ℝ) : ℂ :=
  ((y : ℂ) ^ Fintype.card E)⁻¹ * (q : ℂ) ^ Qatlib.Papers.PottsPartEval07.PottsBridge.componentCount ends *
    (codeSize : ℂ)⁻¹ *
      compressedEnum (Fintype.card E) classSize weights
        (1 + ((q : ℂ) - 1) * y) (1 - (y : ℂ))

/-- The actual codeword partition and dual-code relation prove the exact output. -/
theorem compressedPotts_eq {classes classSize : ℕ} (ends : E → V × V)
    (C : Submodule (ZMod q) (E → ZMod q)) (partition : WeightClasses C classes classSize)
    (hdual : dualCode C = graphCode ends) (y : ℝ) (hy : y ≠ 0) :
    compressedPotts (q := q) ends (Fintype.card C) classSize
      (fun i => hammingWeight (partition.representative i).val) y =
      (Qatlib.Papers.PottsPartEval07.PottsBridge.pottsZ q ends y : ℂ) := by
  unfold compressedPotts
  rw [compressedEnum_eq C partition]
  rw [mul_assoc _ (Fintype.card C : ℂ)⁻¹,
    ← macWilliams_weightEnum C 1 (y : ℂ), hdual, graphCode_enum]
  have hp := Qatlib.Papers.PottsPartEval07.PottsBridge.pottsZ_eq_componentCount q ends y hy
  apply Eq.symm
  exact_mod_cast hp

/-- Recovered representative weights give the same exact graph output. -/
theorem compressedPotts_recovered {classes classSize : ℕ} (ends : E → V × V)
    (C : Submodule (ZMod q) (E → ZMod q)) (partition : WeightClasses C classes classSize)
    (hdual : dualCode C = graphCode ends) (weights : Fin classes → ℕ)
    (hweights : ∀ i, weights i = hammingWeight (partition.representative i).val)
    (y : ℝ) (hy : y ≠ 0) :
    compressedPotts (q := q) ends (Fintype.card C) classSize weights y =
      (Qatlib.Papers.PottsPartEval07.PottsBridge.pottsZ q ends y : ℂ) := by
  have he : weights = fun i => hammingWeight (partition.representative i).val :=
    funext hweights
  simpa only [he] using compressedPotts_eq ends C partition hdual y hy

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
