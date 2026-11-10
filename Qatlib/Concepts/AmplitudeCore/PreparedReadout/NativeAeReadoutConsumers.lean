/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

theorem nativeAEDecode_zero_label (M k : ℕ) (z : Fin M) (hz : z.val = 0) :
    nativeAEDecode M k z = 0 := by
  have hreceipt := congrArg Prod.fst (nativeAESin_value_and_terms 0 k)
  rw [nativeAESin_counted_zero] at hreceipt
  have hs : nativeAESin 0 k = 0 := hreceipt.symm
  simp [nativeAEDecode, hz, hs]

theorem native_ae_counting_relative_output_consumer :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M k N : ℕ) (hM : 2 ≤ M)
      (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ),
      let a := MeasureProb (preparedAAState A j) S
      (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |((N : ℚ) * nativeAEDecode M k z : ℝ) - (N : ℝ) * a| ≤ (N : ℝ) *
          (2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) +
            Real.pi ^ 2 / (M : ℝ) ^ 2 + ((2 : ℝ)⁻¹) ^ k)),
        (aeLaw M A j S hA hM).prob z) ≥ 8 / Real.pi ^ 2 ∧
      (∀ z : Fin M, (a = 0 ∧ z.val = 0) → nativeAEDecode M k z = 0) := by
  intro I _ _ M k N hM A j S hA
  (try dsimp only)
  refine ⟨?_, fun z hz => nativeAEDecode_zero_label M k z hz.2⟩
  let a := MeasureProb (preparedAAState A j) S
  let B := 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) +
    Real.pi ^ 2 / (M : ℝ) ^ 2 + ((2 : ℝ)⁻¹) ^ k
  have hsub : (Finset.univ.filter (fun z : Fin M =>
      |(nativeAEDecode M k z : ℝ) - a| ≤ B)) ⊆
      (Finset.univ.filter (fun z : Fin M =>
        |((N : ℚ) * nativeAEDecode M k z : ℝ) - (N : ℝ) * a| ≤ (N : ℝ) * B)) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h :=
        mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hz).2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    push_cast
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact h
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun z _ _ => (aeLaw M A j S hA hM).nonneg z)
  exact (native_ae_same_record_bhmt_success I M k hM A j S hA).trans hmass

end Qatlib.Concepts.AmplitudeCore.PreparedReadout
