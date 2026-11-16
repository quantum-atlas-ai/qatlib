/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BQPvsPHRaz18.OracleSep.SourceModel
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! A circuit-size tag alone does not certify the hypotheses of Tal's Fourier bound. -/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPvsPHRaz18.OracleSep

open scoped BigOperators
open Qatlib.Papers.BQPvsPHRaz18.OracleSep.SourceModel

/-- The one-coordinate sign function has a unit singleton Fourier coefficient. -/
theorem singleton_coeff :
    fourierCoeff (fun x : Fin 1 → Bool => signVal (x 0)) {0} = 1 := by
  have hs : ∀ x : Fin 1 → Bool, signVal (x 0) * signVal (x 0) = 1 := by
    intro x
    cases x 0 <;> simp [signVal]
  simp only [fourierCoeff, Finset.prod_singleton]
  simp_rw [hs]
  norm_num

/-- An arbitrary size-one circuit record violates the old universally quantified Tal bound. -/
theorem circuit_tag_gap :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ (A : SignCircuit (Fin 1)) (k : ℕ),
      ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin 1) => S.card = k)),
        |fourierCoeff A.value S| ≤
          (c * Real.log (A.size : ℝ)) ^ ((A.depth - 1) * k) := by
  rintro ⟨c, _, hc⟩
  let A : SignCircuit (Fin 1) := {
    value := fun x => signVal (x 0)
    value_sign := by intro x; cases x 0 <;> simp [signVal]
    size := 1
    depth := 2 }
  have h := hc A 1
  have hsets : Finset.univ.filter (fun S : Finset (Fin 1) => S.card = 1) = {{0}} := by
    decide
  rw [hsets] at h
  norm_num [A, singleton_coeff] at h

end Qatlib.Papers.BQPvsPHRaz18.OracleSep
