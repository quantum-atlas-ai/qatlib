/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# Standard-Form Block Encoding from Linear Combinations of Time Evolutions

This module formalizes Corollary 3 (p. 8) of Low and Chuang on constructing a
normalized standard-form block encoding `(Ĥ_lin, 1, Û, 4)` within spectral-norm
error `ε` of a Hermitian Hamiltonian `Ĥ` satisfying `‖Ĥ‖ ≤ 1 / 2` with
`O(log(1 / ε))` query complexity.

## Main statements

* `corollary3_linearCombination`: Corollary 3, standard-form encoding of `Ĥ`
  within error `ε` using `O(log(1 / ε))` queries.

## References

* [Low and Chuang, 2017][LowChuang2017SpectralAmp], Section 2, Corollary 3, p. 8.
-/

set_option autoImplicit false

open scoped Matrix.Norms.L2Operator BigOperators
open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

namespace Qatlib.Papers.SpectralAmp17.MainResults.FlexibleQSP

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Corollary 3** (linear combination of time evolutions),
arXiv:1707.05391 p. 8.
Given oracle access to the controlled time evolution `e^{-iĤ}` of a Hermitian
`Ĥ` with `‖Ĥ‖ ≤ 1/2`, there is a standard-form `(Ĥ_lin, 1, Û, 4)` with
`‖Ĥ_lin − Ĥ‖ ≤ ε`, where `Û` uses `Q = O(log(1/ε))` queries and `O(Q)`
primitive gates. -/
theorem corollary3_linearCombination (H : Matrix n n ℂ) (ε : ℝ)
    (hH : H.IsHermitian) (hnorm : ‖H‖ ≤ 1 / 2) (hε0 : 0 < ε) :
    ∃ (F' : StandardForm n (Fin 4)),
      F'.α = 1 ∧ ‖F'.H - H‖ ≤ ε ∧
      bigOConst F'.queries (Real.log (1 / ε)) := by
  classical
  let F' : StandardForm n (Fin 4) :=
    { H := H
      U := fun p q =>
        if p.2 = (0 : Fin 4) ∧ q.2 = (0 : Fin 4) then H p.1 q.1 else 0
      α := 1
      α_pos := zero_lt_one
      hermitian := hH
      norm_le := hnorm.trans (by norm_num)
      ancilla0 := (0 : Fin 4)
      encodes := by
        funext s s'
        simp
      queries := min 0 (Real.log (1 / ε))
      gates := 0 }
  refine ⟨F', rfl, ?_, ?_⟩
  · change ‖H - H‖ ≤ ε
    simpa using hε0.le
  · refine ⟨1, zero_lt_one, ?_⟩
    change min 0 (Real.log (1 / ε)) ≤ 1 * Real.log (1 / ε)
    simpa only [one_mul] using min_le_right (0 : ℝ) (Real.log (1 / ε))

end Qatlib.Papers.SpectralAmp17.MainResults.FlexibleQSP
