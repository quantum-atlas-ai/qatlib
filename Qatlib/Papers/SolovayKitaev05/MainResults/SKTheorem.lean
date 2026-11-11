/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.SolovayKitaevCount

/-!
# A concrete SU(2) Solovay–Kitaev approximation theorem

This module defines `InstructionSet`, a finite inverse-closed family of special unitaries whose
words approximate every special unitary. Its main theorem `solovay_kitaev_su2_cliffordT` gives a
concrete SU(2) approximation bound for the Clifford–T word evaluator, with word length bounded
by a fixed power of `log (1/ε)`, in the setting of [DawsonNielsen2006].

## Main statements

* `solovay_kitaev_su2_cliffordT`: There are positive constants `K` and `e` such that every SU(2)
  matrix has a Clifford–T word approximating it within `ε` and of length at most `K*(log
  ε⁻¹)^skExponent` whenever `0 < ε ≤ e`, as in [DawsonNielsen2006].

## References

* [Dawson and Nielsen, 2006][DawsonNielsen2006]
-/

set_option warningAsError false

namespace Qatlib.Papers.SolovayKitaev05.MainResults.SKTheorem

open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

/-- A finite instruction set of determinant-one unitaries, closed under adjoints, whose finite
products approximate every determinant-one unitary to arbitrary positive accuracy. -/
structure InstructionSet (d : ℕ) where

  gens : Finset (Matrix (Fin d) (Fin d) ℂ)

  mem_su : ∀ g ∈ gens, g ∈ unitary (Matrix (Fin d) (Fin d) ℂ) ∧ g.det = 1

  inv_mem : ∀ g ∈ gens, star g ∈ gens

  universal : ∀ U : Matrix (Fin d) (Fin d) ℂ,
    U ∈ unitary (Matrix (Fin d) (Fin d) ℂ) → U.det = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ S : List (Matrix (Fin d) (Fin d) ℂ),
        (∀ g ∈ S, g ∈ gens) ∧ ‖U - S.prod‖ < ε

/-- There are positive constants `K` and `e` such that every SU(2) matrix has a Clifford–T word
approximating it within `ε` and of length at most `K*(log ε⁻¹)^skExponent` whenever `0 < ε ≤
e`, as in [DawsonNielsen2006]. -/
theorem solovay_kitaev_su2_cliffordT :
    ∃ K e : ℝ, 0 < K ∧ 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε ≤ e →
      ∀ U ∈ Qatlib.Concepts.UnbiasedBases.ThreeBasis.su2Set,
        ∃ u : List (Fin 3),
          ‖U - Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2.ctEval u‖
              ≤ ε ∧
          (u.length : ℝ) ≤
            K * (Real.log ε⁻¹) ^
              Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2.skExponent :=
  Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2.exists_word_approx_polylog

end Qatlib.Papers.SolovayKitaev05.MainResults.SKTheorem
