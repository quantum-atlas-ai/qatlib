/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.SolovayKitaevCount
set_option warningAsError false

namespace Qatlib.Papers.SolovayKitaev05.MainResults.SKTheorem

open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

structure InstructionSet (d : ℕ) where

  gens : Finset (Matrix (Fin d) (Fin d) ℂ)

  mem_su : ∀ g ∈ gens, g ∈ unitary (Matrix (Fin d) (Fin d) ℂ) ∧ g.det = 1

  inv_mem : ∀ g ∈ gens, star g ∈ gens

  universal : ∀ U : Matrix (Fin d) (Fin d) ℂ,
    U ∈ unitary (Matrix (Fin d) (Fin d) ℂ) → U.det = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ S : List (Matrix (Fin d) (Fin d) ℂ),
        (∀ g ∈ S, g ∈ gens) ∧ ‖U - S.prod‖ < ε

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
