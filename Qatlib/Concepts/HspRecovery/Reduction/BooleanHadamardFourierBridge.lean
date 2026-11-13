/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardPhase

/-!
# Hadamard transform as a Boolean Fourier matrix

`hadamardN_eq_booleanFourier_submatrix` identifies the register-indexed Hadamard transform with
the Fourier matrix of the Boolean group after reindexing rows by Boolean characters and columns
by Boolean vectors. This supplies the matrix bridge between register circuits and character
sampling. See [NielsenChuang2010] for the mathematical background.

## Main statements

* `hadamardN_eq_booleanFourier_submatrix`: the reindexed Fourier matrix equals `HadamardN`.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.HspRecovery.ReductionCore

/-- The `n`-register Hadamard matrix is the Boolean-group Fourier matrix reindexed by Boolean
characters on rows and encoded registers on columns. -/
theorem hadamardN_eq_booleanFourier_submatrix (n : ℕ) :
    Qatlib.Foundations.PureStateMath.HadamardN n =
      (fourierMatrix (BooleanVec n)).submatrix
        (fun y => booleanCharacter (regBooleanEquiv n y))
        (regBooleanEquiv n) := by
  ext y z
  rw [Qatlib.Foundations.PureStateMath.hadamardN_apply]
  change
    ((Real.sqrt 2 : ℂ)⁻¹) ^ n *
        ∏ i, (if y i && z i then (-1 : ℂ) else 1) =
      fourierMatrix (BooleanVec n)
        (booleanCharacter (regBooleanEquiv n y)) (regBooleanEquiv n z)
  exact (booleanFourierMatrix_regBooleanEquiv_apply y z).symm

end Qatlib.Concepts.HspRecovery.ReductionCore
