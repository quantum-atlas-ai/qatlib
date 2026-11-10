/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPartit08.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

def qwgt {M N : ℕ} (A : Matrix (Fin M) (Fin N) (ZMod 2))
    (B : Matrix (Fin N) (Fin N) (ZMod 2)) (x y : ℝ) : ℝ :=
  ∑ b ∈ kerSet A, paritySign (quadForm B b) * x ^ wt b * y ^ (N - wt b)

theorem qwgt_one_eq_signedEulerianSum {R N : ℕ}
    (B : Matrix (Fin N) (Fin N) (ZMod 2)) (CH : Matrix (Fin R) (Fin N) (ZMod 2))
    (lam : ℝ) : qwgt CH B lam 1 = signedEulerianSum B CH lam := by
  simp [qwgt, signedEulerianSum]

theorem qwgt_zero_eq_eulerianSum {R N : ℕ}
    (CH : Matrix (Fin R) (Fin N) (ZMod 2)) (lam : ℝ) :
    qwgt CH (0 : Matrix (Fin N) (Fin N) (ZMod 2)) lam 1 = eulerianSum CH lam := by
  simp [qwgt, eulerianSum, quadForm]

theorem signedEulerianSum_eq_qwgt {R N : ℕ}
    (B : Matrix (Fin N) (Fin N) (ZMod 2)) (CH : Matrix (Fin R) (Fin N) (ZMod 2))
    (lam : ℝ) : signedEulerianSum B CH lam = qwgt CH B lam 1 :=
  (qwgt_one_eq_signedEulerianSum B CH lam).symm

end Qatlib.Papers.IsingPartit08.MainResults
