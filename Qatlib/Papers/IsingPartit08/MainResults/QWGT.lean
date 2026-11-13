/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPartit08.MainResults.Defs

/-!
# Quadratically signed Eulerian weight enumerators

This module defines the real quadratically signed weight enumerator `qwgt` over a binary matrix
kernel. Setting the second weight variable to one recovers `signedEulerianSum`, and taking a
zero sign matrix recovers `eulerianSum`, giving the weight-enumerator notation used in Theorem 1
of [Geraci2008].

## Main statements

* `qwgt_one_eq_signedEulerianSum`: identifies the one-variable specialization with the signed
  Eulerian sum.
* `qwgt_zero_eq_eulerianSum`: identifies the zero-sign specialization with the unsigned sum.

## References

* [Geraci, 2008][Geraci2008]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

/-- The real homogeneous weight enumerator over `kerSet A`, with sign given by `quadForm B` and
weights determined by Hamming weight and its complement. -/
def qwgt {M N : ℕ} (A : Matrix (Fin M) (Fin N) (ZMod 2))
    (B : Matrix (Fin N) (Fin N) (ZMod 2)) (x y : ℝ) : ℝ :=
  ∑ b ∈ kerSet A, paritySign (quadForm B b) * x ^ wt b * y ^ (N - wt b)

/-- The weight enumerator `qwgt CH B lam 1` equals `signedEulerianSum B CH lam`. See
[Geraci2008]. -/
theorem qwgt_one_eq_signedEulerianSum {R N : ℕ}
    (B : Matrix (Fin N) (Fin N) (ZMod 2)) (CH : Matrix (Fin R) (Fin N) (ZMod 2))
    (lam : ℝ) : qwgt CH B lam 1 = signedEulerianSum B CH lam := by
  simp [qwgt, signedEulerianSum]

/-- With zero sign matrix and second weight variable one, the weight enumerator equals the
unsigned Eulerian sum. See [Geraci2008]. -/
theorem qwgt_zero_eq_eulerianSum {R N : ℕ}
    (CH : Matrix (Fin R) (Fin N) (ZMod 2)) (lam : ℝ) :
    qwgt CH (0 : Matrix (Fin N) (Fin N) (ZMod 2)) lam 1 = eulerianSum CH lam := by
  simp [qwgt, eulerianSum, quadForm]

/-- The signed Eulerian sum can be written as `qwgt CH B lam 1`. -/
theorem signedEulerianSum_eq_qwgt {R N : ℕ}
    (B : Matrix (Fin N) (Fin N) (ZMod 2)) (CH : Matrix (Fin R) (Fin N) (ZMod 2))
    (lam : ℝ) : signedEulerianSum B CH lam = qwgt CH B lam 1 :=
  (qwgt_one_eq_signedEulerianSum B CH lam).symm

end Qatlib.Papers.IsingPartit08.MainResults
