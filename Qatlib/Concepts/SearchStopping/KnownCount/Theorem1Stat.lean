/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Hadamard factorization of diffusion

`Theorem1` states the n-qubit matrix identity expressing diffusion as the conjugation of
`ZeroPhaseReflection` by `HadamardN`. The identity underlies the expanded Grover circuit.

For the mathematical background, see [Grover1997].

## Main statements

* `Theorem1`: The proposition that n-qubit diffusion equals `HadamardN n * ZeroPhaseReflection n
  * HadamardN n` for every n.

## References

* [Grover, 1997][Grover1997]
-/

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition that n-qubit diffusion equals `HadamardN n * ZeroPhaseReflection n *
HadamardN n` for every n. -/
def Theorem1 : Prop :=
  ∀ n : ℕ, Diffusion (Reg n) = HadamardN n * ZeroPhaseReflection n * HadamardN n

end Qatlib.Concepts.SearchStopping.KnownCount
