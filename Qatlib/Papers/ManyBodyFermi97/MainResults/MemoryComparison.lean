/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs

/-!
# Memory requirements for first and second quantization

This module compares occupation registers with tuples of particle positions. It counts the basis
configurations, gives the two memory formulas, and proves that the first-quantized
configurations can be injected into the allocated qubit register.

The mathematical setting is that of [AbramsLloyd1997].

## Main statements

* `firstQuantized_encoding_exists`: There is an injective encoding of `n` particle positions in
  `m` modes into a register of `firstQuantizedBits n m` bits.
* `memory_comparison`: Collects the memory formulas, basis cardinalities, and the inequality
  showing that the first-quantized register has enough basis states.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath

/-- The set of configurations of `n` labeled particles in `m` modes has cardinality `m ^ n`. -/
theorem firstQuantized_state_count (n m : ℕ) :
    Fintype.card (Fin n → Fin m) = m ^ n := by
  simp

/-- The second-quantized memory count is `m`, the number of modes. -/
theorem secondQuantized_memory_independent (m : ℕ) : secondQuantizedBits m = m := rfl

/-- The first-quantized memory count is `n * quWordBits m`. -/
theorem firstQuantized_memory_eq (n m : ℕ) :
    firstQuantizedBits n m = n * quWordBits m := rfl

/-- First quantization uses fewer bits whenever `n * quWordBits m < m`. -/
theorem firstQuantized_memory_advantage {n m : ℕ}
    (h : n * quWordBits m < m) : firstQuantizedBits n m < secondQuantizedBits m := by
  simpa [firstQuantizedBits, secondQuantizedBits] using! h

/-- An occupation register with `m` bits has `2 ^ m` basis configurations. -/
theorem occupation_register_card (m : ℕ) : Fintype.card (Reg m) = 2 ^ m :=
  secondQuantized_card m

/-- There is an injective encoding of `n` particle positions in `m` modes into a register of
`firstQuantizedBits n m` bits. [AbramsLloyd1997] -/
theorem firstQuantized_encoding_exists (n m : ℕ) :
    ∃ f : (Fin n → Fin m) → Reg (firstQuantizedBits n m), Function.Injective f :=
  ⟨_, firstQuantized_injective n m⟩

/-- Collects the memory formulas, basis cardinalities, and the inequality showing that the
first-quantized register has enough basis states. [AbramsLloyd1997] -/
theorem memory_comparison (n m : ℕ) :
    secondQuantizedBits m = m ∧
      firstQuantizedBits n m = n * quWordBits m ∧
      Fintype.card (Reg m) = 2 ^ m ∧
      Fintype.card (Fin n → Fin m) = m ^ n ∧
      m ^ n ≤ 2 ^ firstQuantizedBits n m :=
  ⟨rfl, rfl, occupation_register_card m, firstQuantized_state_count n m,
    firstQuantized_bits_suffice n m⟩

end Qatlib.Papers.ManyBodyFermi97.MainResults
