/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath

theorem firstQuantized_state_count (n m : ℕ) :
    Fintype.card (Fin n → Fin m) = m ^ n := by
  simp

theorem secondQuantized_memory_independent (m : ℕ) : secondQuantizedBits m = m := rfl

theorem firstQuantized_memory_eq (n m : ℕ) :
    firstQuantizedBits n m = n * quWordBits m := rfl

theorem firstQuantized_memory_advantage {n m : ℕ}
    (h : n * quWordBits m < m) : firstQuantizedBits n m < secondQuantizedBits m := by
  simpa [firstQuantizedBits, secondQuantizedBits] using! h

theorem occupation_register_card (m : ℕ) : Fintype.card (Reg m) = 2 ^ m :=
  secondQuantized_card m

theorem firstQuantized_encoding_exists (n m : ℕ) :
    ∃ f : (Fin n → Fin m) → Reg (firstQuantizedBits n m), Function.Injective f :=
  ⟨_, firstQuantized_injective n m⟩

theorem memory_comparison (n m : ℕ) :
    secondQuantizedBits m = m ∧
      firstQuantizedBits n m = n * quWordBits m ∧
      Fintype.card (Reg m) = 2 ^ m ∧
      Fintype.card (Fin n → Fin m) = m ^ n ∧
      m ^ n ≤ 2 ^ firstQuantizedBits n m :=
  ⟨rfl, rfl, occupation_register_card m, firstQuantized_state_count n m,
    firstQuantized_bits_suffice n m⟩

end Qatlib.Papers.ManyBodyFermi97.MainResults
