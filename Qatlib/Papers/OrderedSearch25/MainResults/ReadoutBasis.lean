/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialCircuit

@[expose] public section

/-!
# Measurement coordinates in Definition 3

The translation-invariant polynomial readout embeds a basis vector in
two halves of the register. It places the two nonzero coordinates at
`y` and `y+n`, with the second coefficient carrying the query parity.
-/

set_option autoImplicit false

open Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.OrderedSearch25.MainResults

/-- The coordinates of the polynomial readout vector are those of
Equation (11) for every outcome and register coordinate. -/
theorem readout_vector_coordinates (n k : ℕ) (y : Fin n) (i : Fin (2 * n)) :
    tiPolynomialReadoutVector n k y i =
      (if i.val = y.val then (Real.sqrt 2 : ℂ)⁻¹
      else if i.val = y.val + n then (Real.sqrt 2 : ℂ)⁻¹ * (-1 : ℂ) ^ k
      else 0) := by
  unfold tiPolynomialReadoutVector tiPolynomialState
  by_cases hi : i.val < n
  · have hright : i.val ≠ y.val + n := by omega
    simp only [dite_eq_left hi, ket_apply, Fin.ext_iff, ite_eq_right hright]
    split <;> simp
  · have hleft : i.val ≠ y.val := by have := y.isLt; omega
    have hright : i.val - n = y.val ↔ i.val = y.val + n := by omega
    simp only [dite_eq_right hi, ket_apply, Fin.ext_iff, hright, ite_eq_right hleft]
    split <;> simp

end Qatlib.Papers.OrderedSearch25.MainResults
