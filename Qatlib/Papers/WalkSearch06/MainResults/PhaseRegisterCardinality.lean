/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# WalkSearch06 — the cardinality of the phase-reflection register

Source: F. Magniez, A. Nayak, J. Roland, and M. Santha, *Search via Quantum Walk*,
arXiv:quant-ph/0608026v4, Theorem 6, printed p. 9.

Theorem 6 counts the registers of the reflection `R(P)`: it acts on `2⌈log₂ n⌉ + ks`
qubits, where `s ∈ log₂(1/Δ(P)) + O(1)` is the number of bits of each phase register
and `k` is the number of copies.

The library model of that register is
`Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseReflectionSpace I M k
= (Fin k → Fin M) × (Bool × I)`: `k` phase registers of `s` bits (`M = 2 ^ s`), one
control bit, and the walk register `I`. For a walk on `Fin n × Fin n` the register
therefore has `2 * (2 ^ s) ^ k * n ^ 2` basis states. The extra factor of `2` is the
control bit of the library model: the paper's `2⌈log₂ n⌉ + ks` count does not include
it, so the two counts differ by that single control qubit whenever the phase registers
and the walk register are laid out as bit strings.

## Main statements

* `phaseReflectionSpace_card`: the phase-reflection register has `2 * (2 ^ s) ^ k * n ^ 2`
  basis states.

## References

* [Magniez, Nayak, Roland, Santha, 2006][MagniezNayakRolandSantha2011]
-/

namespace Qatlib.Papers.WalkSearch06.MainResults

open Qatlib.Concepts.SpectralFilter.PhaseReadout

/-- The phase-reflection register of `k` phase registers with `s` bits each over a walk on
`Fin n × Fin n` has `2 * (2 ^ s) ^ k * n ^ 2` basis states.

The register is `PhaseReflectionSpace (Fin n × Fin n) (2 ^ s) k = (Fin k → Fin 2 ^ s) ×
(Bool × (Fin n × Fin n))`, so the count is the number of phase register contents
`(2 ^ s) ^ k` times the two values of the control bit times the `n ^ 2` positions of the
walk. The statement records the library representation exactly; it does not claim that the
count equals the paper's `2⌈log₂ n⌉ + ks` qubit count, which omits the control bit and
assumes the walk register is padded to a power of two. -/
theorem phaseReflectionSpace_card (n s k : ℕ) :
    Fintype.card (PhaseReflectionSpace (Fin n × Fin n) (2 ^ s) k) = 2 * (2 ^ s) ^ k * n ^ 2 := by
  change Fintype.card ((Fin k → Fin (2 ^ s)) × (Bool × (Fin n × Fin n)))
    = 2 * (2 ^ s) ^ k * n ^ 2
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

end Qatlib.Papers.WalkSearch06.MainResults
