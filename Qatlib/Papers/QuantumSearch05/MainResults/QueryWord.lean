/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QuantumSearch05.MainResults.Basic

@[expose] public section

/-!
# Query accounting for recursive fixed-point search

Connects the executable prepared-word model with the arithmetic query parameter of
[Grover2005], Section 4. The bridge concerns forward and backward input-preparation queries.
The prepared-word model represents the target phase shift as a fixed gate. The count here
corresponds to the forward and backward uses of `U` in Section 4.

## References

* [Grover, 2005][Grover2005], [arXiv:quant-ph/0503205v1](https://arxiv.org/abs/quant-ph/0503205v1)
-/

set_option autoImplicit false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.LcuPostselect.ScaledLCU

namespace Qatlib.Papers.QuantumSearch05.MainResults

/-- At stage `m`, the executable fixed-point word uses `2 * queries m + 1` forward or backward
input-preparation queries. This is the `3 ^ m` count of forward and backward uses of `U`
in [Grover2005], Section 4. -/
theorem prepared_input_queries_word_eq_two_mul_queries_add_one
    {H O : Type*} [Fintype H] [DecidableEq H] [Fintype O]
    (L : Matrix H O ℂ) (j₀ : H) (cs : List (AdjointStep H)) (m : ℕ) :
    preparedInputQueries (LCUFixedPoint.word L j₀ cs m) =
      2 * Qatlib.Papers.QuantumSearch05.MainResults.queries m + 1 := by
  calc
    preparedInputQueries (LCUFixedPoint.word L j₀ cs m) = 3 ^ m :=
      (LCUFixedPoint.word_counts L j₀ cs m).2.1
    _ = 2 * Qatlib.Papers.QuantumSearch05.MainResults.queries m + 1 :=
      Qatlib.Papers.QuantumSearch05.MainResults.three_pow_eq_two_mul_queries m

end Qatlib.Papers.QuantumSearch05.MainResults
