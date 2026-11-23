/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BeyondCircuit08.MainResults.Zeckendorf

@[expose] public section

/-!
# Exact value range of the Zeckendorf encoding (Proposition 4)

Paper: Stephen P. Jordan, *Quantum Computation Beyond the Circuit Model*,
arXiv:0809.2307v1 (2008), §3.12, Proposition 4, pp. 88–89.

Proposition 4 prints the codomain of the encoding
`z(s) = ∑ᵢ sᵢ fᵢ₊₁` as `{0, …, f_{n+2}}`, but the proof gives the values
`{0, …, f_{n+2} - 1}`: the top endpoint `f_{n+2}` is never attained, since
every allowed string of length `n` has `starWeight` strictly below
`f_{n+2}` (`starWeight_lt_fib` in the public library).  This file turns
that observation into the exact range characterisation: the attained
values are precisely `Set.Iio (Nat.fib (n + 2))`, the cardinality of the
string type is `Nat.fib (n + 2)`, and the printed top endpoint is
unattainable, confirming that the inclusive endpoint in the printed
statement is a typo for `f_{n+2} - 1`.

## Main statements

* `proposition4_value_range`: the range of `zMap` values is
  `Set.Iio (Nat.fib (n + 2))`.
* `proposition4_top_not_attained`: no allowed string has weight
  `Nat.fib (n + 2)`.
* `proposition4_card`: `Fintype.card (PStrings n) = Nat.fib (n + 2)`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BeyondCircuit08.MainResults.Zeckendorf

open Qatlib.Papers.BeyondCircuit08.MainResults.Zeckendorf

/-- The Zeckendorf equivalence supplies a finite enumeration of the allowed strings. -/
instance (n : ℕ) : Fintype (PStrings n) :=
  Fintype.ofEquiv (Fin (Nat.fib (n + 2))) (zEquiv n).symm

/-- The set of values attained by the Zeckendorf encoding `zMap` on
allowed strings of length `n` is exactly `Set.Iio (Nat.fib (n + 2))`,
i.e. `{0, …, f_{n+2} - 1}`: every value is strictly below `f_{n+2}` by
definition of `Fin`, and every smaller value is attained by
`zMap_surjective`. -/
theorem proposition4_value_range (n : ℕ) :
    Set.range (fun s : PStrings n => (zMap s).val) =
      Set.Iio (Nat.fib (n + 2)) := by
  ext v
  constructor
  · rintro ⟨s, rfl⟩
    exact (zMap s).isLt
  · intro hv
    have hv' : v < Nat.fib (n + 2) := hv
    obtain ⟨s, hs⟩ := zMap_surjective (n := n) ⟨v, hv'⟩
    exact ⟨s, congrArg Fin.val hs⟩

/-- The printed top endpoint of Proposition 4 is never attained: no
allowed Boolean list of length `n` has Fibonacci weight `Nat.fib (n + 2)`.
Together with `proposition4_value_range` this shows the codomain printed
in [Jordan2008] as `{0, …, f_{n+2}}` must be read as `{0, …, f_{n+2} - 1}`. -/
theorem proposition4_top_not_attained (n : ℕ) (l : List Bool)
    (hl : l.length = n) (hA : Allowed l) :
    starWeight l ≠ Nat.fib (n + 2) :=
  ne_of_lt (starWeight_lt_fib n l hl hA)

/-- The number of allowed strings of length `n` is `Nat.fib (n + 2)`,
counted through the bijection `zEquiv` of Proposition 4. -/
theorem proposition4_card (n : ℕ) :
    Fintype.card (PStrings n) = Nat.fib (n + 2) := by
  rw [Fintype.card_congr (zEquiv n), Fintype.card_fin]

/-- The value `0` is attained by the Zeckendorf encoding in every length:
the range characterised by `proposition4_value_range` is nonempty, since
`0 < Nat.fib (n + 2)`. -/
theorem proposition4_value_zero_mem (n : ℕ) :
    (0 : ℕ) ∈ Set.range (fun s : PStrings n => (zMap s).val) := by
  rw [proposition4_value_range]
  exact Set.mem_Iio.mpr (Nat.fib_pos.mpr (by omega))

end Qatlib.Papers.BeyondCircuit08.MainResults.Zeckendorf
