/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.FourierRecovery.ModularFourier.FourierGradientDefs

@[expose] public section

/-!
# Shor-line first slice: the public QFT elementary-gate formula at n = 2

The first auditable slice of the ShorFactoring97 line: the public
QFT elementary-gate count formula `qftElementaryGates`, instantiated and evaluated
at the smallest non-trivial width n = 2. The slice fixes the bookkeeping side of
the QFT step — the formula and its value — while explicitly not claiming the
modular-exponentiation part, phase conventions, bit reversal, or any cost bound of
the full factoring pipeline.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.FourierRecovery.ModularFourier

namespace Qatlib.Papers.ShorFactoring97.QftSlice

/-- The public QFT elementary-gate formula at width two evaluates to four: two
Hadamards, one controlled phase, and one final swap's worth of budgeted gates. -/
theorem qft2Gates : qftElementaryGates 2 = 4 := by
  decide

/-- The formula is a function of the width alone, so the slice's count is the
public formula's value, not a new counting convention. -/
theorem qftGatesIsFormula (n : ℕ) : qftElementaryGates n = n + n * (n - 1) / 2 + n / 2 := rfl

end Qatlib.Papers.ShorFactoring97.QftSlice
