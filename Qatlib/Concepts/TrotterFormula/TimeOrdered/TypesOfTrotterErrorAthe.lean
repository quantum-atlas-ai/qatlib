/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.TimeOrdered.TypesOfTrotterErrorStat

/-!
# Product-formula error representation theorem

The theorem `typesOfTrotterError` proves the proposition `TypesOfTrotterError` by assembling the
additive integral identity, the two defect conjugation sums, and the exponentiated and
multiplicative representations of a matrix exponential word. This is the finite-matrix error
representation package associated with [ChildsEtAl2021Trotter].

## Main statements

* `typesOfTrotterError`: all five identities hold for every finite matrix exponential word,
  target generator, and real time.

## References

* [Childs et al., 2021, Theorem 8][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.TrotterFormula.TimeOrdered

/-- Every finite matrix exponential word satisfies the five identities packaged in
`TypesOfTrotterError`: the additive, right-defect, exponentiated, left-defect, and
multiplicative representations. See [Childs et al., Theorem 8][ChildsEtAl2021Trotter]. -/
theorem typesOfTrotterError : TypesOfTrotterError := by
  intro I _ _ xs H t
  exact ⟨pf_word_additive_representation xs H t,
    pfWordDefectRight_suffix_sum xs H,
    pf_word_exponentiated_representation xs H t,
    pfWordDefectLeft_prefix_sum xs H,
    pf_word_multiplicative_representation xs H t⟩

end Qatlib.Concepts.TrotterFormula.TimeOrdered
