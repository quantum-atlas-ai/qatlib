/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversary

set_option backward.isDefEq.respectTransparency false

/-!
# NegWeights06, Theorem 21 — the six-bit weight-three partial function

Source: Høyer–Lee–Špalek, "Negative weights make adversaries stronger",
arXiv:quant-ph/0611054v2 (fixed PDF, SHA256
`8c705081dc3243baa1c83a64ed92870c7cd42fa91dd872c469621158af2c37bb`),
Theorem 21 and its proof, §7.2, printed pages 25–26:

`ADV±(f) ≥ 2 + 3√5/5` for the six-bit partial Boolean function of Hamming
weight three (ten zero inputs and ten one inputs), with the explicit
twenty-by-twenty negative-weight adversary matrix of weights
`a = (1+√5)/5`, `b = (1-√5)/5`, `c = 1/5`.

The paper-layer theorem is a reference/bridge to the frozen realized witness
(Theorem21RealizedWitnessNega) and its source-value consumer
`QuantumAlgorithm.Concepts.AdversaryBounds.AdvDuality.advPmValue_kushilevitz_ge`,
which proves `ENNReal.ofReal (2 + 3√5/5) ≤ advPmValue kushilevitzInputW
kushilevitzFunW`.  Every entry of the witness is exact algebraic data; no
floating point or certificate hypothesis is used.
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.NegWeights06.MainResults.Examples

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

/-- **Theorem 21 (six-bit weight-three partial function).**
`ADV±(f) ≥ 2 + 3√5/5` for the printed Section 7.2 partial function `f`, whose
domain is the twenty six-bit words of Hamming weight three split into ten zero
and ten one inputs.

The witness is the printed complex Hermitian matrix
`kushilevitzGammaW`; the frozen theorem
`advPmValue_kushilevitz_ge` already turns its spectral norm lower bound and
unit filter bound into the `advPmValue` lower bound. -/
theorem theorem21_kushilevitz_bound :
    ENNReal.ofReal (2 + 3 * Real.sqrt 5 / 5) ≤
      advPmValue kushilevitzInputW kushilevitzFunW :=
  advPmValue_kushilevitz_ge

end

end Qatlib.Papers.NegWeights06.MainResults.Examples
