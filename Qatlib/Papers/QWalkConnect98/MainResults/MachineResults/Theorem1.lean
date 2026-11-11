/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.MachineResults.MachineDefs

/-!
# Reduction closure and the SL inclusion

`QRHLClosedUnderReduces` and `USTCONInQRHL` express the closure and regular-connectivity
hypotheses needed for the language inclusion. The proof of `theorem1_SL_subset_QRHL` unfolds
`InSL` and composes these hypotheses.

The inclusion is stated for the abstract language predicates and reduction relation defined in
`MachineDefs`. The formalization follows [Watrous1998].

## Main statements

* `QRHLClosedUnderReduces`: closure of `InQRHL` under the defined reductions.
* `USTCONInQRHL`: membership for decoded regular connectivity languages.
* `theorem1_SL_subset_QRHL`: the conditional inclusion of `InSL` in `InQRHL`.

## References

* [Watrous, 1998][Watrous1998]
-/

set_option warningAsError false

namespace Qatlib.Papers.QWalkConnect98.MainResults.MachineResults

set_option autoImplicit false

/-- The predicate that `InQRHL` is closed under the membership-preserving maps specified by
`Reduces`. -/
def QRHLClosedUnderReduces : Prop :=
  ∀ {A B : List Bool → Prop}, InQRHL B → Reduces A B → InQRHL A

/-- The predicate that every connectivity language decoded into fixed-degree regular graph
instances of degree at least three belongs to `InQRHL`. -/
def USTCONInQRHL : Prop :=
  ∀ (d : ℕ) (decode : List Bool → GraphInstance d), 3 ≤ d →
    InQRHL (fun x => InstanceConnected (decode x))

/-- If decoded regular connectivity belongs to `InQRHL` and `InQRHL` is closed under `Reduces`,
every language satisfying `InSL` also satisfies `InQRHL`. See [Watrous1998]. -/
theorem theorem1_SL_subset_QRHL (A : List Bool → Prop) (hSL : InSL A)
    (hUSTCON : USTCONInQRHL) (hclosed : QRHLClosedUnderReduces) : InQRHL A := by
  obtain ⟨d, decode, hd, hred⟩ := hSL
  exact hclosed (hUSTCON d decode hd) hred

end Qatlib.Papers.QWalkConnect98.MainResults.MachineResults
