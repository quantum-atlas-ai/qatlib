/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecodingCoreDefs

@[expose] public section

/-!
# Reusable CSS distance interfaces

All statements use the public CSS and Pauli types. Distance is characterized
modulo stabilizers, including degenerate codes and infinite extended distance.
The interfaces separate a logical upper witness from a lower-bound argument.
-/

namespace Qatlib.Concepts.ErrorCorrection.LogicalOps

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

variable {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ]

/-- A nontrivial undetectable Pauli label bounds the distance from above. -/
theorem distance_le (c : CssData ι κX κZ) (e : PauliLabel ι)
    (hs : pauliSyndrome c e = (0, 0)) (hn : ¬ IsStabilizerLabel c e) :
    cssDistance c ≤ (pauliWeight e.1 e.2 : ℕ∞) := by
  rw [cssDistance_eq_logical]
  exact sInf_le ⟨e.1, e.2, congrArg Prod.fst hs, congrArg Prod.snd hs, hn, rfl⟩

/-- A distance lower bound means that every smaller undetectable label is a stabilizer. -/
theorem distance_ge_iff (c : CssData ι κX κZ) (d : ℕ∞) :
    d ≤ cssDistance c ↔
      ∀ e : PauliLabel ι, pauliSyndrome c e = (0, 0) →
        (pauliWeight e.1 e.2 : ℕ∞) < d → IsStabilizerLabel c e := by
  constructor
  · intro hd e hs hw
    by_contra hn
    exact (not_lt_of_ge (hd.trans (distance_le c e hs hn))) hw
  · intro hall
    rw [cssDistance_eq_logical]
    apply le_sInf
    rintro w ⟨x, z, hz, hx, hn, rfl⟩
    by_contra hnot
    exact hn (hall (x, z) (Prod.ext hz hx) (lt_of_not_ge hnot))

/-- Matching a lower certificate with a logical upper witness proves exact distance. -/
theorem distance_eq (c : CssData ι κX κZ) (d : ℕ) (e : PauliLabel ι)
    (lower : ∀ f : PauliLabel ι, pauliSyndrome c f = (0, 0) →
      (pauliWeight f.1 f.2 : ℕ∞) < d → IsStabilizerLabel c f)
    (hs : pauliSyndrome c e = (0, 0)) (hn : ¬ IsStabilizerLabel c e)
    (hw : pauliWeight e.1 e.2 = d) : cssDistance c = d := by
  apply le_antisymm
  · simpa only [hw] using distance_le c e hs hn
  · exact (distance_ge_iff c d).mpr lower

end Qatlib.Concepts.ErrorCorrection.LogicalOps
