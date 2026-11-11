/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanQuotientRecovery
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness

/-!
# Rank bounds for Boolean subgroup recovery

`booleanOrthogonalSubmodule` views the Boolean orthogonal complement as a vector space over
`ZMod 2`, and `booleanOrthogonalRank` records its dimension. The orthogonal complement,
character annihilator, and quotient all have cardinality two to this rank.

Substituting these identities into the quotient recovery bounds expresses fresh-sample success
and failure estimates in terms of the orthogonal rank. See [Simon1997] for the mathematical
background.

## Main statements

* `card_booleanQuotient_eq_two_pow_booleanOrthogonalRank`: the quotient cardinality equals two
  to the orthogonal rank.
* `hiddenSubgroupFreshSamples_boolean_failure_le_rank`: the rank-based failure bound.
* `hiddenSubgroupFreshSamples_boolean_success_ge_rank`: the rank-based success bound.

## References

* [Simon, 1997][Simon1997]
-/

set_option warningAsError false

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open scoped Classical

variable {n : ℕ}

/-- The Boolean orthogonal complement of `H`, viewed as a submodule over `ZMod 2`. -/
def booleanOrthogonalSubmodule (H : AddSubgroup (BooleanVec n)) :
    Submodule (ZMod 2) (BooleanVec n) :=
  AddSubgroup.toZModSubmodule 2 (booleanOrthogonal H)

/-- Membership in the orthogonal submodule agrees with membership in `booleanOrthogonal H`. -/
@[simp] theorem mem_booleanOrthogonalSubmodule (H : AddSubgroup (BooleanVec n))
    (a : BooleanVec n) :
    a ∈ booleanOrthogonalSubmodule H ↔ a ∈ booleanOrthogonal H :=
  Iff.rfl

/-- The dimension over `ZMod 2` of the Boolean orthogonal complement of `H`. -/
noncomputable def booleanOrthogonalRank (H : AddSubgroup (BooleanVec n)) : ℕ :=
  Module.finrank (ZMod 2) (booleanOrthogonalSubmodule H)

/-- The Boolean orthogonal complement has cardinality `2 ^ booleanOrthogonalRank H`. -/
theorem card_booleanOrthogonal_eq_two_pow_rank (H : AddSubgroup (BooleanVec n)) :
    Fintype.card (booleanOrthogonal H) = 2 ^ booleanOrthogonalRank H := by
  change Fintype.card (booleanOrthogonalSubmodule H) = 2 ^ booleanOrthogonalRank H
  simpa [booleanOrthogonalRank, ZMod.card] using
    (Module.card_eq_pow_finrank
      (K := ZMod 2) (V := booleanOrthogonalSubmodule H))

/-- The character annihilator has cardinality `2 ^ booleanOrthogonalRank H`. -/
theorem card_characterAnnihilator_eq_two_pow_booleanOrthogonalRank
    (H : AddSubgroup (BooleanVec n)) :
    Fintype.card (characterAnnihilator H) = 2 ^ booleanOrthogonalRank H := by
  calc
    Fintype.card (characterAnnihilator H) = Fintype.card (booleanOrthogonal H) :=
      (Fintype.card_congr (booleanOrthogonalCharacterEquiv H).toEquiv).symm
    _ = 2 ^ booleanOrthogonalRank H := card_booleanOrthogonal_eq_two_pow_rank H

/-- The quotient by `H` has cardinality `2 ^ booleanOrthogonalRank H`. -/
theorem card_booleanQuotient_eq_two_pow_booleanOrthogonalRank
    (H : AddSubgroup (BooleanVec n)) :
    Fintype.card (BooleanVec n ⧸ H) = 2 ^ booleanOrthogonalRank H := by
  rw [card_booleanQuotient_eq_annihilator]
  exact card_characterAnnihilator_eq_two_pow_booleanOrthogonalRank H

variable {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- For a hiding oracle and orthogonal rank `r`, the fresh-sample recovery failure mass is at
most `ENNReal.ofReal ((2 ^ r - 1) / 2 ^ m)`. -/
theorem hiddenSubgroupFreshSamples_boolean_failure_le_rank
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H),
      hiddenSubgroupFreshSamples f e m xs) ≤
      ENNReal.ofReal ((((2 : ℝ) ^ booleanOrthogonalRank H) - 1) / (2 : ℝ) ^ m) := by
  simpa [card_characterAnnihilator_eq_two_pow_booleanOrthogonalRank] using
    hiddenSubgroupFreshSamples_boolean_failure_le_annihilator f H hf e m

/-- For a hiding oracle, the fresh-sample exact recovery mass is at least one minus the
annihilator-cardinality failure estimate, mapped through `ENNReal.ofReal`. -/
theorem hiddenSubgroupFreshSamples_boolean_success_ge_annihilator
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    ENNReal.ofReal
        (1 - ((Fintype.card (characterAnnihilator H) : ℝ) - 1) / (2 : ℝ) ^ m) ≤
      ∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          booleanSampleCandidate (booleanDecodedSamples xs) = H),
        hiddenSubgroupFreshSamples f e m xs := by
  simpa only [card_booleanQuotient_eq_annihilator] using
    hiddenSubgroupFreshSamples_boolean_success_ge_quotient f H hf e m

/-- For a hiding oracle and orthogonal rank `r`, the fresh-sample exact recovery mass is at
least `ENNReal.ofReal (1 - (2 ^ r - 1) / 2 ^ m)`. -/
theorem hiddenSubgroupFreshSamples_boolean_success_ge_rank
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    ENNReal.ofReal
        (1 - ((((2 : ℝ) ^ booleanOrthogonalRank H) - 1) / (2 : ℝ) ^ m)) ≤
      ∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          booleanSampleCandidate (booleanDecodedSamples xs) = H),
        hiddenSubgroupFreshSamples f e m xs := by
  simpa [card_characterAnnihilator_eq_two_pow_booleanOrthogonalRank] using
    hiddenSubgroupFreshSamples_boolean_success_ge_annihilator f H hf e m

end Qatlib.Concepts.HspRecovery.ReductionCore
