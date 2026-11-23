/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.HspRecovery.RecordExtract.Algorithm2

@[expose] public section

/-!
# Concrete collision endpoint for the dihedral sieve

For every nonzero modulus, `affineSlopeOracle` hides the reflection of slope `s`.
On the concrete modulus `5`, the width-three search collides at rotation label `1`
and reflection label `3`, and that label difference is the hidden slope `2`.
The collision program then uses exactly six oracle queries, returns slope `2`
with mass one, and assigns mass zero to every other slope. The modulus stays
nontrivial and the width still covers the whole residue set.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.DihHSPSieve03.MainResults

open Qatlib.Concepts.HspRecovery.OpenSieve
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Algorithm2
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian

/-- The affine oracle used for the concrete `N = 5` hidden-reflection instance.
The two Boolean branches are the rotation and reflection cosets, with the hidden
slope subtracted on the latter branch. -/
def affineSlopeOracle (N : ℕ) (s : ZMod N) : DihedralReg N → ZMod N :=
  fun p => if p.2 then p.1 - s else p.1

/-- The affine oracle hides the reflection of slope `s` at every nonzero modulus. -/
theorem affineSlopeOracle_hides (N : ℕ) [NeZero N] (s : ZMod N) :
    DihedralReflectionHides N (affineSlopeOracle N s) s := by
  intro ⟨a, b⟩ ⟨c, d⟩
  cases b with
  | false =>
      cases d with
      | false =>
          have h : a = c ↔ c = a := eq_comm
          simpa [affineSlopeOracle, dihedralReflect] using h
      | true =>
          have h : a = c - s ↔ c = a + s := by
            constructor
            · intro he
              exact (eq_sub_iff_add_eq.mp he).symm
            · intro he
              exact eq_sub_iff_add_eq.mpr he.symm
          simpa [affineSlopeOracle, dihedralReflect] using h
  | true =>
      cases d with
      | false =>
          have h : a - s = c ↔ c = a - s := eq_comm
          simpa [affineSlopeOracle, dihedralReflect] using h
      | true =>
          have h : a - s = c - s ↔ c = a := by
            constructor
            · intro he
              have hh := congrArg (fun x : ZMod N => x + s) he
              simpa only [sub_add_cancel] using hh.symm
            · intro he
              rw [he]
          simpa [affineSlopeOracle, dihedralReflect] using h

/-- The width-three search has an explicit collision in its finite query grid.
The rotation label `1` and reflection label `3` receive the same oracle value,
and their label difference is the hidden slope `2` in `ZMod 5`. -/
theorem affineSlopeOracle_concrete_collision :
    affineSlopeOracle 5 (2 : ZMod 5) ((1 : ZMod 5), false) =
        affineSlopeOracle 5 (2 : ZMod 5) ((3 : ZMod 5), true) ∧
      (3 : ZMod 5) - 1 = (2 : ZMod 5) := by
  norm_num [affineSlopeOracle]

/-- A concrete general-modulus endpoint for Kuperberg's collision search.
For the nontrivial modulus `5`, width `3` covers the whole residue set.  The
collision program therefore uses exactly six oracle queries, returns the
hidden slope `2` with unit mass, and gives zero mass to every other slope. -/
theorem algorithm2_concrete_main :
    ShiftRecoveryEndpoint 5 1 (generalCollisionLedger 5 3) ∧
      generalCollisionQueryCount 5 3 = 6 ∧
      (∀ u : ZMod 5, u ≠ (2 : ZMod 5) →
        generalCollisionRun (affineSlopeOracle 5 (2 : ZMod 5)) 3 (some u) = 0) ∧
      generalCollisionRun (affineSlopeOracle 5 (2 : ZMod 5)) 3 (some (2 : ZMod 5)) = 1 := by
  have hhide := affineSlopeOracle_hides 5 (2 : ZMod 5)
  have hrec := clause14_collision_recovery
    (affineSlopeOracle 5 (2 : ZMod 5)) (2 : ZMod 5) hhide 3 (by norm_num) (by norm_num)
  have hupper := PMF.coe_le_one
    (generalCollisionRun (affineSlopeOracle 5 (2 : ZMod 5)) 3) (some (2 : ZMod 5))
  have hunit :
      generalCollisionRun (affineSlopeOracle 5 (2 : ZMod 5)) 3 (some (2 : ZMod 5)) = 1 := by
    apply le_antisymm
    · simpa using hupper
    · simpa only [ENNReal.ofReal_one] using hrec.2
  refine ⟨clause14_collision_endpoint 5 3 (by norm_num) (by norm_num), ?_, hrec.1, hunit⟩
  norm_num [clause14_collision_query_count]

end Qatlib.Papers.DihHSPSieve03.MainResults
