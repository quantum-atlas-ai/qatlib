/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.OpenSieve.RepresentationSieveContinuation
import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianIrrep

/-!
# Representation label masses for dihedral records

This module gives the dihedral representation-label mass identities associated with Proposition
8.1 of [Kuperberg2005]. Given a representation transport witness, `prop81_label_mass` identifies
the mass of actual records at a label with the representation dimension times the dimension of
its reflection-fixed subspace, divided by `N`.

`prop81_paper_shape` expresses the same mass using the dihedral group order `2 * N` and
reflection subgroup order two. `prop81_total_mass` proves the corresponding dimension-count
identity for an irreducible representation family.

## Main statements

* `prop81_label_mass`: transported actual-record mass at each representation label.
* `prop81_paper_shape`: equivalent formulas for the representation-label mass.
* `prop81_total_mass`: the sum of dimension times fixed-space dimension equals `N`.

## References

* [Kuperberg, 2005, Proposition 8.1][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Prop81

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.OpenSieve
open scoped BigOperators

/-- Given a representation transport witness, the actual record mass assigned to an irreducible
label equals its representation-label mass, namely the representation dimension times its
fixed-space dimension divided by `N`. This is the transported label-mass formula associated
with [Kuperberg, Proposition 8.1][Kuperberg2005]. -/
theorem prop81_label_mass {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) {Label : Type}
    [Fintype Label] [DecidableEq Label] (family : IrrepFamily N Label)
    (s : ZMod N) (w : RepTransportWitness f s family) (V : Label) :
    (∑' q : ZMod N × Bool × S,
        if w.toLabel q.1 = V then ENNReal.toReal (actualRecordFiniteLaw f q) else 0)
      = repLabelMass (family.irrep V) s ∧
    repLabelMass (family.irrep V) s =
      ((family.irrep V).dim : ℝ) * dimFixed (family.irrep V) s / N :=
  clause1_label_mass_is_prop8_1 f family s w V

/-- Expresses the representation-label mass both as `V.dim * dimFixed V s * 2 / (2 * N)` and as
`V.dim * dimFixed V s / N`, corresponding to the dihedral specialization of [Kuperberg,
Proposition 8.1][Kuperberg2005]. -/
theorem prop81_paper_shape {N : ℕ} [NeZero N] (V : DihedralIrrep N) (s : ZMod N) :
    repLabelMass V s = (V.dim : ℝ) * (dimFixed V s : ℝ) * 2 / (2 * (N : ℝ)) ∧
    repLabelMass V s = (V.dim : ℝ) * (dimFixed V s : ℝ) / (N : ℝ) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  constructor
  · unfold repLabelMass
    ring
  · unfold repLabelMass
    field_simp

/-- For an irreducible representation family, the sum of representation dimension times
fixed-space dimension equals `N`. This is the dimension-count normalization identity for the
label masses associated with [Kuperberg, Proposition 8.1][Kuperberg2005]. -/
theorem prop81_total_mass (N : ℕ) [NeZero N] (Label : Type) [Fintype Label]
    [DecidableEq Label] (family : IrrepFamily N Label) (s : ZMod N) :
    ∑ l : Label, (family.irrep l).dim * dimFixed (family.irrep l) s = N :=
  dimFixedCount_identity N Label family s

end Qatlib.Concepts.HspRecovery.OpenSieve.Prop81
