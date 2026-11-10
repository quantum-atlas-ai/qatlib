/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.OpenSieve.RepresentationSieveContinuation
import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianIrrep
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Prop81

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.OpenSieve
open scoped BigOperators

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

theorem prop81_paper_shape {N : ℕ} [NeZero N] (V : DihedralIrrep N) (s : ZMod N) :
    repLabelMass V s = (V.dim : ℝ) * (dimFixed V s : ℝ) * 2 / (2 * (N : ℝ)) ∧
    repLabelMass V s = (V.dim : ℝ) * (dimFixed V s : ℝ) / (N : ℝ) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  constructor
  · unfold repLabelMass
    ring
  · unfold repLabelMass
    field_simp

theorem prop81_total_mass (N : ℕ) [NeZero N] (Label : Type) [Fintype Label]
    [DecidableEq Label] (family : IrrepFamily N Label) (s : ZMod N) :
    ∑ l : Label, (family.irrep l).dim * dimFixed (family.irrep l) s = N :=
  dimFixedCount_identity N Label family s

end Qatlib.Concepts.HspRecovery.OpenSieve.Prop81
