/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.DihedralHSP13.MainResults.Collimation.SourceCollimationCost
import Qatlib.Papers.DihedralHSP13.MainResults.MachineModel.SourceLinearAccessSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Kuperberg 2013, Corollary 4.3: collimation without quantum access memory

Source: Greg Kuperberg, *Another subexponential-time quantum algorithm for the dihedral
hidden subgroup problem*, arXiv:1112.3333v1 (TQC 2013), Corollary 4.3, Section 4.3, page 7
(txt line 431, PDF p. 7).

The corollary: taking the hypotheses of Proposition 4.2, if the quantum computer has *no*
quantum access memory, then Algorithm 4.1 can be executed with `r = 2` with

* `Õ(ℓmax)` quantum time (and classical time),
* `Õ(ℓmax)` classical space, and
* `O(log ℓmax)` quantum space.

The paper says the corollary "follows immediately from Proposition 4.2 and Proposition 2.2":
the only quantum-access-memory demand of Proposition 4.2 is the `ℓmax · m` bits of the
low-`m`-bit table, and Proposition 2.2 emulates each random access by a linear scan of the
`ℓmax` cells at `Õ(ℓmax)` time.

## Contents

* `Prop43Bounds`: the four bounds of the corollary.
* `algorithm41R2NoQram`: the ledger of §4.3's accounting with the quantum-access table
  replaced by a single linear scan: the classical time of Proposition 4.2's table
  construction is re-charged as *quantum* time (`cor43_quantumTime_eq_prop42_classicalTime`),
  and the QRACM demand drops to zero (`cor43_qramSpace_zero`).
* `cor43_scan_gateCount`: the linear-access scan of a table with `ℓmax` cells is exactly
  `ℓmax` gates, reusing the proved Proposition 2.2 development
  (`prop22_scan_gate_overhead` in `MachineModel.SourceLinearAccessSimulation`).
* `cor43_noQram_quantumTime_eq_scan`: the corollary's quantum time *is* the scan cost times
  the per-entry width, i.e. the explicit Proposition 2.2 emulation ledger.
* `cor43_bounds`: the four bounds hold with constant `1`.

The modelling boundary is the same as for Proposition 4.2: the ledger is the paper's
step-by-step accounting, not a count extracted from a Lean implementation of Algorithm 4.1.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.DihedralHSP13.MainResults.Collimation

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.DihedralHSP13.MainResults.MachineModel

/-- **The four bounds of Corollary 4.3**: `Õ(ℓmax)` quantum time and classical time,
`Õ(ℓmax)` classical space, `O(log ℓmax)` quantum space. -/
def Prop43Bounds (D : CollimationData) (L : Ledger) (K : ℕ) : Prop :=
  L.quantumTime ≤ K * D.lenMax * (Nat.log 2 D.lenMax + 1) * (D.height + 1) ∧
    L.classicalTime ≤ K * D.lenMax * (Nat.log 2 D.lenMax + 1) * (D.height + 1) ∧
      L.classicalSpace ≤ K * D.lenMax * (Nat.log 2 D.lenMax + 1) * (D.height + 1) ∧
        L.quantumSpace ≤ K * (Nat.log 2 D.lenMax + 1)

/-- The ledger of Algorithm 4.1 with `r = 2` and *no* quantum access memory: the table
construction and renumbering that Proposition 4.2 performs in classical time with QRACM is
performed quantumly by one linear scan of the `ℓmax`-cell table (Proposition 2.2), so the
classical time of `algorithm41R2` is re-charged as quantum time, classical space is the
`Õ(ℓmax)` scan workspace, the quantum-access table disappears, and the quantum space is
still only the `⌈log₂ ℓmax⌉`-qubit length register. -/
def algorithm41R2NoQram (D : CollimationData) : Ledger where
  classicalTime := D.lenMax * (Nat.log 2 D.lenMax + 1) * (D.height + 1)
  classicalSpace := D.lenMax * (Nat.log 2 D.lenMax + 1) * (D.height + 1)
  qramClassicalSpace := 0
  quantumTime := D.lenMax * (Nat.log 2 D.lenMax + 1) * (D.height + 1)
  quantumSpace := Nat.log 2 D.lenMax + 1

/-- **Corollary 4.3** (Kuperberg 2013, §4.3, p. 7, txt line 431): without quantum access
memory, Algorithm 4.1 with `r = 2` runs within `Õ(ℓmax)` quantum and classical time,
`Õ(ℓmax)` classical space, and `O(log ℓmax)` quantum space. -/
theorem cor43_bounds (D : CollimationData) :
    Prop43Bounds D (algorithm41R2NoQram D) 1 := by
  simp only [Prop43Bounds, algorithm41R2NoQram, one_mul]
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- The corollary uses no quantum access memory at all. -/
theorem cor43_qramSpace_zero (D : CollimationData) :
    (algorithm41R2NoQram D).qramClassicalSpace = 0 :=
  rfl

/-- **The corollary's derivation from Proposition 4.2.**  The quantum time of the no-QRACM
ledger is exactly the *classical* time of Proposition 4.2's ledger: the table construction
that Proposition 4.2 charges to classical computation is what Corollary 4.3 charges to the
quantum linear scan. -/
theorem cor43_quantumTime_eq_prop42_classicalTime (D : CollimationData) :
    (algorithm41R2NoQram D).quantumTime = (algorithm41R2 D).classicalTime :=
  rfl

/-! ## §2. The Proposition 2.2 linear-access scan ledger -/

/-- **Proposition 2.2 applied to the collimation table.**  Simulating the quantum access
memory of `ℓmax` cells by a classical linear access memory takes exactly one gate per cell,
i.e. `ℓmax` gates (the proved `prop22_scan_gate_overhead`, instantiated at `Fin ℓmax`). -/
theorem cor43_scan_gateCount (D : CollimationData) :
    GateCount (scanCircuit (fun _ : Fin D.lenMax => (0 : ZMod 2))) = D.lenMax := by
  have h := prop22_scan_gate_overhead (I := Fin D.lenMax) (fun _ => (0 : ZMod 2))
  rw [h.1]
  simp

/-- **The corollary's quantum time is the Proposition 2.2 scan ledger.**  `Õ(ℓmax)` quantum
time factorizes as the scan gate count `ℓmax` (one gate per cell) times the
`log ℓmax + 1` address-decoding factor and the `h + 1` phase-width factor. -/
theorem cor43_noQram_quantumTime_eq_scan (D : CollimationData) :
    (algorithm41R2NoQram D).quantumTime =
      GateCount (scanCircuit (fun _ : Fin D.lenMax => (0 : ZMod 2))) *
        (Nat.log 2 D.lenMax + 1) * (D.height + 1) := by
  show D.lenMax * (Nat.log 2 D.lenMax + 1) * (D.height + 1) = _
  rw [cor43_scan_gateCount]

/-- The scan is unitary, so the emulation is a legitimate quantum circuit (reusing
`isUnitaryCircuit_scanCircuit`). -/
theorem cor43_scan_unitary (D : CollimationData) :
    IsUnitaryCircuit (scanCircuit (fun _ : Fin D.lenMax => (0 : ZMod 2))) :=
  isUnitaryCircuit_scanCircuit _

/-- Combined form: the four bounds, no quantum access memory, and the quantum time is exactly
the Proposition 2.2 scan ledger. -/
theorem cor43_all (D : CollimationData) :
    Prop43Bounds D (algorithm41R2NoQram D) 1 ∧
      (algorithm41R2NoQram D).qramClassicalSpace = 0 ∧
        (algorithm41R2NoQram D).quantumTime =
          GateCount (scanCircuit (fun _ : Fin D.lenMax => (0 : ZMod 2))) *
            (Nat.log 2 D.lenMax + 1) * (D.height + 1) :=
  ⟨cor43_bounds D, cor43_qramSpace_zero D, cor43_noQram_quantumTime_eq_scan D⟩

end Qatlib.Papers.DihedralHSP13.MainResults.Collimation
